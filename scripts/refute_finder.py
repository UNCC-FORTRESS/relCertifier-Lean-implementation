#!/usr/bin/env python3
"""Refutation witness finder (UNTRUSTED; branch `refutation`).

For every Black-Okun-Yesha mutant of the suite (the operators and the enumeration of
`scripts/black_mutation.py` on branch `mutation`, copied here), search a rational witness that
Theorem 3's claim of the mutated invariant is false, in the exact form the kernel refutations
read (`Proofs/Encoding/Emitted/Refute.lean`):

* the antecedent at the witness: the stored left mode u's row, the left envelope (left mode 0's
  evolve), the right envelope (right mode 0's evolve), the stored right mode q0's guard and its
  KEPT CUT ATOMS (the model's cut certificate `cutV2`), and the entered mode m's guard,
  m in next(u);
* kind C: no right state satisfies, at the witness's left values, the entered row m with the
  right envelope, some right mode's guard and its kept atoms (one closed query per right mode);
* kind A: some component k of row m is > 0 at the witness, and it is rigid (no right field
  decreases it inside the right envelope; one query per right mode).

Every formula comes from `scripts/refute_dump.lean`, which prints the tool's own parse and
lowering (`Emitted.Data`), so the search is over exactly what the kernel checks; the kernel
re-checks every witness anyway, so nothing here is trusted. Witness values are exact rationals.

Every record carries the SHA-256 of the mutant text searched (`sha256`) and its file under a
per-run scratch folder (`$REFUTE_SCRATCH/<run>/<bench>/`), so `gen_refute.py` uses a mutant text
only from the run that found its witness. With `--only`, the records of the other benchmarks
already in `--out` are kept (a benchmark's block replaced in place, a new benchmark appended).

Usage: scripts/refute_finder.py [--only a,b] [--jobs 8] [--out docs/refute/witnesses.jsonl]
"""
import argparse, glob, hashlib, json, os, re, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import inv_smt as I

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
Z3 = os.environ.get("Z3", "/opt/homebrew/bin/z3")
SCRATCH = os.environ.get("REFUTE_SCRATCH", "/tmp/relcert-refute")
RUN = time.strftime("run-%Y%m%d-%H%M%S") + f"-{os.getpid()}"

# ---------------------------------------------------------------- mutants (black_mutation.py)

def vars_in(e, acc):
    if isinstance(e, list):
        for x in e[1:]:
            vars_in(x, acc)
    elif re.match(r"^[LR]_", e):
        acc.add(e)
    return acc


def norm_op(op):
    return {"==": "=", "=": "="}.get(op, op)


def fix_eq(e):
    if isinstance(e, list):
        return ["=" if e[0] == "==" else e[0]] + [fix_eq(x) for x in e[1:]]
    return e


def load_rows(text):
    b = I.parse_bench(text)
    rows = [(ln, k, [fix_eq(a) for a in I.atoms_of(v, "", [])]) for ln, k, v in b["rows"]]
    return b, rows


def twin_swaps(atom, Lv, Rv):
    vs = sorted(vars_in(atom, set()))
    out = []
    def sub(e, a, b):
        if isinstance(e, list):
            return [e[0]] + [sub(x, a, b) for x in e[1:]]
        return b if e == a else e
    for v in vs:
        side, name = v[0], v[2:]
        other = "R" if side == "L" else "L"
        if name in (Rv if other == "R" else Lv):
            out.append((f"{v}->{other}_{name}", sub(atom, v, f"{other}_{name}")))
    return out


def mutants(rows, Lv, Rv):
    distinct = {}
    for _, _, atoms in rows:
        for a in atoms:
            distinct.setdefault(I.show(a), a)
    out = []
    for key, a in distinct.items():
        op = norm_op(a[0])
        if op in ("<=", ">="):
            o = {"<=": ">=", ">=": "<="}[op]
            out.append(("RRO/SNO", f"{key} [{op}->{o}]", key, [o] + a[1:]))
        if any(len(at) >= 2 and key in map(I.show, at) for _, _, at in rows):
            out.append(("MCO", f"{key} [del]", key, None))
        for tag, b in twin_swaps(a, Lv, Rv):
            out.append(("ORO", f"{key} [{tag}]", key, b))
    return out


def apply(rows, key, new):
    res = []
    for ln, name, atoms in rows:
        if new is None:
            kept = [a for a in atoms if I.show(a) != key]
            atoms = kept if kept else atoms
        else:
            atoms = [new if I.show(a) == key else a for a in atoms]
        res.append((ln, name, atoms))
    return res


def write(text, rows):
    lines = text.split("\n")
    for ln, name, atoms in rows:
        body = atoms[0] if len(atoms) == 1 else ["and"] + atoms
        lines[ln] = f"{name} = smt2:{I.show(body)}"
    return "\n".join(lines)

# ---------------------------------------------------------------- exact evaluation

def evq(e, env):
    """Exact value of an SMT-LIB term/formula (as printed by `IForm.toSmt`)."""
    if not isinstance(e, list):
        if e == "true":
            return True
        if e == "false":
            return False
        if re.match(r"^[LRQ]_", e):
            return env[e]
        return Fraction(e)
    op, args = e[0], e[1:]
    if op == "and":
        return all(evq(a, env) for a in args)
    if op == "or":
        return any(evq(a, env) for a in args)
    if op == "not":
        return not evq(args[0], env)
    v = [evq(a, env) for a in args]
    if op == "+":
        return sum(v, Fraction(0))
    if op == "-":
        return -v[0] if len(v) == 1 else v[0] - sum(v[1:], Fraction(0))
    if op == "*":
        r = Fraction(1)
        for x in v:
            r *= x
        return r
    if op == "/":
        return v[0] / v[1]
    if op == "=":
        return v[0] == v[1]
    if op == "<=":
        return v[0] <= v[1]
    if op == ">=":
        return v[0] >= v[1]
    if op == "<":
        return v[0] < v[1]
    if op == ">":
        return v[0] > v[1]
    raise ValueError(op)


def holds(s, env):
    return s is None or bool(evq(I.parse_sexpr(s), env))

# ---------------------------------------------------------------- z3

def z3(decls, asserts, timeout=30, model=False):
    q = "(set-option :pp.decimal false)\n" + "".join(f"(declare-const {v} Real)\n" for v in decls)
    q += "".join(f"(assert {a})\n" for a in asserts) + "(check-sat)\n"
    if model:
        q += "(get-model)\n"
    try:
        r = subprocess.run([Z3, "-in", f"-T:{timeout}"], input=q, capture_output=True, text=True,
                           timeout=timeout + 15)
    except subprocess.TimeoutExpired:
        return "timeout", None
    lines = r.stdout.strip().splitlines() or ["error"]
    st = lines[0].strip()
    if st != "sat" or not model:
        return (st if st in ("sat", "unsat") else "unknown"), None
    body = "\n".join(lines[1:])
    vals = {}
    for m in re.finditer(r"\(define-fun (\S+) \(\) Real", body):
        start = m.end()
        depth, i = 0, start
        while i < len(body):
            ch = body[i]
            if ch == "(":
                depth += 1
            elif ch == ")":
                if depth == 0:
                    break
                depth -= 1
            i += 1
        txt = body[start:i].strip()
        try:
            vals[m.group(1)] = evq(I.parse_sexpr(txt), {})
        except Exception:
            vals[m.group(1)] = None   # an algebraic number
    return "sat", vals


GRIDS = (1000, 10, 100, 8, 64, 1024, 12, 360)


def z3_grid(decls, asserts, timeout, den):
    """A model on the grid `Z / den` (rational by construction; quadratic equalities often have
    only algebraic solutions off a grid)."""
    grid = [f"(= (* {den} {v}) (to_real N_{v}))" for v in decls]
    q = "(set-option :pp.decimal false)\n" + "".join(
        f"(declare-const {v} Real)\n(declare-const N_{v} Int)\n" for v in decls)
    q += "".join(f"(assert {a})\n" for a in asserts + grid) + "(check-sat)\n(get-model)\n"
    try:
        r = subprocess.run([Z3, "-in", f"-T:{timeout}"], input=q, capture_output=True, text=True,
                           timeout=timeout + 15)
    except subprocess.TimeoutExpired:
        return None
    lines = r.stdout.strip().splitlines() or ["error"]
    if lines[0].strip() != "sat":
        return None
    body = "\n".join(lines[1:])
    vals = {}
    for m in re.finditer(r"\(define-fun (N_\S+) \(\) Int\s+([^()]+|\(- \d+\))\)", body):
        v = evq(I.parse_sexpr(m.group(2).strip()), {})
        vals[m.group(1)[2:]] = Fraction(v) / den
    return {v: vals.get(v, Fraction(0)) for v in decls}


def approx_model(decls, asserts, timeout):
    """Decimal approximations of a model (algebraic values included)."""
    q = "(set-option :pp.decimal true)\n(set-option :pp.decimal_precision 15)\n"
    q += "".join(f"(declare-const {v} Real)\n" for v in decls)
    q += "".join(f"(assert {a})\n" for a in asserts) + "(check-sat)\n(get-model)\n"
    try:
        r = subprocess.run([Z3, "-in", f"-T:{timeout}"], input=q, capture_output=True, text=True,
                           timeout=timeout + 15)
    except subprocess.TimeoutExpired:
        return None
    out = {}
    for m in re.finditer(r"\(define-fun (\S+) \(\) Real\s+(\(- [0-9.?]+\)|[0-9.?]+)\)", r.stdout):
        t = m.group(2).replace("?", "")
        neg = t.startswith("(-")
        t = t.strip("()- ")
        x = Fraction(t)
        out[m.group(1)] = -x if neg else x
    return {v: out.get(v, Fraction(0)) for v in decls}


def isqrt_frac(x):
    if x < 0:
        return None
    import math
    a, b = x.numerator, x.denominator
    ra, rb = math.isqrt(a), math.isqrt(b)
    return Fraction(ra, rb) if ra * ra == a and rb * rb == b else None


def quad_repair(approx, g, decls, check):
    """Points on the quadric `g = 0` near an approximate model: round every coordinate, then solve
    `g = 0` exactly for one coordinate (rational root when the discriminant is a square), varying
    a second coordinate over nearby rationals."""
    ge = I.parse_sexpr(g)
    vs = sorted(v for v in vars_in(ge, set()) if v in approx)
    base = {v: Fraction(approx[v]).limit_denominator(1000) for v in decls}
    def roots(env, v):
        f = lambda x: evq(ge, {**env, v: Fraction(x)})
        c, p1, m1, p2 = f(0), f(1), f(-1), f(2)
        a = (p1 + m1) / 2 - c
        b = (p1 - m1) / 2
        if a * 4 + b * 2 + c != p2:   # not quadratic in v
            return []
        if a == 0:
            return [-c / b] if b != 0 else []
        d = isqrt_frac(b * b - 4 * a * c)
        return [] if d is None else [(-b + d) / (2 * a), (-b - d) / (2 * a)]
    for v in vs:
        for w in [None] + [x for x in vs if x != v]:
            cands = [None] if w is None else sorted(
                {Fraction(round(approx[w] * den + j), den) for den in (10, 100, 1000, 12, 8)
                 for j in range(-20, 21)}, key=lambda x: abs(x - approx[w]))[:400]
            for cw in cands:
                env = dict(base)
                if w is not None:
                    env[w] = cw
                for r in roots(env, v):
                    env2 = {**env, v: r}
                    if check(env2):
                        return env2
    return None


def models(decls, asserts, timeout, eq=None, check=None):
    """Candidate exact models: Z3's own, then grid models, then (for a quadric boundary `eq`)
    repaired points."""
    st, vals = z3(decls, asserts, timeout, model=True)
    if st != "sat":
        return
    env = rationalize(vals, decls, None)
    if env is not None:
        yield env
    for den in GRIDS[:3]:
        env = z3_grid(decls, asserts, min(timeout, 20), den)
        if env is not None:
            yield env
    if eq is not None and check is not None:
        approx = approx_model(decls, asserts, timeout)
        if approx is not None:
            env = quad_repair(approx, eq, decls, check)
            if env is not None:
                yield env
    for den in GRIDS[3:]:
        env = z3_grid(decls, asserts, min(timeout, 20), den)
        if env is not None:
            yield env


def rationalize(vals, decls, decls_env):
    """Exact values; irrational ones approximated (the exact checks decide)."""
    out = {}
    for v in decls:
        x = vals.get(v, Fraction(0)) if vals else Fraction(0)
        if x is None:
            return None
        out[v] = Fraction(x)
    return out

# ---------------------------------------------------------------- dump

def dump(bench, n, paths):
    r = subprocess.run(["lake", "env", "lean", "--run", "scripts/refute_dump.lean", bench, str(n)] + paths,
                       capture_output=True, text=True, cwd=ROOT)
    out, cur = {}, None
    for line in r.stdout.splitlines():
        d = json.loads(line)
        if d["kind"] == "file":
            cur = {"L": [], "R": []}
            out[d["path"]] = cur
        elif d["kind"] == "head":
            cur["head"] = d
        elif d["kind"] == "error":
            cur["error"] = d["msg"]
        else:
            cur[d["kind"]].append(d)
    return out


def bench_dims():
    """The Assumption 1 lemma's dimension of each benchmark: its bridge instance's dimension
    (`structOK IR n`, the clocked `bridgeDimV2`) minus the right clock. `gen_refute.py` writes
    `dim + 1`, so each refutation is stated at the bridge dimension. (Until 2026-10-27 this
    returned the bridge dimension itself, so the refutations found after the clocked change of
    2026-10-21 were stated one dimension above their bridge claims.)"""
    d = {}
    for f in glob.glob(os.path.join(ROOT, "RelCertifier/InstancesV2/Bridge/*.lean")):
        src = open(f).read()
        m = re.search(r"abbrev IR := Parse\.(\w+)_IRv2", src)
        k = re.search(r"structOK IR (\d+)", src)
        if m and k:
            d[m.group(1)] = int(k.group(1)) - 1
    return d

# ---------------------------------------------------------------- search

def conj(xs):
    xs = [x for x in xs if x is not None]
    return "true" if not xs else (xs[0] if len(xs) == 1 else "(and " + " ".join(xs) + ")")


def to_q(s):
    return re.sub(r"\bR_", "Q_", s)


def strictify(e):
    """The strict interior of a lowered formula (`IForm.strictQ`): every atom strict."""
    if not isinstance(e, list):
        return "true" if e == "true" else "false"
    op = e[0]
    if op == "and":
        return ["and"] + [strictify(x) for x in e[1:]]
    if op in ("<=", "<"):
        return ["<"] + e[1:]
    if op in (">=", ">"):
        return [">"] + e[1:]
    if op == "not" and isinstance(e[1], list) and e[1][0] == "=":
        return e
    return "false"


def strict_s(s):
    return "true" if s is None else I.show(strictify(I.parse_sexpr(s)))


def search(D, timeout, kinds="CAB"):
    """First witness (kind C, else A, else B) of a dumped mutant, or None."""
    h = D["head"]
    coords = h["coords"]
    decls = [f"L_{c}" for c in coords] + [f"R_{c}" for c in coords]
    Ls, Rs = D["L"], D["R"]
    nR = h["nR"]
    if any(not l["compsOK"] for l in Ls):
        return None, "lowering"
    rig_cache = {}
    def rigid(m, k):
        if (m, k) not in rig_cache:
            ok = True
            for q in range(nR):
                s = Rs[q]["rigid"][m][k]
                if s is None or z3(decls, [s], timeout)[0] != "unsat":
                    ok = False
                    break
            rig_cache[(m, k)] = ok
        return rig_cache[(m, k)]
    def comps_le(l):
        return [f"(<= {g} 0)" for g in Ls[l]["comps"]]
    def pre(u, m, q0):
        return conj(comps_le(u) + [h["domL"], h["domR"], Rs[q0]["guard"], Rs[q0]["cuts"],
                                    Ls[m]["guard"]])
    def exact_pre(env, u, m, q0):
        return all(holds(s, env) for s in comps_le(u) + [h["domL"], h["domR"], Rs[q0]["guard"],
                                                       Rs[q0]["cuts"], Ls[m]["guard"]])
    def partner(m, q):
        return conj(comps_le(m) + [h["domR"], Rs[q]["guard"], Rs[q]["cuts"]])
    sdomL = strict_s(h["domL"])
    def exit_ok(env, m, k):
        return (holds(sdomL, env) and evq(I.parse_sexpr(Ls[m]["comps"][k]), env) >= 0
                and Ls[m]["leftLie"][k] is not None
                and evq(I.parse_sexpr(Ls[m]["leftLie"][k]), env) > 0)
    def try_b(P, m, exact):
        for k, g in enumerate(Ls[m]["comps"]):
            if Ls[m]["leftLie"][k] is None or not rigid(m, k):
                continue
            for env in models(decls, [P, sdomL, f"(>= {g} 0)", f"(> {Ls[m]['leftLie'][k]} 0)"],
                              timeout, eq=g, check=lambda e: exact(e) and exit_ok(e, m, k)):
                if exact(env) and exit_ok(env, m, k):
                    return k, env
        return None
    if h["rowsSame"]:
        # the window form: kind B only, the left picks a window whose guard holds
        if "B" not in kinds:
            return None, "window"
        for m in range(len(Ls)):
            for q0 in range(nR):
                parts = comps_le(0) + [h["domL"], h["domR"], Rs[q0]["guard"], Rs[q0]["cuts"],
                                       Ls[m]["guard"]]
                r = try_b(conj(parts), m, lambda env: all(holds(x, env) for x in parts))
                if r:
                    return wit("B", m, m, q0, r[0], r[1], coords), None
        return None, "none"
    for u in range(len(Ls)):
        for m in Ls[u]["next"]:
            if m == u or Ls[m]["comps"] == Ls[u]["comps"]:
                continue
            for q0 in range(nR):
                P = pre(u, m, q0)
                # kind C
                qv = " ".join(f"(Q_{c} Real)" for c in coords)
                nopart = "(forall (" + qv + ") (not (or " + " ".join(to_q(partner(m, q)) for q in range(nR)) + ")))"
                st, vals = z3(decls, [P, nopart], timeout, model=True)
                if st == "sat":
                    env = rationalize(vals, decls, None)
                    if env is not None and exact_pre(env, u, m, q0):
                        fix = conj([f"(= L_{c} {smt_rat(env['L_' + c])})" for c in coords])
                        if all(z3(decls, [fix, partner(m, q)], timeout)[0] == "unsat" for q in range(nR)):
                            return wit("C", u, m, q0, 0, env, coords), None
                # kind A
                for k, g in enumerate(Ls[m]["comps"]):
                    if not rigid(m, k):
                        continue
                    for env in models(decls, [P, f"(> {g} 0)"], timeout):
                        if exact_pre(env, u, m, q0) and evq(I.parse_sexpr(g), env) > 0:
                            return wit("A", u, m, q0, k, env, coords), None
    if "B" in kinds:
        for u in range(len(Ls)):
            for m in Ls[u]["next"]:
                for q0 in range(nR):
                    r = try_b(pre(u, m, q0), m, lambda env: exact_pre(env, u, m, q0))
                    if r:
                        return wit("B", u, m, q0, r[0], r[1], coords), None
    return None, "none"


def smt_rat(x):
    x = Fraction(x)
    s = f"(/ {abs(x.numerator)} {x.denominator})" if x.denominator != 1 else f"{abs(x.numerator)}"
    return f"(- {s})" if x < 0 else s


def wit(kind, u, m, q0, k, env, coords):
    return {"kind": kind, "u": u, "m": m, "q0": q0, "k": k,
            "wL": [str(env["L_" + c]) for c in coords], "wR": [str(env["R_" + c]) for c in coords]}

# ---------------------------------------------------------------- driver

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=30)
    ap.add_argument("--out", default=os.path.join(ROOT, "docs/refute/witnesses.jsonl"))
    ap.add_argument("--suite", default=os.path.join(ROOT, "benchmarks/suite_v2"))
    ap.add_argument("--kinds", default="CAB")
    ap.add_argument("--reuse", help="earlier witnesses.jsonl: keep its witnesses, search only the rest")
    a = ap.parse_args()
    prev = {}
    if a.reuse:
        for l in open(a.reuse):
            r = json.loads(l)
            if r["witness"]:
                prev[(r["bench"], r["idx"])] = r["witness"]
    dims = bench_dims()
    paths = sorted(glob.glob(os.path.join(a.suite, "*/input.txt")))
    if a.only:
        keep = set(a.only.split(","))
        paths = [p for p in paths if os.path.basename(os.path.dirname(p)) in keep]
    os.makedirs(os.path.dirname(a.out), exist_ok=True)
    results = []
    for p in paths:
        bench = os.path.basename(os.path.dirname(p))
        if bench not in dims:
            print(f"{bench}: no bridge dimension, skipped", flush=True)
            continue
        text = open(p).read()
        b, rows = load_rows(text)
        muts = mutants(rows, b["L"]["vars"], b["R"]["vars"])
        d = os.path.join(SCRATCH, RUN, bench)
        os.makedirs(d, exist_ok=True)
        files, hashes = [], []
        for i, (op, label, key, new) in enumerate(muts):
            f = os.path.join(d, f"m{i:03d}.txt")
            mt = write(text, apply(rows, key, new))
            open(f, "w").write(mt)
            files.append(f)
            hashes.append(hashlib.sha256(mt.encode()).hexdigest())
        D = dump(bench, dims[bench], files)
        with ThreadPoolExecutor(a.jobs) as pool:
            futs = [None if (bench, i) in prev or "head" not in D.get(f, {}) else
                    pool.submit(search, D[f], a.timeout, a.kinds) for i, f in enumerate(files)]
            for i, (op, label, key, new) in enumerate(muts):
                if (bench, i) in prev:
                    w, why = prev[(bench, i)], None
                elif futs[i] is None:
                    w, why = None, D.get(files[i], {}).get("error", "dump")
                else:
                    w, why = futs[i].result()
                rec = {"bench": bench, "idx": i, "op": op, "mutant": label, "dim": dims[bench],
                       "rowsSame": D.get(files[i], {}).get("head", {}).get("rowsSame"),
                       "file": files[i], "sha256": hashes[i], "witness": w, "why": why}
                results.append(rec)
        nref = sum(1 for r in results if r["bench"] == bench and r["witness"])
        print(f"{bench}: mutants={len(muts)} witnesses={nref}", flush=True)
    if a.only and os.path.exists(a.out):
        # keep the other benchmarks' records; replace a visited benchmark's block in place
        new = {}
        for r in results:
            new.setdefault(r["bench"], []).append(r)
        merged, placed = [], set()
        for l in open(a.out):
            r = json.loads(l)
            if r["bench"] in new:
                if r["bench"] not in placed:
                    merged += new[r["bench"]]
                    placed.add(r["bench"])
            else:
                merged.append(r)
        merged += [r for b, rs in new.items() if b not in placed for r in rs]
        results = merged
    with open(a.out, "w") as fh:
        for r in results:
            fh.write(json.dumps(r) + "\n")


if __name__ == "__main__":
    main()
