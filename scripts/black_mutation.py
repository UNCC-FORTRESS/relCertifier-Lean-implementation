#!/usr/bin/env python3
"""Specification mutation with the Black-Okun-Yesha operators (ASE 2000), with an
independent refuter as ground truth (branch `mutation`).

Mutants. The declared relational invariant is a conjunction of polynomial atoms per left
mode. Of the operators of Black, Okun and Yesha, four stay inside that language:
  RRO  relational operator replacement, never by the opposite (<= -> <, >=; >= -> >, <=;
       < -> <=, >; > -> >=, <); equalities are not mutated (real-valued expressions);
  SNO  simple expression negation (<= -> >, >= -> <, < -> >=, > -> <=);
  MCO  missing condition: delete one atom from a row with at least two atoms;
  ORO  operand replacement, restricted to swapping a variable for its twin on the other
       side (L_x <-> R_x), all occurrences in the atom.
Each distinct atom is mutated in every row it occurs in, one mutation at a time.
ENO, LRO, ASO and stuck-at leave the conjunctive language (or give a vacuous row).

Refuter (ground truth, independent of relcert). Theorem 3 reads
    phi_u & op_R & D_u & D_ur  ->  [|(L*, R*)>> (phi & op_R & D).
A mutant is REFUTED when Z3 finds a joint state s satisfying the antecedent (stored left
mode u, some stored right mode u_r) and a left mode m in next(u) whose guard and domain
hold at s, such that one atom A of the mutated row of m
  (case A) already fails at s, or
  (case B) holds with equality at s, s is in the interior of m's domain, and the left flow
           of m strictly pushes A's expression out (Lie derivative),
and A is RIGID for the right system: in every right mode, over its domain, the right flow
cannot move A's expression back (Lie derivative along f_R of the right sign, for all left
values). The left run "switch to m, flow 0 (case A) or a short time (case B)" then reaches
a state where every right run violates A, so the mutated formula is not a forall-exists
invariant. Z3 `sat` is the only accepted evidence; unsat/unknown leave the mutant
UNREFUTED. The unmutated invariants are run through the refuter as a negative control
(all 50 are certified, hence true, so none may be refuted).

Usage: scripts/black_mutation.py [--relcert BIN] [--jobs 8] [--timeout 120]
                                 [--only a,b] [--json OUT] [--no-relcert]
"""
import argparse, glob, json, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import inv_smt as I

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
VERDICT = re.compile(r"^(\S+): (CERTIFIED|DECLINED|ERROR)", re.M)
Z3 = "/opt/homebrew/bin/z3"
RUN_CWD = os.environ.get("RELCERT_CWD", ROOT)

# ---------------------------------------------------------------- expressions

def parse_term(s, side, svars):
    s = s.strip()
    if s.startswith("smt2:"):
        return I.rename(I.parse_sexpr(s[5:].strip()), side, svars)
    p = I.Infix(s, side, svars)
    e = p.sum()
    assert p.p == len(p.toks), ("trailing tokens", s)
    return e


def parse_ode(s, side, svars):
    f = {}
    for part in s.split(";"):
        part = part.strip()
        if not part:
            continue
        lhs, rhs = part.split("=", 1)
        v = lhs.strip().rstrip("'").strip()
        assert v in svars, (v, svars)
        f[side + "_" + v] = parse_term(rhs, side, svars)
    for v in svars:
        f.setdefault(side + "_" + v, "0.0")
    return f


def has_var(e):
    if isinstance(e, list):
        return any(has_var(x) for x in e[1:])
    return bool(re.match(r"^[LR]_", e))


def deriv(e, v):
    if not isinstance(e, list):
        return "1.0" if e == v else "0.0"
    op, args = e[0], e[1:]
    if op == "+":
        return ["+"] + [deriv(a, v) for a in args] if len(args) > 1 else deriv(args[0], v)
    if op == "-":
        return ["-"] + [deriv(a, v) for a in args]
    if op == "*":
        terms = []
        for i in range(len(args)):
            terms.append(["*"] + args[:i] + [deriv(args[i], v)] + args[i + 1:])
        return ["+"] + terms if len(terms) > 1 else terms[0]
    if op == "/":
        assert len(args) == 2 and not has_var(args[1]), ("non-constant division", e)
        return ["/", deriv(args[0], v), args[1]]
    raise ValueError("cannot differentiate " + op)


def lie(e, f):
    return ["+"] + [["*", deriv(e, v), rhs] for v, rhs in f.items()]


def vars_in(e, acc):
    if isinstance(e, list):
        for x in e[1:]:
            vars_in(x, acc)
    elif re.match(r"^[LR]_", e):
        acc.add(e)
    return acc


def conj(fs):
    fs = [f for f in fs if f != "true"]
    if not fs:
        return "true"
    return fs[0] if len(fs) == 1 else ["and"] + fs


def disj(fs):
    fs = [f for f in fs if f != "false"]
    if not fs:
        return "false"
    return fs[0] if len(fs) == 1 else ["or"] + fs


def z3(f, timeout=20):
    vs = sorted(vars_in(f, set()))
    q = "".join(f"(declare-const {v} Real)\n" for v in vs) + f"(assert {I.show(f)})\n(check-sat)\n"
    try:
        r = subprocess.run([Z3, "-in", f"-T:{timeout}"], input=q, capture_output=True, text=True,
                           timeout=timeout + 10)
        out = (r.stdout.strip().splitlines() or ["error"])[0]
    except subprocess.TimeoutExpired:
        out = "timeout"
    return out if out in ("sat", "unsat") else "unknown"

# ---------------------------------------------------------------- model

NEG = {"<=": ">", ">=": "<", "<": ">=", ">": "<="}
RRO = {"<=": ["<", ">="], ">=": [">", "<="], "<": ["<=", ">"], ">": [">=", "<"]}


def norm_op(op):
    return {"==": "=", "=": "="}.get(op, op)


def fix_eq(e):
    if isinstance(e, list):
        return ["=" if e[0] == "==" else e[0]] + [fix_eq(x) for x in e[1:]]
    return e


def load(path):
    text = open(path).read()
    b = I.parse_bench(text)
    M = {}
    for side in ("L", "R"):
        sv = b[side]["vars"]
        M[side] = {}
        for name, d in b[side]["modes"].items():
            M[side][name] = {
                "f": parse_ode(d["ode"], side, sv),
                "guard": conj(I.atoms_of(d["guard"], side, sv)),
                "evolve_atoms": I.atoms_of(d["evolve"], side, sv),
                "next": [x.strip() for x in d["next"].strip()[1:-1].split(",") if x.strip()],
            }
            M[side][name]["evolve"] = conj(M[side][name]["evolve_atoms"])
    rows = [(ln, k, [fix_eq(a) for a in I.atoms_of(v, "", [])]) for ln, k, v in b["rows"]]
    for side in M.values():
        for d in side.values():
            d["evolve_atoms"] = [fix_eq(a) for a in d["evolve_atoms"]]
            d["evolve"] = fix_eq(d["evolve"]); d["guard"] = fix_eq(d["guard"])
    return text, b, M, rows


def strict(a):
    op = norm_op(a[0])
    if op == "<=": return ["<"] + a[1:]
    if op == ">=": return [">"] + a[1:]
    return a


def rigid(atom, MR):
    """The right flow cannot repair a violation of `atom` (for all left values)."""
    op = norm_op(atom[0])
    e = ["-", atom[1], atom[2]]
    for d in MR.values():
        le = lie(e, d["f"])
        if op in ("<=", "<"):
            bad = ["<", le, "0.0"]
        elif op in (">=", ">"):
            bad = [">", le, "0.0"]
        else:
            bad = ["not", ["=", le, "0.0"]]
        if z3(conj([d["evolve"], bad])) != "unsat":
            return False
    return True


def qe_project(f, rv):
    """Quantifier-free formula over the left variables equivalent to EXISTS rv. f, or None."""
    vs = sorted(v for v in vars_in(f, set()) if v not in rv)
    q = ("".join(f"(declare-const {v} Real)\n" for v in vs)
         + f"(assert (exists ({' '.join(f'({v} Real)' for v in rv)}) {I.show(f)}))\n"
         + "(apply (then qe simplify))\n")
    try:
        r = subprocess.run([Z3, "-in", "-T:20"], input=q, capture_output=True, text=True, timeout=30)
    except subprocess.TimeoutExpired:
        return None
    out = r.stdout
    if ("(goal" not in out or "exists" in out or "forall" in out or "!" in out
            or "timeout" in out or "unknown" in out or "error" in out):
        return None
    body = re.split(r"\(goal\s", out, maxsplit=1)[1].split(":precision", 1)[0]
    g = I.parse_sexpr("(and " + body + ")")
    return fix_eq(g)


def leaves_soon(phi, f):
    """Sufficient first-order condition: phi is FALSE at every small positive time along f."""
    if not isinstance(phi, list):
        return {"true": "false", "false": "true"}[phi]
    op = phi[0]
    if op == "and":
        return disj([leaves_soon(x, f) for x in phi[1:]])
    if op == "or":
        return conj([leaves_soon(x, f) for x in phi[1:]])
    if op == "not":
        return stays_soon(phi[1], f)
    e = ["-", phi[1], phi[2]]
    le = lie(e, f)
    if op in ("<=", "<"):
        return disj([[">", e, "0.0"], conj([["=", e, "0.0"], [">", le, "0.0"]])])
    if op in (">=", ">"):
        return disj([["<", e, "0.0"], conj([["=", e, "0.0"], ["<", le, "0.0"]])])
    if op == "=":
        return disj([["not", ["=", e, "0.0"]], ["not", ["=", le, "0.0"]]])
    raise ValueError("leaves_soon: " + str(op))


def stays_soon(phi, f):
    """Sufficient first-order condition: phi is TRUE at every small positive time along f."""
    if not isinstance(phi, list):
        return {"true": "true", "false": "false"}[phi]
    op = phi[0]
    if op == "and":
        return conj([stays_soon(x, f) for x in phi[1:]])
    if op == "or":
        return disj([stays_soon(x, f) for x in phi[1:]])
    if op == "not":
        return leaves_soon(phi[1], f)
    e = ["-", phi[1], phi[2]]
    le = lie(e, f)
    if op in ("<=", "<"):
        return disj([["<", e, "0.0"], conj([["=", e, "0.0"], ["<", le, "0.0"]])])
    if op in (">=", ">"):
        return disj([[">", e, "0.0"], conj([["=", e, "0.0"], [">", le, "0.0"]])])
    if op == "=":
        return "false"
    raise ValueError("stays_soon: " + str(op))


def refute(M, rowmap):
    """rowmap: left mode -> list of atoms (mutated). Returns (verdict, witness-kind)."""
    L, R = M["L"], M["R"]
    rok = disj([conj([d["evolve"], disj([R[n]["guard"] for n in d["next"] if n in R])])
                for d in R.values()])
    rig = {}
    done_c = {}
    done_d = {}
    unknown = False
    for m, dm in L.items():
        for atom in rowmap.get(m, []):
            key = I.show(atom)
            if key not in rig:
                rig[key] = rigid(atom, R)
            op = norm_op(atom[0])
            e = ["-", atom[1], atom[2]]
            preds = [u for u, du in L.items() if m in du["next"]]
            for u in preds:
                if u not in rowmap:
                    continue
                base = [conj(rowmap[u]), L[u]["evolve"], rok, dm["guard"]]
                # case C: after switching to m, no right state at all pairs with s_l
                rv = sorted(v for v in vars_in(conj([rok] + rowmap[m]), set()) if v.startswith("R_"))
                ren = lambda e: [ren(x) for x in e] if isinstance(e, list) else ("Q" + e[1:] if e in rv else e)
                if rv and not done_c.get((u, m)):
                    done_c[(u, m)] = True
                    qc = conj(base + [dm["evolve"], ["forall", [[("Q" + v[1:]), "Real"] for v in rv],
                                                     ["not", ren(conj([rok] + rowmap[m]))]]])
                    rc = z3(qc)
                    if rc == "sat":
                        return "REFUTED", f"C:{u}->{m}"
                    unknown |= rc == "unknown"
                # case D: the left flow of m leaves, immediately, the set of left states
                # that have any right partner (exact projection by quantifier elimination)
                if rv and not done_d.get((u, m)):
                    done_d[(u, m)] = True
                    P = qe_project(conj([rok] + rowmap[m]), rv)
                    if P is not None:
                        qd = conj(base + [conj([strict(a) for a in dm["evolve_atoms"]]),
                                          leaves_soon(P, {k: v for k, v in dm["f"].items()})])
                        rd = z3(qd)
                        if rd == "sat":
                            return "REFUTED", f"D:{u}->{m}"
                        unknown |= rd == "unknown"
                if not rig[key]:
                    continue
                # case A: the atom fails right after switching to m (zero-length flow)
                qa = conj(base + [dm["evolve"], ["not", atom]])
                ra = z3(qa)
                if ra == "sat":
                    return "REFUTED", f"A:{u}->{m}:{key}"
                unknown |= ra == "unknown"
                # case B: on the atom's boundary, the left flow of m pushes it out
                if op in ("<=", ">=", "="):
                    le = lie(e, dm["f"])
                    out = {"<=": [">", le, "0.0"], ">=": ["<", le, "0.0"],
                           "=": ["not", ["=", le, "0.0"]]}[op]
                    qb = conj(base + [conj([strict(a) for a in dm["evolve_atoms"]]),
                                      ["=", atom[1], atom[2]], out])
                    rb = z3(qb)
                    if rb == "sat":
                        return "REFUTED", f"B:{u}->{m}:{key}"
                    unknown |= rb == "unknown"
    return ("UNKNOWN" if unknown else "UNREFUTED"), None

# ---------------------------------------------------------------- mutants

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
            # RRO restricted to the non-strict language relcert accepts faithfully: the only
            # non-opposite replacement that stays non-strict is <= <-> >=, which is also the
            # closure of SNO's negation. Strict atoms (<, >) are lowered by relcert as their
            # non-strict closure (Trusted/InvComponents.lean), so strict mutants are not tested.
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
            atoms = kept if kept else atoms   # MCO only deletes from conjunctions
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


def run_handoff(relcert, text, timeout=120):
    """Theorem 3's third premise: every declared left mode change satisfies the handoff
    condition. `relcert <file>` alone does not check it; `relcert --handoff` does."""
    d = tempfile.mkdtemp()
    p = os.path.join(d, "input.txt")
    open(p, "w").write(text)
    env = dict(os.environ, RELCERT_IMPLIED_CUT="1")
    try:
        r = subprocess.run([relcert, "--handoff", p], capture_output=True, text=True, env=env,
                           timeout=timeout, cwd=RUN_CWD)
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    m = re.search(r"(\d+)/(\d+) transitions checked, (\d+) passed, failing: (\S+)", r.stdout)
    if not m:
        return "ERROR"
    ok = r.returncode == 0 and m.group(1) == m.group(2) == m.group(3) and m.group(4) == "-"
    return "PASS" if ok else "FAIL"


def run_relcert(relcert, text, timeout):
    """Full verdict: the handoff check, then the cover search. CERTIFIED only if both pass."""
    h = run_handoff(relcert, text)
    if h != "PASS":
        return "DECLINED" if h == "FAIL" else h
    d = tempfile.mkdtemp()
    p = os.path.join(d, "input.txt")
    open(p, "w").write(text)
    env = dict(os.environ, RELCERT_IMPLIED_CUT="1")
    try:
        r = subprocess.run([relcert, p], capture_output=True, text=True, env=env,
                           timeout=timeout, cwd=RUN_CWD)
        m = VERDICT.search(r.stdout + r.stderr)
        return m.group(2) if m else "ERROR"
    except subprocess.TimeoutExpired:
        return "TIMEOUT"

# ---------------------------------------------------------------- driver

def study(path, a, pool):
    name = os.path.basename(os.path.dirname(path))
    text, b, M, rows = load(path)
    rowmap0 = {k: at for _, k, at in rows}
    control = refute(M, rowmap0)[0]
    jobs = []
    for opname, label, key, new in mutants(rows, b["L"]["vars"], b["R"]["vars"]):
        mrows = apply(rows, key, new)
        rowmap = {k: at for _, k, at in mrows}
        ref = pool.submit(refute, M, rowmap)
        rc = None if a.no_relcert else pool.submit(run_relcert, a.relcert, write(text, mrows), a.timeout)
        jobs.append((opname, label, ref, rc))
    sanity = None if a.no_relcert else run_relcert(a.relcert, write(text, rows), a.timeout)
    res = []
    for opname, label, ref, rc in jobs:
        v, w = ref.result()
        res.append({"op": opname, "mutant": label, "refuter": v, "witness": w,
                    "relcert": None if rc is None else rc.result()})
    return name, control, sanity, res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--relcert", default=os.path.join(ROOT, ".lake", "build", "bin", "relcert"))
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--only")
    ap.add_argument("--json")
    ap.add_argument("--jsonl")
    ap.add_argument("--no-relcert", action="store_true")
    ap.add_argument("--suite", default=os.path.join(ROOT, "benchmarks/suite_v2"))
    a = ap.parse_args()
    paths = sorted(glob.glob(os.path.join(a.suite, "*/input.txt")))
    if a.only:
        keep = set(a.only.split(","))
        paths = [p for p in paths if os.path.basename(os.path.dirname(p)) in keep]
    out = {}
    with ThreadPoolExecutor(a.jobs) as pool:
        for p in paths:
            try:
                name, control, sanity, res = study(p, a, pool)
            except Exception as e:
                name = os.path.basename(os.path.dirname(p))
                print(f"{name}: SCRIPT ERROR {e!r}", flush=True)
                out[name] = {"error": repr(e)}
                continue
            out[name] = {"control": control, "sanity": sanity, "mutants": res}
            if a.jsonl:
                with open(a.jsonl, "a") as fh:
                    fh.write(json.dumps({"bench": name, **out[name]}) + "\n")
            ref = [r for r in res if r["refuter"] == "REFUTED"]
            bad = [r for r in ref if r["relcert"] == "CERTIFIED"]
            print(f"{name}: control={control} sanity={sanity} mutants={len(res)} "
                  f"refuted={len(ref)} refuted&certified={len(bad)}", flush=True)
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
