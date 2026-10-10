#!/usr/bin/env python3
"""Re-run benchmarks/suite_v2 and regenerate the mechanism matrix of docs/SUITE-REDESIGN.md.

For every `benchmarks/suite_v2/<name>/input.txt` the script runs the tool four ways and
reads the evidence off the tool's own output (never off the file's header):

  1. `relcert <input>` with RELCERT_DEBUG=1   -> verdict, wall time, [prune] line,
                                                 [admissible]/[cut] diagnostics
  2. `relcert --emit-cover <input> x`         -> the emitted cover: per left mode the
                                                 lambda, the budget, the per-right-mode
                                                 flag rows (jointOK, dynPre, dynPost) and
                                                 the admissible starts
  3. RELCERT_NO_PRUNE=1 relcert <input>        -> the pruning counter-run
  4. RELCERT_NO_CUT=1 relcert <input>          -> the checked-cut counter-run
  4b. RELCERT_NO_IMPLIED_CUT=1 relcert <input> -> the implied-cut counter-run (legacy
                                                 guard-conjunct cuts only)
  4c. RELCERT_NO_LINEAR_CUT=1 relcert <input>  -> the linear-form counter-run (closures
                                                 and implied atoms kept, the L7 chain off)
  5. `relcert --handoff <input>`               -> the cross-mode handoff queries
                                                 (vacuous = every row identical)

Every run except 4b sets RELCERT_IMPLIED_CUT=1: the suite_v2 runs use the widened cut
channel (closures of strict guard conjuncts, implied-contraction atoms, and the
linear-form chain of recognized second-order pairs; Checker/EvolStrengtheningX.lean),
which is off by default (a run without it searches with the guard-conjunct certificate
alone, the one the 19 carried-over legacy instances quote). The `[cut-x]` debug lines list the widened atoms (kind, O1 justification,
O2 route, conditioning atoms).

From (2) the script REPLAYS the verified checker's structural cover (`decideCovered`,
RelCertifier/Checker/Checker.lean) on the emitted flags and the file's declared
successor lists minus the pruned edges, in the checker's own alternative order
(base, joint step, dynamic reposition),
and records the derivation
it finds: which right modes the cover path visits, whether a right-only reposition
step is on it, and the largest number of distinct non-self retained successors at a
joint step (branching). The mechanism columns are then DERIVED:

  M1  some left mode's cover has lambda != 1 (and whether that pairing's dynamics are
      polynomial of degree >= 2: a product of state variables, or a square)
  M2  some left mode's budget >= 2 and its derivation takes a joint step (several
      right segments); "RO" if a right-only reposition step is on the path
  M3  some joint step on the path has >= 2 distinct non-self retained successors
  M4  the tool prunes at least one edge AND RELCERT_NO_PRUNE=1 DECLINES
  M5  the invariant rows differ between left modes, the --handoff queries are
      non-vacuous and all unsat, and the benchmark is CERTIFIED
  M6  some mode keeps a checked cut AND RELCERT_NO_CUT=1 DECLINES
  M6+ some mode keeps a widened atom (closure / implied-contraction / linear-form /
      derived-bound) AND RELCERT_NO_IMPLIED_CUT=1 DECLINES: the cuts are load-bearing
      only with the widened atoms
  M6L some mode keeps a linear-form or derived-bound atom AND RELCERT_NO_LINEAR_CUT=1
      DECLINES: the L7 chain (docs/SUITE-REDESIGN.md section 13) is load-bearing
  domains: "per-mode" if some side's modes declare different evolve domains (the
      paper's Eq. 2 model; the uniform-evolve discipline of the Lean lift does not
      cover these yet), else "uniform"
  M7  the scenario kind is read from the file's `# scenario:` line; the dimension and
      invariant shape are computed from the file

A mechanism is credited only when the counter-run or the replayed derivation shows it
mattered. Vacuous exercises are printed as such (`M5: rows identical (vacuous)`,
`M6: cuts kept but NO_CUT still certifies`, ...).

Usage:
  scripts/suite_v2_matrix.py [--bench DIR] [--relcert BIN] [--json OUT.json] [--md OUT.md]
                             [--only name1,name2] [--timeout SEC]

The normalized-hash duplicate check of docs/history/SUITE-DEDUPE.md is run over the whole set.
"""
import argparse, hashlib, json, os, re, subprocess, sys, time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))

# Family of a benchmark (by name prefix) and the scenario kind of the 19 benchmarks that
# were copied unchanged from the retired legacy suite (their headers carry no
# `# scenario:` line).
FAMILIES = [
    ("acc_", "ACC under sensor spoofing / retune"),
    ("quad_", "Quadrotor climb, lighter airframe"),
    ("charger_", "Battery charger"),
    ("heater_", "Heater cycle"),
    ("platoon_", "Platoon follower, delayed link"),
    ("platoon3_", "Platoon string, three followers"),
    ("rover_patrol_", "Rover patrol (zones)"),
    ("rover3tier_", "Rover patrol (zones)"),
    ("match_multi_rate", "Rover patrol (zones)"),
    ("arm_plateau_", "Arm, leading reference"),
    ("refinement_ladder_rover_", "Terrain/position ladder"),
    ("rover_dof_terrain_", "Terrain/position ladder"),
    ("story1_", "Story ladders"),
    ("story2_", "Story ladders"),
    ("story3_", "Story ladders"),
    ("watertank", "Watertank"),
    ("sat_detumble_", "Rigid-body detumbling (polynomial)"),
    ("sat3w_detumble_", "Rigid-body detumbling (polynomial)"),
]
KEPT_SCENARIO = {
    "watertank": "sensor-attack",
    "match_multi_rate": "model-refinement",
    "rover3tier_rung12": "model-refinement",
}
def family_of(name):
    for pre, fam in FAMILIES:
        if name.startswith(pre):
            return fam
    return "other"

# ----------------------------------------------------------------------------- parsing

def strip_comment(line):
    return line.split("#", 1)[0].rstrip()

def parse_input(path):
    """Minimal reader of the benchmark format (sections, keys, modes, rows)."""
    prob = {"problem": {}, "L": {"vars": [], "eps": None, "modes": {}, "order": []},
            "R": {"vars": [], "eps": None, "modes": {}, "order": []}, "rows": {}, "row_order": [],
            "header": [], "scenario": None, "mechanisms": None}
    cur = None
    for raw in open(path, encoding="utf-8"):
        s = raw.rstrip("\n")
        if s.strip().startswith("#"):
            prob["header"].append(s)
            m = re.match(r"#\s*scenario\s*:\s*(.+)$", s.strip())
            if m: prob["scenario"] = m.group(1).strip()
            m = re.match(r"#\s*mechanisms\s*:\s*(.+)$", s.strip())
            if m: prob["mechanisms"] = m.group(1).strip()
            continue
        s = strip_comment(s)
        if not s.strip():
            continue
        m = re.match(r"\[(.+)\]$", s.strip())
        if m:
            cur = m.group(1).strip()
            mm = re.match(r"(Lsys|Rsys)\.mode\.(\w+)$", cur)
            if mm:
                side = "L" if mm.group(1) == "Lsys" else "R"
                prob[side]["modes"][mm.group(2)] = {"ode": "", "guard": "", "evolve": "", "next": []}
                prob[side]["order"].append(mm.group(2))
            continue
        if "=" not in s:
            continue
        k, v = s.split("=", 1)
        k, v = k.strip(), v.strip()
        if cur == "problem":
            prob["problem"][k] = v
        elif cur in ("Lsys", "Rsys"):
            side = "L" if cur == "Lsys" else "R"
            if k == "state_vars":
                prob[side]["vars"] = [x.strip() for x in v.strip("[]").split(",") if x.strip()]
            elif k == "epsilon":
                prob[side]["eps"] = v
        elif cur and re.match(r"(Lsys|Rsys)\.mode\.", cur):
            side = "L" if cur.startswith("Lsys") else "R"
            name = cur.split(".")[-1]
            if k == "next":
                prob[side]["modes"][name]["next"] = [x.strip() for x in v.strip("[]").split(",") if x.strip()]
            else:
                prob[side]["modes"][name][k] = v
        elif cur == "relational_invariant":
            prob["rows"][k] = v
            prob["row_order"].append(k)
    return prob

def tolerance_masked_hash(path):
    """docs/history/SUITE-DEDUPE.md tolerance-only variants: the normalized text with every numeric
    literal of the [relational_invariant] rows masked -- two files with the same masked hash
    differ at most in their tolerance constants."""
    out, inrows = [], False
    for raw in open(path, encoding="utf-8"):
        s = re.sub(r"#.*$", "", raw).rstrip()
        if not s.strip() or re.match(r"^name\s*=", s.strip()):
            continue
        if re.match(r"^\[.*\]$", s.strip()):
            inrows = s.strip() == "[relational_invariant]"
        elif inrows:
            s = re.sub(r"(?<![A-Za-z_])-?\d+(?:\.\d+)?", "#", s)
        out.append(s)
    return hashlib.md5(("\n".join(out) + "\n").encode()).hexdigest()

def normalized_hash(path):
    """docs/history/SUITE-DEDUPE.md: comments, trailing blanks, blank lines and the `name =` line removed."""
    out = []
    for raw in open(path, encoding="utf-8"):
        s = re.sub(r"#.*$", "", raw).rstrip()
        if not s.strip():
            continue
        if re.match(r"^name\s*=", s.strip()):
            continue
        out.append(s)
    return hashlib.md5(("\n".join(out) + "\n").encode()).hexdigest()

# ----------------------------------------------------------------------------- shape analysis

def _sexpr_tokens(expr):
    return re.findall(r"\(|\)|[^\s()]+", expr)

def _parse_sexpr(toks, i=0):
    t = toks[i]
    if t == "(":
        out = []
        i += 1
        while toks[i] != ")":
            node, i = _parse_sexpr(toks, i)
            out.append(node)
        return out, i + 1
    return t, i + 1

def _degree(node, vars_):
    """Polynomial degree in the state variables of a parsed smt2 term (None = not polynomial)."""
    if isinstance(node, str):
        return 1 if node in vars_ else 0
    op, args = node[0], node[1:]
    degs = [_degree(a, vars_) for a in args]
    if any(d is None for d in degs):
        return None
    if op in ("+", "-"):
        return max(degs) if degs else 0
    if op == "*":
        return sum(degs)
    if op == "/":
        return degs[0] if len(degs) == 2 and degs[1] == 0 else None
    return None

def _infix_degree(expr, vars_):
    # infix RHS of the form a*b + c ... : count variable factors per product term
    best = 0
    for term in re.split(r"(?<![*\/])[+-]", expr):
        nv = sum(1 for tok in re.findall(r"[A-Za-z_]\w*", term) if tok in vars_)
        best = max(best, nv)
    return best

def ode_is_nonlinear(ode_text, vars_):
    """Some right-hand side has polynomial degree >= 2 in the state variables."""
    for rhs in [p.strip() for p in ode_text.split(";") if p.strip()]:
        if "=" not in rhs:
            continue
        expr = rhs.split("=", 1)[1].strip()
        if expr.startswith("smt2:"):
            try:
                node, _ = _parse_sexpr(_sexpr_tokens(expr[5:].strip()))
            except (IndexError, ValueError):
                continue
            d = _degree(node, vars_)
            if d is not None and d >= 2:
                return True
        else:
            if _infix_degree(expr, vars_) >= 2:
                return True
    return False

def row_shape(row):
    r = row.strip()
    if r.startswith("smt2:"):
        body = r[5:]
        conj = body.lstrip().startswith("(and")
        quad = bool(re.search(r"\(\*\s*[LR]_\w+\s+[LR]_\w+", body)) or bool(re.search(r"\(\*\s*\d[\d.]*\s*\(\*\s*[LR]_\w+\s+[LR]_\w+", body)) or bool(re.search(r"\(\*\s*[LR]_\w+\s*\(\*", body))
        # any product of two projected variables anywhere
        quad = quad or len(re.findall(r"\(\*[^()]*[LR]_\w+[^()]*[LR]_\w+", body)) > 0
        if quad and conj: return "quadratic+conj"
        if quad: return "quadratic"
        if conj: return "conjunctive"
        return "linear"
    if re.search(r"\w\[[lr]\]\s*\*\s*\w+\[[lr]\]", r) or re.search(r"\*\s*\w\[[lr]\]\s*\*\s*\w\[[lr]\]", r):
        return "quadratic"
    if " and " in r:
        return "conjunctive"
    return "linear"

# ----------------------------------------------------------------------------- tool runs

def run(cmd, env_extra=None, timeout=600):
    env = dict(os.environ)
    if env_extra:
        env.update(env_extra)
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=timeout, cwd=ROOT)
        return p.returncode, p.stdout, p.stderr, time.time() - t0
    except subprocess.TimeoutExpired:
        return -1, "", "TIMEOUT", time.time() - t0

VERDICT_RE = re.compile(r"^(\S+): (CERTIFIED|DECLINED|ERROR)(?: \((\d+)ms\))?(.*)$", re.M)

def verdict_of(stdout):
    m = VERDICT_RE.search(stdout)
    if not m:
        return ("UNKNOWN", None, stdout.strip()[-200:])
    return (m.group(2), int(m.group(3)) if m.group(3) else None, m.group(4).strip())

def parse_cover(text):
    """Parse the `--emit-cover` literal. Returns (pruned, covers) or None."""
    if "CoverEmitE" not in text:
        return None
    name_m = re.search(r'⟨"([^"]+)", \[(.*?)\], \[\s*$', text, re.M)
    pruned = []
    pm = re.search(r'CoverEmitE :=\s*⟨"[^"]+", \[(.*?)\], \[', text, re.S)
    if pm:
        pruned = re.findall(r'\("([^"]+)", "([^"]+)"\)', pm.group(1))
    covers = []
    for lm in re.finditer(r'⟨"(\w+)", \(([-\d]+) : ℚ\) / (\d+), (\d+), \[(.*?)\], \[(.*?)\], \[(.*?)\]⟩,?\s*$', text, re.M):
        mL = lm.group(1)
        lam = Fraction(int(lm.group(2)), int(lm.group(3)))
        budget = int(lm.group(4))
        flags = []
        for fm in re.finditer(r'⟨"(\w+)", (true|false), (true|false), (true|false)⟩', lm.group(5)):
            flags.append({"name": fm.group(1), "jointOK": fm.group(2) == "true",
                          "dynPre": fm.group(3) == "true", "dynPost": fm.group(4) == "true"})
        adm = re.findall(r'"(\w+)"', lm.group(6))
        covers.append({"mL": mL, "lam": lam, "budget": budget, "flags": flags, "admissible": adm})
    return pruned, covers

# ----------------------------------------------------------------------------- cover replay

def is_node(f):
    return f["jointOK"] or f["dynPre"] or f["dynPost"]

class Replay:
    """`decideCovered` (Checker/Checker.lean) over `buildCoverGraph` (Checker/CoverEmit.lean),
    with a derivation record: the first alternative that succeeds, in the checker's order."""
    def __init__(self, flags, succ, pruned):
        self.nodes = [f for f in flags if is_node(f)]
        self.k = len(self.nodes)
        self.idx = {f["name"]: i for i, f in enumerate(self.nodes)}
        self.succ = succ
        self.pruned = set(pruned)
        self.memo = {}
        # edges: src idx -> list of (tgt idx or sentinel, tgt name)
        self.edges = {}
        for f in self.nodes:
            s = self.idx[f["name"]]
            self.edges[s] = []
            for t in succ.get(f["name"], []):
                if (f["name"], t) in self.pruned:
                    continue
                self.edges[s].append((self.idx.get(t, self.k), t))
    def retained(self, q):
        return [q] + [t for t, _ in self.edges.get(q, [])]
    def exits(self, q):
        return [t for t, _ in self.edges.get(q, []) if t != q]
    def mode(self, q):
        return self.nodes[q] if q < self.k else None
    def covered(self, fuel, q, B, sigma):
        """Returns a derivation dict or None."""
        key = (fuel, q, B, sigma)
        if key in self.memo:
            return self.memo[key]
        res = None
        if fuel > 0:
            m = self.mode(q)
            if m is not None:
                if m["jointOK"] and B <= 1:
                    res = {"kind": "base", "q": m["name"], "B": B, "sigma": sigma}
                elif m["jointOK"] and 1 < B:
                    kids = []
                    ok = True
                    for q2 in self.retained(q):
                        d = self.covered(fuel - 1, q2, B - 1, "postJ")
                        if d is None:
                            ok = False; break
                        kids.append(d)
                    if ok:
                        res = {"kind": "joint", "q": m["name"], "B": B, "sigma": sigma,
                               "retained": [self.nodes[t]["name"] if t < self.k else "<sentinel>" for t in self.retained(q)],
                               "kids": kids}
                if res is None:
                    for kind, flag in (("repoDyn", "dynPre" if sigma == "preJ" else "dynPost"),):
                        if m[flag] and B > 0 and self.exits(q):
                            kids = []
                            ok = True
                            for q2 in self.exits(q):
                                d = self.covered(fuel - 1, q2, B, sigma)
                                if d is None:
                                    ok = False; break
                                kids.append(d)
                            if ok:
                                res = {"kind": kind, "q": m["name"], "B": B, "sigma": sigma,
                                       "exits": [self.nodes[t]["name"] if t < self.k else "<sentinel>" for t in self.exits(q)],
                                       "kids": kids}
                                break
        self.memo[key] = res
        return res

def summarize_derivation(d, acc):
    """Collect kinds, modes visited, max branching at joint steps, RO use."""
    if d is None:
        return
    acc["kinds"].add(d["kind"])
    acc["modes"].add(d["q"])
    if d["kind"] == "joint":
        nonself = set(x for x in d["retained"] if x != d["q"])
        acc["branch"] = max(acc["branch"], len(nonself))
        acc["joint_steps"] += 1
        acc["joint_modes"].add(d["q"])
    if d["kind"] == "repoDyn":
        acc["ro"] = True
        acc["ro_modes"].add(d["q"])
    for k in d.get("kids", []):
        summarize_derivation(k, acc)

def path_string(d):
    """A compact rendering of the derivation as the set of distinct steps it uses (the
    derivation is a DAG: a self-loop at budget B-1 is the same configuration however
    often it is reached), one `mode:kind(B,sigma)->[successor configs]` per step."""
    if d is None:
        return "?"
    steps = []
    seen = set()
    def cfg(x):
        return f"{x['q']}@{x['B']}{'' if x['kind']=='base' else ''}"
    def walk(x):
        key = (x["kind"], x["q"], x["B"], x["sigma"])
        if key in seen:
            return
        seen.add(key)
        if x["kind"] == "base":
            steps.append(f"{x['q']}:base(B={x['B']})")
        elif x["kind"] == "joint":
            steps.append(f"{x['q']}:joint(B={x['B']})->[" + ", ".join(cfg(k) for k in x["kids"]) + "]")
        else:
            steps.append(f"{x['q']}:{x['kind']}(B={x['B']},{x['sigma']})->[" + ", ".join(cfg(k) for k in x["kids"]) + "]")
        for k in x.get("kids", []):
            walk(k)
    walk(d)
    return "; ".join(steps)

# ----------------------------------------------------------------------------- Z3 profile

def _sx(text):
    toks = re.findall(r"\(|\)|[^\s()]+", text)
    node, _ = _parse_sexpr(toks, 0)
    return node

def _sides(n, acc):
    if isinstance(n, str):
        if n.startswith("L_"): acc.add("L")
        if n.startswith("R_"): acc.add("R")
    else:
        for x in n: _sides(x, acc)

def _sdeg(n):
    if isinstance(n, str):
        return 1 if (n.startswith("L_") or n.startswith("R_")) else 0
    ds = [_sdeg(x) for x in n[1:]]
    return sum(ds) if n[0] == "*" else (max(ds) if ds else 0)

def query_shape(q):
    """Shape of the asserted formula's last top-level conjunct X: route A (X = gdot > 0),
    B (X = g = 0 and gdot >= 0), C (X = g >= 0 and gdot > 0), or 'other' (static region,
    entry, non-connection source queries and anything else are 'other' unless they match
    a route shape). A-shaped terms of degree <= 1 (affine Lie derivatives and static region queries alike) are counted as "A-or-static"."""
    i = q.find("(assert ")
    if i < 0:
        return "other", ""
    try:
        f = _sx(q[i:])[1]
    except (IndexError, ValueError):
        return "other", ""
    X = f[-1] if (isinstance(f, list) and f and f[0] == "and") else f
    side = set(); _sides(X, side); side = "".join(sorted(side))
    if isinstance(X, list) and len(X) == 3 and X[0] == "and" and isinstance(X[1], list) and X[1][0] == "=":
        return "B", side
    if isinstance(X, list) and len(X) == 3 and X[0] == "and" and isinstance(X[1], list) and X[1][0] == ">=" and isinstance(X[2], list) and X[2][0] == ">":
        return "C", side
    if isinstance(X, list) and X and X[0] == ">":
        return ("A" if _sdeg(X[1]) >= 2 else "A-or-static"), side
    return "other", side

def z3_profile(relcert, path, timeout):
    """One extra run through scripts/z3_timing_proxy.py: number of Z3 queries, total and
    maximal Z3 wall time (from the (check-sat) to the sentinel, per query), and the UNSAT
    queries by shape (A/B/C on both sides = joint or reposition flow certificates)."""
    import tempfile
    proxy = os.path.join(HERE, "z3_timing_proxy.py")
    with tempfile.NamedTemporaryFile(suffix=".jsonl", delete=False) as tf:
        logp = tf.name
    try:
        rc, out, err, wall = run([relcert, path], {"RELCERT_IMPLIED_CUT": "1", "RELCERT_Z3": proxy,
                                                   "Z3PROXY_LOG": logp}, timeout)
        rs = [json.loads(l) for l in open(logp) if l.strip()]
    finally:
        os.unlink(logp)
    shapes = {}
    for r in rs:
        if r.get("verdict") == "unsat":
            sh, side = query_shape(r.get("q", ""))
            key = sh + ("" if side == "LR" else "/" + (side or "-"))
            shapes[key] = shapes.get(key, 0) + 1
    return {"queries": len(rs), "z3_ms": round(sum(r["ms"] for r in rs)), "z3_max_ms": round(max([r["ms"] for r in rs] or [0])),
            "proxied_wall_s": round(wall, 2), "unsat_shapes": dict(sorted(shapes.items()))}

# ----------------------------------------------------------------------------- per benchmark

def analyze(name, path, relcert, timeout, z3time=False):
    prob = parse_input(path)
    scenario = prob["scenario"] or KEPT_SCENARIO.get(name) or ("model-refinement" if family_of(name) in ("Terrain/position ladder", "Story ladders") else None)
    rec = {"name": name, "path": os.path.relpath(path, ROOT), "scenario": scenario, "family": family_of(name),
           "declared_mechanisms": prob["mechanisms"],
           "dimL": len(prob["L"]["vars"]), "dimR": len(prob["R"]["vars"]),
           "modesL": len(prob["L"]["order"]), "modesR": len(prob["R"]["order"]),
           "epsL": prob["L"]["eps"], "epsR": prob["R"]["eps"],
           "lambda_min": prob["problem"].get("lambda_min"), "lambda_max": prob["problem"].get("lambda_max"),
           "rows": prob["rows"], "hash": normalized_hash(path), "tol_hash": tolerance_masked_hash(path)}
    rows = [prob["rows"][k] for k in prob["row_order"]]
    rec["rows_identical"] = all(r == rows[0] for r in rows) if rows else True
    shapes = sorted(set(row_shape(r) for r in rows))
    rec["inv_shape"] = "+".join(shapes)
    rec["per_mode_evolve"] = any(
        len(set(prob[side]["modes"][m]["evolve"] for m in prob[side]["order"])) > 1 for side in ("L", "R"))
    rec["nonlinear_L"] = any(ode_is_nonlinear(prob["L"]["modes"][m]["ode"], prob["L"]["vars"]) for m in prob["L"]["order"])
    rec["nonlinear_R"] = any(ode_is_nonlinear(prob["R"]["modes"][m]["ode"], prob["R"]["vars"]) for m in prob["R"]["order"])

    # 1. main run
    rc, out, err, wall = run([relcert, path], {"RELCERT_DEBUG": "1", "RELCERT_IMPLIED_CUT": "1"}, timeout)
    v, ms, extra = verdict_of(out)
    rec["verdict"] = v; rec["ms"] = ms; rec["verdict_extra"] = extra
    rec["prune_line"] = next((l.strip() for l in err.splitlines() if l.strip().startswith("[prune]")), None)
    rec["admissible_lines"] = [l.strip() for l in err.splitlines() if l.strip().startswith("[admissible]")]
    rec["cut_lines"] = [l.strip() for l in err.splitlines() if l.strip().startswith("[cut]") and "0 conjunct" not in l]
    rec["cutx_lines"] = [l.strip() for l in err.splitlines() if l.strip().startswith("[cut-x]")]
    rec["route_lines"] = [l.strip() for l in err.splitlines() if l.strip().startswith("[route]")]
    rec["repo_lines"] = [l.strip() for l in err.splitlines() if l.strip().startswith("[repo-dyn-pre]")]
    rec["debug_stderr"] = err
    rec["wall_s"] = round(wall, 2)
    if z3time:
        rec["z3"] = z3_profile(relcert, path, timeout)

    # 2. cover
    rc, out2, err2, _ = run([relcert, "--emit-cover", path, "x"], {"RELCERT_IMPLIED_CUT": "1"}, timeout)
    cov = parse_cover(out2) if v == "CERTIFIED" else None
    rec["covers"] = []
    rec["pruned"] = []
    if cov:
        pruned, covers = cov
        rec["pruned"] = pruned
        succ = {m: prob["R"]["modes"][m]["next"] for m in prob["R"]["order"]}
        for c in covers:
            rp = Replay(c["flags"], succ, pruned)
            fuel = c["budget"] * (rp.k + 1) + 1
            acc = {"kinds": set(), "modes": set(), "branch": 0, "ro": False, "joint_steps": 0,
                   "joint_modes": set(), "ro_modes": set()}
            paths = {}
            allok = True
            for start in c["admissible"]:
                q = rp.idx.get(start, rp.k)
                d = rp.covered(fuel, q, c["budget"], "preJ")
                if d is None:
                    allok = False
                paths[start] = path_string(d)
                summarize_derivation(d, acc)
            rec["covers"].append({
                "mL": c["mL"], "lam": str(c["lam"]), "lam_float": float(c["lam"]), "budget": c["budget"],
                "admissible": c["admissible"], "replay_ok": allok,
                "flags": {f["name"]: "".join(k[0] if f[k] else "-" for k in ("jointOK", "dynPre", "dynPost")) for f in c["flags"]},
                "kinds": sorted(acc["kinds"]), "modes_on_path": sorted(acc["modes"]),
                "joint_modes": sorted(acc["joint_modes"]), "ro_modes": sorted(acc["ro_modes"]),
                "branching": acc["branch"], "right_only": acc["ro"], "joint_steps": acc["joint_steps"],
                "paths": paths})

    # 3./4. counter-runs
    rc, o3, e3, _ = run([relcert, path], {"RELCERT_NO_PRUNE": "1", "RELCERT_IMPLIED_CUT": "1"}, timeout)
    rec["no_prune_verdict"] = verdict_of(o3)[0]
    rec["no_prune_ms"] = verdict_of(o3)[1]
    rc, o4, e4, _ = run([relcert, path], {"RELCERT_NO_CUT": "1", "RELCERT_IMPLIED_CUT": "1"}, timeout)
    rec["no_cut_verdict"] = verdict_of(o4)[0]
    rec["no_cut_ms"] = verdict_of(o4)[1]
    # 4b. the implied-cut counter-run (legacy guard-conjunct cuts only)
    rc, o4b, e4b, _ = run([relcert, path], {"RELCERT_NO_IMPLIED_CUT": "1"}, timeout)
    rec["no_implied_verdict"] = verdict_of(o4b)[0]
    rec["no_implied_ms"] = verdict_of(o4b)[1]
    # 4c. the linear-form counter-run (closures and implied atoms kept, the L7 chain off)
    rc, o4c, e4c, _ = run([relcert, path], {"RELCERT_NO_LINEAR_CUT": "1", "RELCERT_IMPLIED_CUT": "1"}, timeout)
    rec["no_linear_verdict"] = verdict_of(o4c)[0]
    rec["no_linear_ms"] = verdict_of(o4c)[1]

    # 5. handoff
    rc, o5, e5, _ = run([relcert, "--handoff", path], {}, timeout)
    hm = re.search(r"\[handoff\] \S+: (\d+)/(\d+) transitions checked, (\d+) passed, failing: ([^(]+?)(\s*\(vacuous[^)]*\))? \((\d+)ms\)", o5 + e5)
    if hm:
        rec["handoff"] = {"checked": int(hm.group(1)), "declared": int(hm.group(2)), "passed": int(hm.group(3)),
                          "failing": hm.group(4).strip(), "vacuous": bool(hm.group(5)), "ms": int(hm.group(6))}
    else:
        rec["handoff"] = {"raw": (o5 + e5).strip()[-300:]}

    # ---- derived mechanism cells
    cells = {}
    cert = v == "CERTIFIED"
    lams = [c for c in rec["covers"] if c["lam_float"] != 1.0]
    if cert and lams:
        nl = rec["nonlinear_L"] or rec["nonlinear_R"]
        cells["M1"] = "yes: " + ", ".join(f"{c['mL']} λ={c['lam']}" for c in lams) + (" (polynomial dynamics)" if nl else " (affine dynamics)")
    else:
        cells["M1"] = "no (λ=1 everywhere)" if cert else "no"
    multi = [c for c in rec["covers"] if c["budget"] >= 2 and c["joint_steps"] >= 1]
    if cert and multi:
        s = ", ".join(f"{c['mL']} B={c['budget']} via {'/'.join(c['joint_modes'])}" + (" +RO" if c["right_only"] else "") for c in multi)
        cells["M2"] = "yes: " + s
    else:
        ro = [c for c in rec["covers"] if c["right_only"]]
        cells["M2"] = ("no (single segment" + (", RO used" if ro else "") + ")") if cert else "no"
    rec["right_only_any"] = any(c["right_only"] for c in rec["covers"])
    br = [c for c in rec["covers"] if c["branching"] >= 2]
    cells["M3"] = ("yes: " + ", ".join(f"{c['mL']} branch={c['branching']}" for c in br)) if (cert and br) else ("no (max non-self successors at a joint step = %d)" % max([c["branching"] for c in rec["covers"]] or [0]) if cert else "no")
    if cert and rec["pruned"] and rec["no_prune_verdict"] == "DECLINED":
        cells["M4"] = "yes: pruned " + ", ".join(f"{a}->{b}" for a, b in rec["pruned"]) + "; NO_PRUNE=DECLINED"
    elif cert and rec["pruned"]:
        cells["M4"] = "vacuous: pruned " + ", ".join(f"{a}->{b}" for a, b in rec["pruned"]) + f" but NO_PRUNE={rec['no_prune_verdict']}"
    else:
        cells["M4"] = "no (nothing pruned)" if cert else "no"
    h = rec["handoff"]
    if cert and not rec["rows_identical"] and "checked" in h and not h["vacuous"] and h["failing"] == "-" and h["passed"] == h["declared"]:
        cells["M5"] = f"yes: {h['passed']}/{h['declared']} handoffs unsat, rows differ"
    elif cert and not rec["rows_identical"]:
        cells["M5"] = f"NO: rows differ but handoff {h}"
    else:
        cells["M5"] = "no (rows identical; handoff vacuous)" if cert else "no"
    if cert and rec["cut_lines"] and rec["no_cut_verdict"] == "DECLINED":
        cells["M6"] = "yes: " + "; ".join(l.replace("[cut] ", "") for l in rec["cut_lines"]) + "; NO_CUT=DECLINED"
    elif cert and rec["cut_lines"]:
        cells["M6"] = "vacuous: cuts kept (" + "; ".join(l.replace("[cut] ", "") for l in rec["cut_lines"]) + f") but NO_CUT={rec['no_cut_verdict']}"
    else:
        cells["M6"] = "no (no cut kept)" if cert else "no"
    xatoms = [l.replace("[cut-x] ", "") for l in rec["cutx_lines"]]
    if cert and xatoms and rec["no_implied_verdict"] == "DECLINED":
        cells["M6+"] = "yes: " + "; ".join(xatoms) + "; NO_IMPLIED=DECLINED"
    elif cert and xatoms:
        cells["M6+"] = "vacuous: widened atoms kept (" + "; ".join(xatoms) + f") but NO_IMPLIED={rec['no_implied_verdict']}"
    else:
        cells["M6+"] = "no (no widened atom kept)" if cert else "no"
    latoms = [a for a in xatoms if "kind=linear-form" in a or "kind=derived-bound" in a]
    if cert and latoms and rec["no_linear_verdict"] == "DECLINED":
        cells["M6L"] = "yes: " + "; ".join(latoms) + "; NO_LINEAR=DECLINED"
    elif cert and latoms:
        cells["M6L"] = "vacuous: linear-form atoms kept (" + "; ".join(latoms) + f") but NO_LINEAR={rec['no_linear_verdict']}"
    else:
        cells["M6L"] = "no (no linear-form atom kept)" if cert else "no"
    cells["M7"] = f"{rec['scenario'] or 'UNTAGGED'}; dim {rec['dimL']}" + (f"+{rec['dimR'] - rec['dimL']}" if rec['dimR'] != rec['dimL'] else "") + f"; {rec['inv_shape']}" + ("; per-mode domains" if rec["per_mode_evolve"] else "")
    rec["cells"] = cells
    rec["exercised"] = [m for m in ("M1", "M2", "M3", "M4", "M5", "M6", "M6+", "M6L") if cells[m].startswith("yes")]
    return rec

# ----------------------------------------------------------------------------- output

def md_table(recs):
    lines = []
    lines.append("| benchmark | verdict (ms) | M1 λ≠1 | M2 multi-step | M3 branch | M4 prune | M5 mode-dep | M6 cut | M6+ widened cut | M6L linear-form chain | M7 scenario; dim; invariant; domains |")
    lines.append("|---|---|---|---|---|---|---|---|---|---|---|")
    for r in recs:
        c = r["cells"]
        def short(x):
            return x if len(x) < 70 else x[:67] + "..."
        lines.append(f"| `{r['name']}` | {r['verdict']} ({r['ms']}) | {short(c['M1'])} | {short(c['M2'])} | {short(c['M3'])} | {short(c['M4'])} | {short(c['M5'])} | {short(c['M6'])} | {short(c['M6+'])} | {short(c['M6L'])} | {c['M7']} |")
    return "\n".join(lines)

def md_totals(recs):
    tot = {m: [r["name"] for r in recs if m in r["exercised"]] for m in ("M1", "M2", "M3", "M4", "M5", "M6", "M6+", "M6L")}
    tot["per-mode domains"] = [r["name"] for r in recs if r["per_mode_evolve"]]
    lines = ["| mechanism | benchmarks (non-vacuous) | count |", "|---|---|---|"]
    for m, names in tot.items():
        lines.append(f"| {m} | {', '.join('`'+n+'`' for n in names)} | {len(names)} |")
    return "\n".join(lines)

def md_table1(recs):
    """Proposed Table-1 grouping: group, count, dim range, invariant forms, dynamics, discrete structure."""
    groups = {}
    for r in recs:
        groups.setdefault(r["family"], []).append(r)
    order = ["ACC under sensor spoofing / retune", "Quadrotor climb, lighter airframe", "Battery charger",
             "Platoon follower, delayed link", "Platoon string, three followers", "Rover patrol (zones)", "Arm, leading reference", "Rigid-body detumbling (polynomial)", "Heater cycle",
             "Terrain/position ladder", "Story ladders", "Watertank", "other"]
    lines = ["| group | count | dim (L/R) | invariant forms | dynamics | discrete structure (modes L/R; pruned fallbacks; mode-dep. rows; cuts; widened cuts; linear-form chains; per-mode domains) |",
             "|---|---|---|---|---|---|"]
    total = 0
    for g in order:
        rs = groups.get(g)
        if not rs:
            continue
        total += len(rs)
        dims = sorted(set((r["dimL"], r["dimR"]) for r in rs))
        dimtxt = ", ".join(f"{a}/{b}" if a != b else f"{a}" for a, b in dims)
        forms = sorted(set(r["inv_shape"] for r in rs))
        dyn = "polynomial" if all(r["nonlinear_L"] or r["nonlinear_R"] for r in rs) else ("affine" if not any(r["nonlinear_L"] or r["nonlinear_R"] for r in rs) else "affine + polynomial")
        mL = sorted(set(r["modesL"] for r in rs)); mR = sorted(set(r["modesR"] for r in rs))
        pr = sum(1 for r in rs if r["cells"]["M4"].startswith("yes"))
        md = sum(1 for r in rs if r["cells"]["M5"].startswith("yes"))
        cut = sum(1 for r in rs if r["cells"]["M6"].startswith("yes"))
        cutx = sum(1 for r in rs if r["cells"]["M6+"].startswith("yes"))
        cutl = sum(1 for r in rs if r["cells"]["M6L"].startswith("yes"))
        pmd = sum(1 for r in rs if r["per_mode_evolve"])
        struct = f"modes {min(mL)}-{max(mL)} / {min(mR)}-{max(mR)}; {pr} with a pruned fallback; {md} mode-dependent; {cut} cut-reliant; {cutx} widened-cut-reliant; {cutl} linear-form-reliant; {pmd} per-mode domains"
        lines.append(f"| {g} | {len(rs)} | {dimtxt} | {', '.join(forms)} | {dyn} | {struct} |")
    lines.append(f"| **total** | **{total}** | | | | |")
    return "\n".join(lines)

def md_timing(recs):
    lines = ["| benchmark | dim L/R | verdict | tool ms (relcert's own) | wall s (process) | Z3 queries | Z3 ms (sum) | Z3 max ms | UNSAT queries by shape |",
             "|---|---|---|---|---|---|---|---|---|"]
    tot_ms = tot_z3 = 0
    for r in recs:
        z = r.get("z3")
        tot_ms += r["ms"] or 0
        if z:
            tot_z3 += z["z3_ms"]
        lines.append(f"| `{r['name']}` | {r['dimL']}/{r['dimR']} | {r['verdict']} | {r['ms']} | {r.get('wall_s')} | "
                     + (f"{z['queries']} | {z['z3_ms']} | {z['z3_max_ms']} | " + ", ".join(f"{k} {v}" for k, v in z['unsat_shapes'].items()) + " |" if z else "- | - | - | - |"))
    lines.append(f"| **total** | | | **{tot_ms}** | | | **{tot_z3}** | | |")
    return "\n".join(lines)

def md_records(recs):
    out = []
    for r in recs:
        out.append(f"### `{r['name']}`\n")
        out.append(f"* family: {r['family']}; scenario: {r['scenario']}; dims L/R {r['dimL']}/{r['dimR']}; modes L/R {r['modesL']}/{r['modesR']}; εL/εR {r['epsL']}/{r['epsR']}; λ ∈ [{r['lambda_min']}, {r['lambda_max']}]; invariant shape {r['inv_shape']}; rows identical: {r['rows_identical']}; normalized md5 `{r['hash'][:12]}`")
        out.append(f"* `relcert`: **{r['verdict']}** ({r['ms']} ms); `{r['prune_line']}`; NO_PRUNE: **{r['no_prune_verdict']}** ({r['no_prune_ms']} ms); NO_CUT: **{r['no_cut_verdict']}** ({r['no_cut_ms']} ms); NO_IMPLIED_CUT: **{r['no_implied_verdict']}** ({r['no_implied_ms']} ms); NO_LINEAR_CUT: **{r['no_linear_verdict']}** ({r['no_linear_ms']} ms); domains: {'per-mode' if r['per_mode_evolve'] else 'uniform'}")
        for l in r["cut_lines"]:
            out.append(f"* `{l}`")
        for l in r["cutx_lines"]:
            out.append(f"* `{l}`")
        for l in r["admissible_lines"]:
            out.append(f"* `{l}`")
        h = r["handoff"]
        if "checked" in h:
            out.append(f"* `--handoff`: {h['checked']}/{h['declared']} checked, {h['passed']} passed, failing {h['failing']}, {'VACUOUS (identical rows)' if h['vacuous'] else 'non-vacuous'} ({h['ms']} ms)")
        else:
            out.append(f"* `--handoff`: {h.get('raw')}")
        for c in r["covers"]:
            out.append(f"* cover `{c['mL']}_L`: λ = {c['lam']}, budget {c['budget']}, admissible {c['admissible']}, flags {c['flags']}, kinds {c['kinds']}, path modes {c['modes_on_path']}, branching {c['branching']}, right-only {c['right_only']}")
            for s, p in c["paths"].items():
                out.append(f"    * from `{s}`: `{p}`")
        out.append("* cells: " + "; ".join(f"**{m}** {r['cells'][m]}" for m in ("M1", "M2", "M3", "M4", "M5", "M6", "M6+", "M6L")))
        out.append("")
    return "\n".join(out)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bench", default=os.path.join(ROOT, "benchmarks", "suite_v2"))
    ap.add_argument("--relcert", default=os.path.join(ROOT, ".lake", "build", "bin", "relcert"))
    ap.add_argument("--json", default=None)
    ap.add_argument("--md", default=None)
    ap.add_argument("--only", default=None)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--z3time", action="store_true", help="one extra proxied run per benchmark: Z3 time, query count, UNSAT queries by route shape")
    args = ap.parse_args()
    names = sorted(d for d in os.listdir(args.bench) if os.path.isfile(os.path.join(args.bench, d, "input.txt")))
    if args.only:
        keep = set(args.only.split(","))
        names = [n for n in names if n in keep]
    recs = []
    for n in names:
        path = os.path.join(args.bench, n, "input.txt")
        r = analyze(n, path, args.relcert, args.timeout, args.z3time)
        recs.append(r)
        print(f"{n}: {r['verdict']} ({r['ms']} ms) NO_PRUNE={r['no_prune_verdict']} NO_CUT={r['no_cut_verdict']} NO_IMPLIED_CUT={r['no_implied_verdict']} NO_LINEAR_CUT={r['no_linear_verdict']} domains={'per-mode' if r['per_mode_evolve'] else 'uniform'} exercised={r['exercised']}", flush=True)
    # duplicates
    byhash = {}
    for r in recs:
        byhash.setdefault(r["hash"], []).append(r["name"])
    dups = {h: v for h, v in byhash.items() if len(v) > 1}
    print("\nDUPLICATE CHECK:", "none" if not dups else dups)
    bytol = {}
    for r in recs:
        bytol.setdefault(r["tol_hash"], []).append(r["name"])
    toldups = {h: v for h, v in bytol.items() if len(v) > 1}
    print("TOLERANCE-ONLY VARIANT CHECK:", "none" if not toldups else toldups)
    for r in recs:
        r.pop("debug_stderr", None)
    if args.json:
        with open(args.json, "w") as f:
            json.dump({"records": recs, "duplicates": dups, "tolerance_variants": toldups}, f, indent=1, default=str)
    md = ["## Matrix\n", md_table(recs), "\n## Totals\n", md_totals(recs), "\n## Proposed Table-1 grouping\n", md_table1(recs), "\n## Duplicate check\n",
          ("no two benchmarks normalize to the same model" if not dups else f"DUPLICATES: {dups}")
          + "; " + ("no two benchmarks differ only in tolerance constants (rows' numerals masked)" if not toldups else f"TOLERANCE-ONLY VARIANTS: {toldups}"),
          "\n## Timing\n", md_timing(recs),
          "\n## Per-benchmark run records\n", md_records(recs)]
    if args.md:
        with open(args.md, "w") as f:
            f.write("\n".join(md) + "\n")
    else:
        print("\n".join(md))
    return 0

if __name__ == "__main__":
    sys.exit(main())
