#!/usr/bin/env python3
"""The paper's Table 1 letters per benchmark, each credited only where the certificate needs it.

Called by scripts/paper_numbers.sh after its runs and the mechanism matrix:

  scripts/suite_v2_letters.py OUTDIR [--bench DIR] [--relcert BIN]

Reads OUTDIR/{control,sync,nochoice,noprune,norepo}.txt (one verdict line per benchmark) and
OUTDIR/matrix.json (scripts/suite_v2_matrix.py), runs two kinds of variant files of its own
(written to a temporary directory, never to the suite), and writes OUTDIR/letters.json,
OUTDIR/letters.md and OUTDIR/suite_results.json (the per-benchmark rows of the paper's
appendix table: name, family, dimensions, modes, invariant kind, letters, time).

Letters (the paper's legend), every one measured, never read off a header:
  S stretching       RELCERT_SYNC=1 DECLINES and some left mode's cover has lambda != 1
                     (a positive stretch: a stutter pairing, lambda = 0, does not count, see W)
                     (diagnostic S_lam1: the file with lambda_min = lambda_max = 1 and no
                     stutter, right-only segments still allowed, DECLINES)
                     For a file whose cover has a stutter pairing, S also needs the file at
                     lambda_min = lambda_max = 1 WITH the key kept to DECLINE (RELCERT_SYNC drops
                     the stretch-0 candidate, so its decline alone may be W's; 2026-10-30)
  M multi-step cover some left mode's budget >= 2 and its replayed derivation takes a joint
                     step (matrix M2)
  R right-only       some cover's replayed derivation has a right-only segment AND
                     RELCERT_NO_REPO=1 DECLINES (diagnostic R_cover: on the path at all)
  W witness waits    some cover has a stutter pairing (lambda = 0: the right waits while the left
                     runs a joint segment; the opt-in key `stutter = true`, docs/STUTTER.md) AND
                     the file without the key DECLINES (the dual of R, in which the left waits)
  B branching        a joint step on the path has >= 2 distinct non-self retained successors
                     (matrix M3)
  P pruning          an edge is pruned AND RELCERT_NO_PRUNE=1 DECLINES (matrix M4)
  D mode-dependent   the stated requirement differs per mode, so the claim needs mode-dependent
                     rows: the rows differ, the handoffs are non-vacuous and unsat (matrix M5),
                     AND every uniform row set built from the file's own rows that keeps every
                     stated requirement DECLINES (each distinct row placed on every left mode; a
                     uniform row keeps the requirement of a mode when it implies that mode's row,
                     checked by Z3 over the reals; when no single row implies all, the conjunction
                     of the distinct rows is the uniform candidate). A weaker uniform row that
                     drops a stated requirement may certify without removing D (owner's rule of
                     2026-10-27). Diagnostics: D_rows = matrix M5 alone; D_strict = every uniform
                     row set built from the file's own rows DECLINES (the rule before 2026-10-27)
  I mode fact        RELCERT_NO_CUT=1 DECLINES (matrix no_cut_verdict)
  X committed subset RELCERT_NO_CHOICE=1 DECLINES
"""
import argparse, json, os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, HERE)
from suite_v2_matrix import parse_input, run, verdict_of  # noqa: E402
from inv_smt import atoms_of, show  # noqa: E402

LETTERS = ["S", "M", "R", "W", "B", "P", "D", "I", "X"]
LINE_RE = re.compile(r"^([A-Za-z0-9_]+): (CERTIFIED|DECLINED|ERROR)(?: \[.*\])? \((\d+)ms\)")


def verdicts(path):
    d = {}
    for line in open(path):
        m = LINE_RE.match(line)
        if m:
            d[m.group(1)] = (m.group(2), int(m.group(3)))
    return d


def variant_lambda1(text):
    out = []
    for line in text.splitlines():
        if re.match(r"^\s*lambda_min\s*=", line):
            line = "lambda_min = 1.0"
        elif re.match(r"^\s*lambda_max\s*=", line):
            line = "lambda_max = 1.0"
        elif re.match(r"^\s*stutter\s*=", line):
            continue
        out.append(line)
    return "\n".join(out) + "\n"


def variant_lambda1_key(text):
    """The file at lambda_min = lambda_max = 1 with the `stutter` key kept (stretch 0 still a
    candidate): declines only if a positive stretch other than 1 is needed."""
    out = []
    for line in text.splitlines():
        if re.match(r"^\s*lambda_min\s*=", line):
            line = "lambda_min = 1.0"
        elif re.match(r"^\s*lambda_max\s*=", line):
            line = "lambda_max = 1.0"
        out.append(line)
    return "\n".join(out) + "\n"


def variant_nostutter(text):
    """The file without the opt-in `stutter` key."""
    return "\n".join(l for l in text.splitlines() if not re.match(r"^\s*stutter\s*=", l)) + "\n"


def stutter_pairs(c):
    """The cover's pairings at stretch 0 (the matrix keeps a pairing's stretch when it differs
    from the window's)."""
    return [m for m, x in c.get("lam_pairs", {}).items() if x == "0"]


def positive_stretch_ne1(c):
    """Some pairing of the cover runs at a positive stretch other than 1: a listed pairing
    stretch outside {0, 1}, or the window's stretch (when not 1) carried by a pairing that is
    not listed. A cover without stutter pairings keeps the pre-W rule exactly."""
    if not stutter_pairs(c):
        return c.get("lam_float", 1.0) != 1.0 or bool(c.get("lam_pairs"))
    listed = c.get("lam_pairs", {})
    return any(x not in ("0", "1") for x in listed.values()) or (
        c.get("lam_float", 1.0) != 1.0 and any(m not in listed for m in c.get("flags", {})))


def variant_uniform(text, row):
    """Every row of [relational_invariant] replaced by `row`."""
    out, inrel = [], False
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("[") and s.endswith("]"):
            inrel = s == "[relational_invariant]"
            out.append(line)
            continue
        if inrel and s and not s.startswith("#") and "=" in s:
            k = s.split("=", 1)[0].strip()
            out.append(f"{k} = {row}")
            continue
        out.append(line)
    return "\n".join(out) + "\n"


def z3_bin():
    for p in (os.environ.get("RELCERT_Z3"), "/opt/homebrew/bin/z3", "/usr/local/bin/z3", "/usr/bin/z3",
              shutil.which("z3")):
        if p and os.path.exists(p):
            return p
    raise SystemExit("z3 not found (set RELCERT_Z3)")


def row_atoms(row):
    return [show(x) for x in atoms_of(row, None, [])]


def implies(stronger, weaker):
    """Z3 over the reals: every point satisfying row `stronger` satisfies row `weaker`."""
    a, b = row_atoms(stronger), row_atoms(weaker)
    syms = sorted(set(re.findall(r"\b[LR]_[A-Za-z0-9_]+\b", " ".join(a + b))))
    q = "".join(f"(declare-const {s} Real)\n" for s in syms)
    q += f"(assert (and true {' '.join(a)}))\n(assert (not (and true {' '.join(b)})))\n(check-sat)\n"
    r = subprocess.run([z3_bin(), "-in"], input=q, capture_output=True, text=True, timeout=60)
    out = r.stdout.strip()
    if out not in ("sat", "unsat"):
        raise SystemExit(f"implication check inconclusive ({out!r}): {stronger} => {weaker}")
    return out == "unsat"


def conj_row(rows):
    return "smt2:(and " + " ".join(x for r in rows for x in row_atoms(r)) + ")"


def run_variant(relcert, text, tmpdir, tag, timeout):
    p = os.path.join(tmpdir, f"{tag}.txt")
    with open(p, "w") as f:
        f.write(text)
    _, out, _, _ = run([relcert, p], {"RELCERT_IMPLIED_CUT": "1"}, timeout)
    return verdict_of(out)[0]


def inv_kind(shape):
    return "quadratic" if "quadratic" in shape else "linear"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--bench", default=os.path.join(ROOT, "benchmarks", "suite_v2"))
    ap.add_argument("--relcert", default=os.path.join(ROOT, ".lake", "build", "bin", "relcert"))
    ap.add_argument("--timeout", type=int, default=600)
    a = ap.parse_args()
    for k in ("RELCERT_NO_PRUNE", "RELCERT_NO_CUT", "RELCERT_NO_IMPLIED_CUT", "RELCERT_NO_LINEAR_CUT",
              "RELCERT_NO_CHOICE", "RELCERT_SYNC", "RELCERT_NO_REPO", "RELCERT_NO_PAIR_STRETCH",
              "RELCERT_DEBUG", "RELCERT_LAMBDA_SCAN", "RELCERT_OPREGION", "RELCERT_TIME_BUDGET_MS",
              "RELCERT_MAX_QUERIES"):
        os.environ.pop(k, None)
    ctl = verdicts(f"{a.out}/control.txt")
    runs = {k: verdicts(f"{a.out}/{k}.txt") for k in ("sync", "nochoice", "noprune", "norepo")}
    recs = json.load(open(f"{a.out}/matrix.json"))["records"]
    recs = list(recs.values()) if isinstance(recs, dict) else recs
    byname = {r["name"]: r for r in recs}
    rows, table = [], []
    with tempfile.TemporaryDirectory() as tmp:
        for name in sorted(ctl):
            r = byname[name]
            path = os.path.join(a.bench, name, "input.txt")
            text = open(path).read()
            prob = parse_input(path)
            cert = ctl[name][0] == "CERTIFIED"
            lam_ne1 = any(positive_stretch_ne1(c) for c in r["covers"])
            stut = any(stutter_pairs(c) for c in r["covers"])
            nostut = run_variant(a.relcert, variant_nostutter(text), tmp, name + "_nostutter", a.timeout) if stut else "-"
            ro = any(c.get("right_only") for c in r["covers"])
            cells = r["cells"]
            v = {k: runs[k].get(name, ("MISSING", 0))[0] for k in runs}
            lam1 = run_variant(a.relcert, variant_lambda1(text), tmp, name + "_lam1", a.timeout) if lam_ne1 else "-"
            lam1key = (run_variant(a.relcert, variant_lambda1_key(text), tmp, name + "_lam1key", a.timeout)
                       if lam_ne1 and stut else "-")
            uni, keeps, own = {}, {}, set()
            if cells["M5"].startswith("yes"):
                distinct = []
                for k in prob["row_order"]:
                    if prob["rows"][k] not in distinct:
                        distinct.append(prob["rows"][k])
                keys = {}
                for k in prob["row_order"]:
                    keys.setdefault(prob["rows"][k], []).append(k)
                for i, row in enumerate(distinct):
                    lab = "/".join(keys[row])
                    uni[lab] = run_variant(a.relcert, variant_uniform(text, row), tmp, f"{name}_uni{i}", a.timeout)
                    keeps[lab] = all(implies(row, other) for other in distinct)
                    own.add(lab)
                if not any(keeps.values()):
                    uni["conj"] = run_variant(a.relcert, variant_uniform(text, conj_row(distinct)), tmp, f"{name}_uniconj", a.timeout)
                    keeps["conj"] = True
            L = {
                "S": cert and v["sync"] == "DECLINED" and lam_ne1 and (not stut or lam1key == "DECLINED"),
                "M": cells["M2"].startswith("yes"),
                "R": cert and ro and v["norepo"] == "DECLINED",
                "W": cert and stut and nostut == "DECLINED",
                "B": cells["M3"].startswith("yes"),
                "P": cells["M4"].startswith("yes"),
                "D": cells["M5"].startswith("yes") and any(keeps.values())
                     and all(x == "DECLINED" for k, x in uni.items() if keeps[k]),
                "I": cert and r["no_cut_verdict"] == "DECLINED",
                "X": cert and v["nochoice"] == "DECLINED",
            }
            diag = {
                "S_lam1": lam1 == "DECLINED", "lam1_verdict": lam1,
                "R_cover": ro, "D_rows": cells["M5"].startswith("yes"), "uniform_rows": uni,
                "uniform_keeps_all": keeps,
                "D_strict": cells["M5"].startswith("yes") and bool(own) and all(uni[k] == "DECLINED" for k in own),
                "P_noprune_declines": v["noprune"] == "DECLINED",
            }
            if stut:
                diag["W_nostutter_verdict"] = nostut
                diag["S_lam1key_verdict"] = lam1key
            letters = " ".join(k for k in LETTERS if L[k])
            rec = {"name": name, "family": r["family"], "dimL": r["dimL"], "dimR": r["dimR"],
                   "modesL": r["modesL"], "modesR": r["modesR"], "inv": inv_kind(r["inv_shape"]),
                   "inv_shape": r["inv_shape"], "dyn": "polynomial" if (r["nonlinear_L"] or r["nonlinear_R"]) else "linear",
                   "mech": letters, "ms": ctl[name][1], "verdict": ctl[name][0],
                   "sync": v["sync"], "nochoice": v["nochoice"], "noprune": v["noprune"], "norepo": v["norepo"],
                   "nocut": r["no_cut_verdict"], "noimplied": r["no_implied_verdict"], "nolinear": r["no_linear_verdict"],
                   "lambdas": {c["mL"]: c["lam"] for c in r["covers"]},
                   "letters": L, "diagnostics": diag}
            rows.append(rec)
            dl = [k for k, x in (("S_lam1", diag["S_lam1"]), ("R_cover", ro), ("D_rows", diag["D_rows"]),
                                 ("D_strict", diag["D_strict"])) if x]
            unis = ", ".join(f"{k}:{x}" + ("" if keeps[k] else " (drops a stated row)") for k, x in uni.items())
            table.append(f"| `{name}` | {r['family']} | {r['dimL']}/{r['dimR']} | {r['modesL']}/{r['modesR']} | {rec['inv']} | {letters or '--'} | {ctl[name][1]/1000:.1f} | {v['sync']} | {lam1} | {v['norepo']} | {unis or '-'} | {' '.join(dl) or '-'} |")
            print(f"{name}: {letters or '--'} (lam1={lam1}, norepo={v['norepo']}, uniform={uni}, keeps_all={keeps})", flush=True)
    tot = {k: sum(1 for x in rows if x["letters"][k]) for k in LETTERS}
    nstrict = sum(1 for x in rows if x["diagnostics"]["D_strict"])
    json.dump({"rows": rows, "totals": tot}, open(f"{a.out}/letters.json", "w"), indent=1)
    json.dump([{k: x[k] for k in ("name", "family", "dimL", "dimR", "modesL", "modesR", "inv", "dyn", "mech", "ms")} for x in rows],
              open(f"{a.out}/suite_results.json", "w"), indent=1)
    with open(f"{a.out}/letters.md", "w") as f:
        f.write("| benchmark | family | dim L/R | modes L/R | inv | letters | time (s) | SYNC | lambda=1 file | NO_REPO | uniform rows | diagnostics |\n")
        f.write("|---|---|---|---|---|---|---|---|---|---|---|---|\n")
        f.write("\n".join(table) + "\n\n")
        f.write("Totals: " + ", ".join(f"{k} {tot[k]}" for k in LETTERS) + "\n\n")
        f.write("D rule (2026-10-27): the stated requirement differs per mode, so the claim needs mode-dependent rows: "
                "matrix M5 and every uniform row set from the file's own rows that keeps every stated requirement declines; "
                "a uniform row marked (drops a stated row) may certify without removing D. "
                f"Under the earlier strict rule (every uniform row set declines, diagnostic D_strict) D = {nstrict}.\n")
    print("TOTALS " + " ".join(f"{k}={tot[k]}" for k in LETTERS) + f" (D_strict={nstrict})")


if __name__ == "__main__":
    main()
