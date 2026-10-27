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
                     (diagnostic S_lam1: the file with lambda_min = lambda_max = 1, right-only
                     segments still allowed, DECLINES)
  M multi-step cover some left mode's budget >= 2 and its replayed derivation takes a joint
                     step (matrix M2)
  R right-only       some cover's replayed derivation has a right-only segment AND
                     RELCERT_NO_REPO=1 DECLINES (diagnostic R_cover: on the path at all)
  B branching        a joint step on the path has >= 2 distinct non-self retained successors
                     (matrix M3)
  P pruning          an edge is pruned AND RELCERT_NO_PRUNE=1 DECLINES (matrix M4)
  D mode-dependent   the rows differ, the handoffs are non-vacuous and unsat (matrix M5), AND
                     every uniform row set built from the file's own rows DECLINES (each
                     distinct row placed on every left mode; diagnostic D_rows: matrix M5 alone)
  I mode fact        RELCERT_NO_CUT=1 DECLINES (matrix no_cut_verdict)
  X committed subset RELCERT_NO_CHOICE=1 DECLINES
"""
import argparse, json, os, re, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, HERE)
from suite_v2_matrix import parse_input, run, verdict_of  # noqa: E402

LETTERS = ["S", "M", "R", "B", "P", "D", "I", "X"]
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
        out.append(line)
    return "\n".join(out) + "\n"


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
            lam_ne1 = any(c.get("lam_float", 1.0) != 1.0 or c.get("lam_pairs") for c in r["covers"])
            ro = any(c.get("right_only") for c in r["covers"])
            cells = r["cells"]
            v = {k: runs[k].get(name, ("MISSING", 0))[0] for k in runs}
            lam1 = run_variant(a.relcert, variant_lambda1(text), tmp, name + "_lam1", a.timeout) if lam_ne1 else "-"
            uni = {}
            if cells["M5"].startswith("yes"):
                distinct = []
                for k in prob["row_order"]:
                    if prob["rows"][k] not in distinct:
                        distinct.append(prob["rows"][k])
                keys = {}
                for k in prob["row_order"]:
                    keys.setdefault(prob["rows"][k], []).append(k)
                for i, row in enumerate(distinct):
                    uni["/".join(keys[row])] = run_variant(a.relcert, variant_uniform(text, row), tmp, f"{name}_uni{i}", a.timeout)
            L = {
                "S": cert and v["sync"] == "DECLINED" and lam_ne1,
                "M": cells["M2"].startswith("yes"),
                "R": cert and ro and v["norepo"] == "DECLINED",
                "B": cells["M3"].startswith("yes"),
                "P": cells["M4"].startswith("yes"),
                "D": cells["M5"].startswith("yes") and bool(uni) and all(x == "DECLINED" for x in uni.values()),
                "I": cert and r["no_cut_verdict"] == "DECLINED",
                "X": cert and v["nochoice"] == "DECLINED",
            }
            diag = {
                "S_lam1": lam1 == "DECLINED", "lam1_verdict": lam1,
                "R_cover": ro, "D_rows": cells["M5"].startswith("yes"), "uniform_rows": uni,
                "P_noprune_declines": v["noprune"] == "DECLINED",
            }
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
            dl = [k for k, x in (("S_lam1", diag["S_lam1"]), ("R_cover", ro), ("D_rows", diag["D_rows"])) if x]
            table.append(f"| `{name}` | {r['family']} | {r['dimL']}/{r['dimR']} | {r['modesL']}/{r['modesR']} | {rec['inv']} | {letters or '--'} | {ctl[name][1]/1000:.1f} | {v['sync']} | {lam1} | {v['norepo']} | {', '.join(f'{k}:{x}' for k, x in uni.items()) or '-'} | {' '.join(dl) or '-'} |")
            print(f"{name}: {letters or '--'} (lam1={lam1}, norepo={v['norepo']}, uniform={uni})", flush=True)
    tot = {k: sum(1 for x in rows if x["letters"][k]) for k in LETTERS}
    json.dump({"rows": rows, "totals": tot}, open(f"{a.out}/letters.json", "w"), indent=1)
    json.dump([{k: x[k] for k in ("name", "family", "dimL", "dimR", "modesL", "modesR", "inv", "dyn", "mech", "ms")} for x in rows],
              open(f"{a.out}/suite_results.json", "w"), indent=1)
    with open(f"{a.out}/letters.md", "w") as f:
        f.write("| benchmark | family | dim L/R | modes L/R | inv | letters | time (s) | SYNC | lambda=1 file | NO_REPO | uniform rows | diagnostics |\n")
        f.write("|---|---|---|---|---|---|---|---|---|---|---|---|\n")
        f.write("\n".join(table) + "\n\n")
        f.write("Totals: " + ", ".join(f"{k} {tot[k]}" for k in LETTERS) + "\n")
    print("TOTALS " + " ".join(f"{k}={tot[k]}" for k in LETTERS))


if __name__ == "__main__":
    main()
