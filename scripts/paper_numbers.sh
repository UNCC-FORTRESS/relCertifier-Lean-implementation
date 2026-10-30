#!/bin/zsh
# One frozen run that produces every number the paper cites.
#   scripts/paper_numbers.sh OUTDIR
# Records the commit, Z3 version, OS and flags; emits every cover twice and requires them
# byte-identical; runs every configuration; runs the mechanism matrix; writes OUTDIR/numbers.tex.
# Letter macros (2026-10-30, batch 11; scripts/suite_v2_letters.py, docstring "USED and NEEDED"):
#   \numletter<L>      files whose certificate NEEDS mechanism <L> (the rule kept for continuity:
#                      the file declines with <L> switched off; M and B by the cover shape)
#   \numletter<L>used  files whose certificate USES <L> (the replayed derivation of the cover found)
#   <L> in S M R B P D I X; needed <= used for every letter.
# Table snippets (same script): OUTDIR/table1.tex (Table 1, by group, one column per letter,
# \mechNeeded / \mechUsed / blank, a needed/used totals row) and OUTDIR/table_per_benchmark.tex
# (the appendix table); the paper defines \mechNeeded and \mechUsed.
set -u
OUT=${1:?usage: paper_numbers.sh OUTDIR}
mkdir -p $OUT/covers1 $OUT/covers2
cd "$(dirname $0)/.."
lake build relcert > $OUT/build.log 2>&1 || { echo "build failed (see build.log)"; exit 1; }
B=./.lake/build/bin/relcert
S=(benchmarks/suite_v2/*/input.txt)
C=(benchmarks/choice/*/input.txt)
export RELCERT_IMPLIED_CUT=1
unset RELCERT_NO_PRUNE RELCERT_NO_CUT RELCERT_NO_IMPLIED_CUT RELCERT_NO_LINEAR_CUT \
      RELCERT_NO_CHOICE RELCERT_SYNC RELCERT_NO_PAIR_STRETCH RELCERT_DEBUG \
      RELCERT_LAMBDA_SCAN RELCERT_OPREGION RELCERT_TIME_BUDGET_MS RELCERT_MAX_QUERIES \
      RELCERT_NO_REPO RELCERT_NO_PROGRESS RELCERT_SINGLE_STEP

{
  echo "commit $(git rev-parse HEAD) $(git diff --quiet && echo clean || echo DIRTY)"
  echo "z3 $(z3 -version)"
  echo "os $(uname -srm)"
  echo "date $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "flags RELCERT_IMPLIED_CUT=1 (all runs); per-run switches in the run names"
} > $OUT/MANIFEST.txt

# 1. emitted covers, twice, must be byte-identical
for d in covers1 covers2; do
  for f in $S $C; do
    b=$(basename $(dirname $f))
    $B --emit-cover $f x > $OUT/$d/$b.lean 2>/dev/null
  done
done
if diff -r $OUT/covers1 $OUT/covers2 > $OUT/covers.diff; then
  echo "covers identical" >> $OUT/MANIFEST.txt
else
  echo "COVERS DIFFER (see covers.diff)" >> $OUT/MANIFEST.txt
fi

# 2. runs
run() { local name=$1; shift; env "$@" $B ${=FILES} > $OUT/$name.txt 2> $OUT/$name.err; }
FILES="$S"
run control
run nochoice RELCERT_NO_CHOICE=1
run sync RELCERT_SYNC=1
run sync_nochoice RELCERT_SYNC=1 RELCERT_NO_CHOICE=1
run noprune RELCERT_NO_PRUNE=1
run noprune_nochoice RELCERT_NO_PRUNE=1 RELCERT_NO_CHOICE=1
run norepo RELCERT_NO_REPO=1
run singlestep RELCERT_SINGLE_STEP=1   # information only: single-step covers (budget 1), not a letter
run opregion RELCERT_OPREGION=1
FILES="$C"
run exhibits_off RELCERT_NO_CHOICE=1
run exhibits_on
run exhibits_sync_on RELCERT_SYNC=1

# 3. mechanism matrix (its own counter-runs)
python3 scripts/suite_v2_matrix.py --json $OUT/matrix.json --md $OUT/matrix.md > $OUT/matrix.log 2>&1

# 3b. Table 1 letters per benchmark (counter-runs above + lambda = 1 and uniform-row variant
#     files), the per-benchmark rows of the appendix table (suite_results.json)
python3 scripts/suite_v2_letters.py $OUT > $OUT/letters.log 2>&1

# 4. numbers.tex
python3 - $OUT <<'EOF'
import json, re, sys, os
out = sys.argv[1]
def verdicts(name):
    d = {}
    for line in open(f"{out}/{name}.txt"):
        m = re.match(r"^([A-Za-z0-9_]+): (CERTIFIED|DECLINED|ERROR)(?: \[.*\])? \((\d+)ms\)", line)
        if m: d[m.group(1)] = (m.group(2), int(m.group(3)))
    return d
def count(d, v): return sum(1 for x in d.values() if x[0] == v)
ctl, syn = verdicts("control"), verdicts("sync")
recs = json.load(open(f"{out}/matrix.json"))["records"]
recs = list(recs.values()) if isinstance(recs, dict) else recs
byname = {r["name"]: r for r in recs}
def uses_stretch(b): return any(c.get("lam_float", 1.0) != 1.0 for c in byname[b]["covers"])
def uses_ro(b): return any(c.get("right_only") for c in byname[b]["covers"])
def uses_stutter(b): return any(x == "0" for c in byname[b]["covers"] for x in c.get("lam_pairs", {}).values())
syn_decl = [b for b, v in syn.items() if v[0] == "DECLINED"]
# stretch includes stretch 0 (stutter; SYNC drops that candidate too; 2026-10-30 letter W folded into S)
nst = sum(1 for b in syn_decl if uses_stretch(b) or uses_stutter(b))
cells = {k: sum(1 for r in recs if str(r["cells"].get(k, "")).startswith("yes")) for k in
         ["M1", "M2", "M3", "M4", "M5", "M6", "M6+", "M6L"]}
nro = sum(1 for r in recs if uses_ro(r["name"]))
ms = sorted((v[1], b) for b, v in ctl.items())
let = json.load(open(f"{out}/letters.json"))
def cert(r, k): return sum(1 for x in r if x.get(k) == "CERTIFIED")
opr = set()
for line in open(f"{out}/opregion.err"):
    m = re.search(r"\[opregion\] (\S+) \S+: starts OUTSIDE", line)
    if m: opr.add(m.group(1))
mac = {
 "numbenchmarks": len(ctl), "numcertified": count(ctl, "CERTIFIED"),
 "numsync": count(syn, "CERTIFIED"), "numsyncdeclined": len(syn_decl),
 "numsyncstretch": nst, "numsyncrightonly": len(syn_decl) - nst, "numrightonly": nro,
 "numnochoice": count(verdicts("nochoice"), "CERTIFIED"),
 "numnoprunedecl": count(verdicts("noprune"), "DECLINED"),
 "numnoprunenochoicedecl": count(verdicts("noprune_nochoice"), "DECLINED"),
 "numsyncnochoice": count(verdicts("sync_nochoice"), "CERTIFIED"),
 "numexhibits": len(verdicts("exhibits_on")),
 "numexhibitsoff": count(verdicts("exhibits_off"), "CERTIFIED"),
 "numexhibitson": count(verdicts("exhibits_on"), "CERTIFIED"),
 "numopregionout": len(opr),
 "nummechS": cells["M1"], "nummechM": cells["M2"], "nummechB": cells["M3"],
 "nummechP": cells["M4"], "nummechD": cells["M5"], "nummechc": cells["M6"],
 "nummechcplus": cells["M6+"], "nummechcL": cells["M6L"],
 "totaltimes": f"{sum(v[1] for v in ctl.values())/1000:.0f}",
 "numunderonesec": sum(1 for v in ctl.values() if v[1] < 1000),
 "slowesttime": f"{ms[-1][0]/1000:.0f}",
 "numlit": sum(1 for r in recs if r["family"] == "Literature"),
 "numnoprune": count(verdicts("noprune"), "CERTIFIED"),
 "numnoprunenochoice": count(verdicts("noprune_nochoice"), "CERTIFIED"),
 "numnorepo": count(verdicts("norepo"), "CERTIFIED"),
 "numnocut": cert(recs, "no_cut_verdict"),
 "numguardonly": cert(recs, "no_implied_verdict"),
 "numnolinear": cert(recs, "no_linear_verdict"),
 "numsinglestep": count(verdicts("singlestep"), "CERTIFIED"),
 **{f"numletter{k}": v for k, v in let["totals"].items()},
 **{f"numletter{k}used": v for k, v in let.get("totals_used", {}).items()},
}
# informational macros: measured and kept, not paper numbers
info = {"numnolinear": "informational, not a paper number: certified without decoupling forms (no benchmark needs one)",
        "numsinglestep": "informational, not a paper number: certified with single-step covers only (RELCERT_SINGLE_STEP=1)"}
with open(f"{out}/numbers.tex", "w") as f:
    f.write("% generated by scripts/paper_numbers.sh; see MANIFEST.txt\n")
    for k, v in mac.items():
        f.write(f"\\newcommand{{\\{k}}}{{{v}\\xspace}}" + (f" % {info[k]}" if k in info else "") + "\n")
    f.write(f"% slowest benchmark: {ms[-1][1]}\n")
print(open(f"{out}/numbers.tex").read())
EOF
cat $OUT/MANIFEST.txt
