#!/usr/bin/env python3
"""Recreate the refutation finder's mutant scratch files (REFUTE_SCRATCH, default
/tmp/relcert-refute/<bench>/mNNN.txt) with the finder's own code (refute_finder.load_rows,
mutants, apply, write; the loop of its main), without any search. gen_refute.py copies these
into benchmarks/refute_mutants. Usage: python3 write_mutants.py REPO"""
import glob, os, sys
REPO = os.path.abspath(sys.argv[1])
sys.path.insert(0, os.path.join(REPO, "scripts"))
import refute_finder as F

n = 0
for p in sorted(glob.glob(os.path.join(REPO, "benchmarks/suite_v2/*/input.txt"))):
    bench = os.path.basename(os.path.dirname(p))
    text = open(p).read()
    b, rows = F.load_rows(text)
    muts = F.mutants(rows, b["L"]["vars"], b["R"]["vars"])
    d = os.path.join(F.SCRATCH, bench)
    os.makedirs(d, exist_ok=True)
    for i, (op, label, key, new) in enumerate(muts):
        open(os.path.join(d, f"m{i:03d}.txt"), "w").write(F.write(text, F.apply(rows, key, new)))
        n += 1
print(f"wrote {n} mutant files under {F.SCRATCH}")
