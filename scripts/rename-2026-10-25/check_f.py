#!/usr/bin/env python3
"""(f) Compare two paper_numbers runs: numbers.tex (macro by macro) and matrix.json (record by
record, old name -> new name through the rename map). Timing fields are ignored:
ms, wall_s, every *_ms, and handoff.ms. name/path are compared after the map.
Writes the old -> new record mapping to OUTDIR/matrix_rename_map.tsv.
Usage: python3 check_f.py OLD_DIR NEW_DIR"""
import json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rename_map as R
old_dir, new_dir = sys.argv[1], sys.argv[2]

def macros(p):
    d, other = {}, []
    for l in open(p):
        m = re.match(r"\\newcommand\{\\(\w+)\}\{(.*)\}\s*$", l)
        if m:
            d[m.group(1)] = m.group(2)
        else:
            other.append(l.rstrip("\n"))
    return d, other

TIMING = {"totaltimes", "numunderonesec", "slowesttime"}
a, ao = macros(f"{old_dir}/numbers.tex"); b, bo = macros(f"{new_dir}/numbers.tex")
print("numbers.tex: macros old", len(a), "new", len(b))
for k in sorted(set(a) | set(b)):
    if a.get(k) != b.get(k):
        tag = "timing" if k in TIMING else ("removed" if k not in b else ("added" if k not in a else "VALUE"))
        print(f"  {tag}: {k}: {a.get(k)!r} -> {b.get(k)!r}")
for x, y in zip(ao, bo):
    if R.apply(x) != y:
        print(f"  line: {x!r} -> {y!r}")
if len(ao) != len(bo):
    print("  non-macro line counts differ", len(ao), len(bo))

def strip(x):
    if isinstance(x, dict):
        return {k: strip(v) for k, v in x.items()
                if not (k in ("ms", "wall_s") or k.endswith("_ms"))}
    if isinstance(x, list):
        return [strip(v) for v in x]
    if isinstance(x, str):
        return R.apply(x)
    return x

A = json.load(open(f"{old_dir}/matrix.json")); B = json.load(open(f"{new_dir}/matrix.json"))
ra = {r["name"]: r for r in A["records"]}; rb = {r["name"]: r for r in B["records"]}
print("matrix.json records: old", len(ra), "new", len(rb))
same = diff = 0
with open(f"{new_dir}/matrix_rename_map.tsv", "w") as fh:
    for n, r in sorted(ra.items()):
        m = R.apply(n)
        fh.write(f"{n}\t{m}\n")
        if m not in rb:
            print("  MISSING", n, "->", m); diff += 1; continue
        x, y = strip(r), strip(rb[m])
        if x == y:
            same += 1
        else:
            diff += 1
            ks = [k for k in set(x) | set(y) if x.get(k) != y.get(k)]
            print("  DIFF", n, "->", m, "fields:", ks)
print(f"  records identical up to name and timings: {same}; differing: {diff}")
print("  renamed records:", sum(1 for n in ra if R.apply(n) != n))
for k in ("duplicates", "tolerance_variants"):
    print(f"  {k}:", "identical up to names" if strip(A[k]) == strip(B[k]) else "DIFFER")
