#!/usr/bin/env python3
"""(a) Every renamed benchmark input.txt (suite_v2 and refute_mutants) differs from its main
version only in lines that contain the old name (main side) and the new name (branch side),
and the branch file is exactly the rename map applied to the main file.
Usage: python3 check_a.py REPO"""
import os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rename_map as R
os.chdir(sys.argv[1])

def show(rev, path):
    return subprocess.run(["git", "show", f"{rev}:{path}"], capture_output=True, text=True, check=True).stdout

st = subprocess.run(["git", "diff", "-M", "--name-status", "main", "--", "benchmarks"],
                    capture_output=True, text=True, check=True).stdout.splitlines()
n = bad = 0; lines_changed = 0
for l in st:
    parts = l.split("\t")
    if not parts[0].startswith("R") or not parts[1].endswith("input.txt"):
        continue
    old, new = parts[1], parts[2]
    a = show("main", old); b = open(new).read()
    al, bl = a.split("\n"), b.split("\n")
    ok = len(al) == len(bl) and R.apply(a) == b
    for x, y in zip(al, bl):
        if x != y:
            lines_changed += 1
            if not (R.matches(x) and any(v in y for v in R.MAP.values())):
                ok = False
    n += 1
    if not ok:
        bad += 1; print("FAIL", old, "->", new)
print(f"(a) renamed input.txt files: {n}; changed lines: {lines_changed}; failures: {bad}")
