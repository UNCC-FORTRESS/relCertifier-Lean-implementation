#!/usr/bin/env python3
"""Apply rename_map to the repo: git mv every tracked path whose name carries an old key,
then rewrite every tracked text file except the dated historical docs.
Run from anywhere: python3 apply_rename.py REPO"""
import os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rename_map as R

REPO = sys.argv[1]
os.chdir(REPO)
DATED = {"docs/HANDOFF.md", "docs/GUARDED-SWITCHING.md", "docs/SUITE-DEDUPE.md",
         "docs/SUITE-REDESIGN.md", "docs/REFUTATION-RESULTS.md"}

files = subprocess.run(["git", "ls-files"], capture_output=True, text=True, check=True).stdout.split("\n")
files = [f for f in files if f]
moved = 0
for f in files:
    g = R.apply(f)
    if g != f:
        os.makedirs(os.path.dirname(g), exist_ok=True)
        subprocess.run(["git", "mv", f, g], check=True)
        moved += 1
files = subprocess.run(["git", "ls-files"], capture_output=True, text=True, check=True).stdout.split("\n")
files = [f for f in files if f]
changed = 0; occ = 0
for f in files:
    if f in DATED or f.endswith(".bib"):
        continue
    try:
        with open(f, encoding="utf-8") as h:
            s = h.read()
    except (UnicodeDecodeError, IsADirectoryError):
        continue
    n = len(R.matches(s))
    if n:
        with open(f, "w", encoding="utf-8") as h:
            h.write(R.apply(s))
        changed += 1; occ += n
print(f"moved {moved} paths; rewrote {changed} files, {occ} occurrences")
