#!/usr/bin/env python3
"""(b) For every file changed against main (renames followed), apply the rename map to the
main version and compare with the branch version. Classes:
  exact    -- branch == map(main)
  reorder  -- same multiset of lines as map(main), different order (sorted aggregators)
  other    -- anything else (prints a short unified diff of map(main) vs branch)
Usage: python3 check_b.py REPO [--lean-only] [--diff]"""
import difflib, os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rename_map as R
os.chdir(sys.argv[1])
lean_only = "--lean-only" in sys.argv
show_diff = "--diff" in sys.argv

def git(*a):
    return subprocess.run(["git", *a], capture_output=True, text=True, check=True).stdout

main_files = [x for x in git("ls-tree", "-r", "--name-only", "main").split("\n") if x]
br_files = set(x for x in git("ls-files").split("\n") if x)
cls = {"exact": [], "reorder": [], "other": [], "added": [], "deleted": []}
pairs = []
changed = set(git("diff", "--name-only", "--no-renames", "main").split("\n")) - {""}
for old in main_files:
    new = R.apply(old)
    if new not in br_files:
        cls["deleted"].append(old); continue
    if old == new and old not in changed:
        continue
    pairs.append((old, new))
for x in sorted(br_files - set(R.apply(o) for o in main_files)):
    cls["added"].append(x)
for old, new in pairs:
    if lean_only and not new.endswith(".lean"):
        continue
    a = R.apply(git("show", f"main:{old}"))
    b = open(new).read()
    if a == b:
        cls["exact"].append(new)
    elif sorted(a.split("\n")) == sorted(b.split("\n")):
        cls["reorder"].append(new)
    else:
        cls["other"].append(new)
        if show_diff:
            d = list(difflib.unified_diff(a.split("\n"), b.split("\n"), "map(main)", "branch", n=0, lineterm=""))
            print(f"--- {new}: {len([x for x in d if x[:1] in '+-' and x[:3] not in ('+++','---')])} differing lines")
            for x in d[2:14]:
                print("   ", x[:180])
for k, v in cls.items():
    print(f"{k}: {len(v)}")
    if k != "exact":
        for f in v:
            print("   ", f)
