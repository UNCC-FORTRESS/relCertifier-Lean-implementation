#!/usr/bin/env python3
"""Derive the pack rows of `RelCertifier/VerdictsV2/RunV2.lean` from the emitted leaves.

The rows are the packs the replay of the verified checker (`decideCovered` / `decideCoveredX`,
the matrix's `Replay` / `ReplayX`, `scripts/suite_v2_matrix.py`) consumes on a benchmark's
cover merged with its pre-landing record (`Emitted.withPL`), from every admissible start:

* a joint (modal) row `⟨b, dim, invRow, order, lamN, lamD, l, m⟩` per derivation node of kind
  base / joint / jointChosen (window `l`, right mode `m`, the pairing's strata order and stretch);
* a reposition row `⟨b, dim, invRow, order, pre, l, m, preland⟩` per derivation node of kind
  repoDyn / repoChosen (`pre` = before the window's first joint segment; the order of the
  pre-landing record for a pre-landing node, `preland = true`, else the cover's dynPre/dynPost
  order).

`dim` is the benchmark's Assumption 1 dimension (its first pack row's, else the state variables
padded to three: `bridgeDimV2`'s rule before its `+ 1`), `invRow` is the window's own row for a
benchmark with per-mode rows (`gen_bridge.KEYED`) and row 0 otherwise (its rows are identical,
`rowsSame`), the table's convention.

Usage:
  python3 scripts/gen_pack_rows.py --dyn             rewrite the whole `dynPacksV2` table
  python3 scripts/gen_pack_rows.py --joint b1,b2     rewrite the `packsV2` rows of b1, b2
  python3 scripts/gen_pack_rows.py --joint-swap o1,o2 n1,n2
                                                     replace the `packsV2` rows of o1, o2 (left
                                                     the suite) by the derived rows of n1, n2
  python3 scripts/gen_pack_rows.py --check           print, per benchmark, whether the derived
                                                     joint rows equal the table's (no write)
The rows are derived from InstancesV2/{BenchCovers,BenchPrelanding,BenchChoice}/<b>.lean; run
`scripts/gen_v2_data.py` first.
"""
import os, re, sys
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
os.chdir(ROOT)
sys.path.insert(0, "scripts")
import suite_v2_matrix as M
from gen_bridge import KEYED

SUITE = "benchmarks/suite_v2"
LEAF = "RelCertifier/InstancesV2"
RUNV2 = "RelCertifier/VerdictsV2/RunV2.lean"


def strata(text):
    out = {}
    for lm in re.finditer(r'⟨"(\w+)", \(([-\d]+) : ℚ\) / (\d+), (\d+), \[(.*?)\], \[(.*?)\], \[(.*?)\]⟩,?\s*$',
                          text, re.M):
        out[lm.group(1)] = {m.group(1): (eval(m.group(2)), eval(m.group(3)), eval(m.group(4)),
                                         int(m.group(5)), int(m.group(6)))
                            for m in re.finditer(r'⟨"(\w+)", (\[[^\]]*\]), (\[[^\]]*\]), (\[[^\]]*\]), (\d+), (\d+)⟩',
                                                 lm.group(7))}
    return out


def read(p):
    return open(p).read() if os.path.exists(p) else ""


def derive(b):
    """(joint rows, reposition rows) of suite benchmark `b` from its emitted leaves."""
    prob = M.parse_input(f"{SUITE}/{b}/input.txt")
    covtxt = read(f"{LEAF}/BenchCovers/{b}.lean")
    pltxt = read(f"{LEAF}/BenchPrelanding/{b}.lean")
    chtxt = read(f"{LEAF}/BenchChoice/{b}.lean")
    pruned, covers = M.parse_cover(covtxt)
    pl = M.parse_preland(pltxt)
    plorder = {(m.group(1), m.group(2), m.group(3) == "true"): eval(m.group(4))
               for m in re.finditer(r'⟨"(\w+)", "(\w+)", (true|false), (\[[^\]]*\])⟩',
                                    re.sub(r"\s*\n\s*", " ", pltxt))}
    M.merge_preland(covers, pl)
    entries = M.parse_choice(chtxt)
    st = strata(M.unwrap_cover(covtxt))   # Lean's line wrapping undone
    succ = {m: prob["R"]["modes"][m]["next"] for m in prob["R"]["order"]}
    Lord, Rord = prob["L"]["order"], prob["R"]["order"]
    joint, dyn = set(), set()

    def walk(d, l):
        if d is None:
            return
        if d["kind"] in ("base", "joint", "jointChosen"):
            joint.add((l, d["q"]))
        if d["kind"] in ("repoDyn", "repoChosen"):
            dyn.add((l, d["q"], d["sigma"] == "preJ"))
        for k in d.get("kids", []):
            walk(k, l)
    for c in covers:
        ents = [e for e in entries if e["mL"] == c["mL"]]
        rp = M.ReplayX(Rord, c["flags"], succ, pruned, ents) if ents else M.Replay(c["flags"], succ, pruned)
        fuel = c["budget"] * (rp.k + 1) + 1
        for start in c["admissible"]:
            d = rp.covered(fuel, rp.idx.get(start, rp.k), c["budget"], "preJ")
            if d is None:
                sys.exit(f"{b}: the replay does not cover {c['mL']} from {start}")
            walk(d, c["mL"])
    inv = lambda l: l if b in KEYED else 0
    rows = []
    for (mL, mR) in sorted(joint, key=lambda t: (Lord.index(t[0]), Rord.index(t[1]))):
        o, _, _, ln, ld = st[mL][mR]
        l = Lord.index(mL)
        rows.append(dict(l=l, m=Rord.index(mR), inv=inv(l), order=o, lamN=ln, lamD=ld))
    drows = []
    for (mL, mR, pre) in sorted(dyn, key=lambda t: (Lord.index(t[0]), Rord.index(t[1]), not t[2])):
        _, dpre, dpost, _, _ = st[mL][mR]
        key = (mL, mR, pre)
        l = Lord.index(mL)
        drows.append(dict(l=l, m=Rord.index(mR), inv=inv(l), pre=pre,
                          order=plorder.get(key, dpre if pre else dpost), preland=key in plorder))
    return rows, drows


def benches():
    return sorted(d for d in os.listdir(SUITE) if os.path.isfile(f"{SUITE}/{d}/input.txt"))


def table_dims(src):
    d = {}
    pk = src[src.index("def packsV2"):src.index("def expectedModalV2")]
    for m in re.finditer(r'⟨"(\w+)", (\d+), \d+, \[', pk):
        d.setdefault(m.group(1), int(m.group(2)))
    return d


def dim_of(b, dims):
    if b in dims:
        return dims[b]
    prob = M.parse_input(f"{SUITE}/{b}/input.txt")
    return max(len(prob["L"]["vars"]), 3)


def lst(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def joint_line(b, dim, r):
    return f'⟨"{b}", {dim}, {r["inv"]}, {lst(r["order"])}, {r["lamN"]}, {r["lamD"]}, {r["l"]}, {r["m"]}⟩'


def dyn_line(b, dim, r):
    return (f'⟨"{b}", {dim}, {r["inv"]}, {lst(r["order"])}, {"true" if r["pre"] else "false"}, '
            f'{r["l"]}, {r["m"]}, {"true" if r["preland"] else "false"}⟩')


def main():
    src = open(RUNV2).read()
    dims = table_dims(src)
    args = sys.argv[1:]
    if args == ["--dyn"]:
        out = []
        for b in benches():
            _, drows = derive(b)
            if drows:
                d = dim_of(b, dims)
                out.append(f"    -- {b}: the right-only nodes the replay consumes "
                           f"({sum(r['preland'] for r in drows)} of {len(drows)} pre-landing)")
                out += [f"    {dyn_line(b, d, r)}," for r in drows]
        if out:
            out[-1] = out[-1].rstrip(",")
        i = src.index("def dynPacksV2 : List DynPackV2 :=")
        j = src.index("/-- Declared: the number of component groups the reposition packs owe")
        body = ("def dynPacksV2 : List DynPackV2 :=\n  [\n" + "\n".join(out) + " ]\n\n")
        src = src[:i] + body + src[j:]
        open(RUNV2, "w").write(src)
        print(f"dynPacksV2: {sum(1 for x in out if x.lstrip().startswith('⟨'))} rows")
    elif len(args) == 2 and args[0] == "--joint":
        for b in args[1].split(","):
            rows, _ = derive(b)
            d = dim_of(b, dims)
            lines = src.split("\n")
            idx = [k for k, ln in enumerate(lines) if re.match(rf'\s*(\[ )?⟨"{b}", ', ln)
                   and k < src[:src.index("def expectedModalV2")].count("\n")]
            if not idx:
                sys.exit(f"{b}: no packsV2 rows to replace")
            first, last = idx[0], idx[-1]
            if idx != list(range(first, last + 1)):
                sys.exit(f"{b}: its packsV2 rows are not contiguous")
            lead = "  [ " if lines[first].lstrip().startswith("[ ") else "    "
            tail = " ]" if lines[last].rstrip().endswith("⟩ ]") else ","
            new = [("    " if k else lead) + joint_line(b, d, r) + ("," if k < len(rows) - 1 else tail)
                   for k, r in enumerate(rows)]
            lines[first:last + 1] = new
            src = "\n".join(lines)
            print(f"packsV2 {b}: {last - first + 1} -> {len(rows)} rows")
        open(RUNV2, "w").write(src)
    elif len(args) == 3 and args[0] == "--joint-swap":
        # replace the packsV2 rows (and their `-- b ...` comment lines) of the benchmarks that
        # left the suite by the derived rows of the benchmarks that took their place, at the
        # position of the first removed line (the new benchmarks have no rows yet, so `--joint`
        # cannot place them)
        olds, news = args[1].split(","), args[2].split(",")
        for b in news:
            if not os.path.isfile(f"{SUITE}/{b}/input.txt"):
                sys.exit(f"{b}: not a suite benchmark")
        for b in olds:
            if os.path.isfile(f"{SUITE}/{b}/input.txt"):
                sys.exit(f"{b}: still a suite benchmark")
        lines = src.split("\n")
        end = src[:src.index("def expectedModalV2")].count("\n")
        drop = [k for k, ln in enumerate(lines) if k < end and any(
            re.match(rf'\s*(\[ )?⟨"{b}", ', ln) or re.match(rf'\s*-- {b} ', ln) for b in olds)]
        if not drop:
            sys.exit(f"{olds}: no packsV2 rows to replace")
        first, last = drop[0], drop[-1]
        if drop != list(range(first, last + 1)):
            sys.exit(f"{olds}: their packsV2 rows are not contiguous")
        if lines[first].lstrip().startswith("[ ") or lines[last].rstrip().endswith("⟩ ]"):
            sys.exit(f"{olds}: the block is at an end of the table (not supported)")
        new = []
        for b in news:
            rows, _ = derive(b)
            d = dim_of(b, dims)
            new.append(f"    -- {b} (rows derived from the emitted cover: the joint pairings reached in each window)")
            new += [f"    {joint_line(b, d, r)}," for r in rows]
            print(f"packsV2 {b}: {len(rows)} rows")
        lines[first:last + 1] = new
        open(RUNV2, "w").write("\n".join(lines))
        print(f"packsV2: {last - first + 1} lines of {', '.join(olds)} replaced")
    elif args == ["--check"]:
        pk = src[src.index("def packsV2"):src.index("def expectedModalV2")]
        tab = {}
        for m in re.finditer(r'⟨"(\w+)", (\d+), (\d+), (\[[^\]]*\]), (\d+), (\d+), (\d+), (\d+)⟩', pk):
            tab.setdefault(m.group(1), set()).add(m.group(0))
        for b in benches():
            rows, _ = derive(b)
            der = {joint_line(b, dim_of(b, dims), r) for r in rows}
            t = tab.get(b, set())
            print(f"{b}: {'same' if der == t else 'DIFF'} (table {len(t)}, derived {len(der)})"
                  + ("" if der == t else f" only-table {sorted(t - der)[:3]} only-derived {sorted(der - t)[:3]}"))
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
