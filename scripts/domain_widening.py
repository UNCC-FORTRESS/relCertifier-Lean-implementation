#!/usr/bin/env python3
"""The domain-widening test: which evolve bounds is a certificate standing on?

User rule (docs/SUITE-REDESIGN.md section 13): an evolve domain states the PHYSICAL
limits of the plant; it must never be narrowed to a reachable-set estimate so that the
certificate closes. A bound that is load-bearing is therefore either a physical limit
the dynamics genuinely need, a forward-invariant floor the model justifies, or a
finding. This script makes the load-bearing bounds visible.

For every `benchmarks/suite_v2/<name>/input.txt` (or the files given):

  1. parse the evolve domains of both sides, mode by mode, into threshold bounds
     `v >= lo` / `v <= hi` (strict or not);
  2. for every GROUP (side, variable, direction) widen that bound in EVERY mode of the
     side by half the variable's range in that mode (hi - lo of the mode's own domain;
     a one-sided bound takes the range of the same variable's domain on the other side,
     and is reported as skipped if that is one-sided too), run `relcert` on the
     widened file and record the verdict — DECLINED or ERROR means the bound is
     LOAD-BEARING;
  3. widen ALL bounds at once and run again (the test the header of a repaired file
     claims to pass).

Every run sets RELCERT_IMPLIED_CUT=1 (the widened cut channel of the suite_v2 runs).
Runs are independent and are spread over a process pool (`--jobs`).

Output: one line per benchmark with the all-widened verdict and the load-bearing
groups; `--md` writes the table of docs/SUITE-REDESIGN.md section 13; `--json` the
raw records (every widened verdict, the widened amounts).

Usage:
  scripts/domain_widening.py [--bench DIR | FILE ...] [--relcert BIN] [--jobs N]
                             [--timeout SEC] [--md OUT.md] [--json OUT.json]
                             [--only name1,name2]
"""
import argparse, json, os, re, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))

BOUND_RE = re.compile(r"^\s*(\w+)\s*(<=|>=|<|>)\s*(-?\d+(?:\.\d+)?)\s*$")
VERDICT_RE = re.compile(r"^(\S+): (CERTIFIED|DECLINED|ERROR)(?: \((\d+)ms\))?", re.M)


def fmt(q):
    """Decimal text of a Fraction (exact when the denominator divides a power of ten)."""
    q = Fraction(q)
    for k in range(0, 30):
        if (10 ** k) % q.denominator == 0:
            m = q.numerator * (10 ** k // q.denominator)
            s = str(abs(m)).rjust(k + 1, "0")
            s = s[:-k] + "." + s[-k:] if k else s
            return ("-" if m < 0 else "") + s
    return repr(float(q))


class Bench:
    """The file as lines, with the evolve lines located per (side, mode)."""

    def __init__(self, path):
        self.path = path
        self.lines = open(path, encoding="utf-8").read().split("\n")
        self.evolve = {}   # (side, mode) -> line index
        side = mode = None
        for i, raw in enumerate(self.lines):
            s = raw.split("#", 1)[0].strip()
            m = re.match(r"\[(Lsys|Rsys)\.mode\.(\w+)\]$", s)
            if m:
                side, mode = ("L" if m.group(1) == "Lsys" else "R"), m.group(2)
                continue
            if re.match(r"\[.*\]$", s):
                side = mode = None
                continue
            if side and s.startswith("evolve") and "=" in s:
                self.evolve[(side, mode)] = i

    def conjuncts(self, idx):
        s = self.lines[idx].split("#", 1)[0]
        rhs = s.split("=", 1)[1]
        return [c.strip() for c in rhs.split(" and ")]

    def bounds(self):
        """{(side, mode): {var: {'lo': (op, value, k), 'hi': (op, value, k)}}} with k the
        conjunct index."""
        out = {}
        for key, idx in self.evolve.items():
            d = {}
            for k, c in enumerate(self.conjuncts(idx)):
                m = BOUND_RE.match(c)
                if not m:
                    continue
                v, op, val = m.group(1), m.group(2), Fraction(m.group(3))
                d.setdefault(v, {})
                if op in ("<=", "<"):
                    d[v]["hi"] = (op, val, k)
                else:
                    d[v]["lo"] = (op, val, k)
            out[key] = d
        return out

    def widened(self, edits):
        """A copy of the file with the given {(side, mode, k): new conjunct text}."""
        lines = list(self.lines)
        per_line = {}
        for (side, mode, k), text in edits.items():
            per_line.setdefault(self.evolve[(side, mode)], {})[k] = text
        for idx, ks in per_line.items():
            cs = self.conjuncts(idx)
            for k, text in ks.items():
                cs[k] = text
            key = self.lines[idx].split("=", 1)[0]
            lines[idx] = key + "= " + " and ".join(cs)
        return "\n".join(lines)


def run_relcert(relcert, text, name, timeout):
    with tempfile.TemporaryDirectory() as td:
        p = os.path.join(td, name, "input.txt")
        os.makedirs(os.path.dirname(p))
        open(p, "w").write(text)
        env = dict(os.environ)
        env["RELCERT_IMPLIED_CUT"] = "1"
        t0 = time.time()
        try:
            r = subprocess.run([relcert, p], capture_output=True, text=True, env=env, timeout=timeout, cwd=ROOT)
            out = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            return "TIMEOUT", time.time() - t0
        m = VERDICT_RE.search(out)
        return (m.group(2) if m else "UNKNOWN"), time.time() - t0


def plan(bench):
    """The widening groups: {(side, var, dir): {(side, mode, k): (old, new, delta)}}, plus
    the skipped one-sided bounds."""
    b = bench.bounds()
    groups, skipped = {}, []
    # the range of a variable on a side, per mode, and the fallback from the other side
    def rng(side, mode, v):
        d = b.get((side, mode), {}).get(v, {})
        if "lo" in d and "hi" in d:
            return d["hi"][1] - d["lo"][1]
        return None
    def other_rng(side, v):
        o = "R" if side == "L" else "L"
        for (s, m), d in b.items():
            if s == o and v in d and "lo" in d[v] and "hi" in d[v]:
                return d[v]["hi"][1] - d[v]["lo"][1]
        return None
    for (side, mode), d in b.items():
        for v, dd in d.items():
            for dr in ("lo", "hi"):
                if dr not in dd:
                    continue
                op, val, k = dd[dr]
                r = rng(side, mode, v)
                src = "own"
                if r is None:
                    r = other_rng(side, v)
                    src = "other side"
                if r is None or r <= 0:
                    skipped.append((side, mode, v, dr, "one-sided on both sides" if r is None else "empty range"))
                    continue
                delta = r / 2
                new = val - delta if dr == "lo" else val + delta
                groups.setdefault((side, v, dr), {})[(side, mode, k)] = (op, val, new, delta, src)
    return groups, skipped


def analyze(path, relcert, timeout, pool):
    name = os.path.basename(os.path.dirname(path))
    bench = Bench(path)
    groups, skipped = plan(bench)
    base_text = "\n".join(bench.lines)
    jobs = {}
    jobs["__base__"] = pool.submit(run_relcert, relcert, base_text, name, timeout)
    all_edits = {}
    for g, members in groups.items():
        edits = {}
        for (side, mode, k), (op, val, new, delta, src) in members.items():
            var = g[1]
            edits[(side, mode, k)] = f"{var} {op} {fmt(new)}"
        all_edits.update(edits)
        jobs[g] = pool.submit(run_relcert, relcert, bench.widened(edits), name, timeout)
    jobs["__all__"] = pool.submit(run_relcert, relcert, bench.widened(all_edits), name, timeout)
    rec = {"name": name, "path": os.path.relpath(path, ROOT), "groups": {}, "skipped": skipped}
    v, t = jobs["__base__"].result()
    rec["base"] = {"verdict": v, "s": round(t, 2)}
    v, t = jobs["__all__"].result()
    rec["all_widened"] = {"verdict": v, "s": round(t, 2)}
    rec["load_bearing"] = []
    for g, members in groups.items():
        v, t = jobs[g].result()
        side, var, dr = g
        key = f"{side}.{var}.{dr}"
        amounts = sorted(set(f"{fmt(val)}->{fmt(new)}" for (op, val, new, delta, src) in members.values()))
        rec["groups"][key] = {"verdict": v, "s": round(t, 2), "modes": len(members), "widened": amounts,
                              "source": sorted(set(src for (_, _, _, _, src) in members.values()))}
        if v != "CERTIFIED":
            rec["load_bearing"].append(key)
    rec["load_bearing"].sort()
    return rec


def md_table(recs):
    lines = ["| benchmark | base | all widened | load-bearing evolve bounds (widened by half the range: verdict) | skipped (one-sided) |",
             "|---|---|---|---|---|"]
    for r in recs:
        lb = "; ".join(f"`{k}` ({', '.join(r['groups'][k]['widened'])}: {r['groups'][k]['verdict']})" for k in r["load_bearing"]) or "none"
        sk = ", ".join(f"`{s}.{v}.{d}`" for (s, m, v, d, why) in r["skipped"]) or "none"
        lines.append(f"| `{r['name']}` | {r['base']['verdict']} | {r['all_widened']['verdict']} | {lb} | {sk} |")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="*")
    ap.add_argument("--bench", default=os.path.join(ROOT, "benchmarks", "suite_v2"))
    ap.add_argument("--relcert", default=os.path.join(ROOT, ".lake", "build", "bin", "relcert"))
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--only", default=None)
    ap.add_argument("--md", default=None)
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    if args.files:
        paths = [os.path.abspath(f) for f in args.files]
    else:
        names = sorted(d for d in os.listdir(args.bench) if os.path.isfile(os.path.join(args.bench, d, "input.txt")))
        if args.only:
            keep = set(args.only.split(","))
            names = [n for n in names if n in keep]
        paths = [os.path.join(args.bench, n, "input.txt") for n in names]
    recs = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for p in paths:
            r = analyze(p, args.relcert, args.timeout, pool)
            recs.append(r)
            print(f"{r['name']}: base={r['base']['verdict']} all-widened={r['all_widened']['verdict']} "
                  f"load-bearing={r['load_bearing'] or 'none'}"
                  + (f" skipped={[f'{s}.{v}.{d}' for (s, m, v, d, w) in r['skipped']]}" if r["skipped"] else ""), flush=True)
    if args.json:
        with open(args.json, "w") as f:
            json.dump(recs, f, indent=1, default=str)
    md = md_table(recs)
    if args.md:
        with open(args.md, "w") as f:
            f.write(md + "\n")
    else:
        print()
        print(md)
    return 0


if __name__ == "__main__":
    sys.exit(main())
