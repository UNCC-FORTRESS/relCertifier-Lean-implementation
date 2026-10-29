#!/usr/bin/env python3
"""One physical evolve domain per benchmark (owner's rule, 2026-10-29).

Every suite_v2 benchmark has ONE evolve domain, the same text on every mode of both sides (left
and right). A domain states physical constraints only (hardware limits, sensor ranges,
saturations, trips), never set points, asymptotes or reachable-set bands.

The one exception (kind iii): the two sides state the same physical limit in different
coordinates, e.g. the same trip setting applied to two differently scaled speed readings and
written in true-speed coordinates. Such a benchmark is listed in ALLOWED below with its
conversion, and the check then requires (a) exactly two distinct evolve lines, one shared by
every left mode and one shared by every right mode, and (b) a header line starting with
`# Domain conversion (kind iii):` that states the conversion.

Usage: scripts/check_one_domain.py [SUITE_DIR]   (default benchmarks/suite_v2)
Exit 0 and `ONE DOMAIN: PASS (...)` when every benchmark complies, else exit 1 with one line per
offending benchmark.
"""
import glob, os, re, sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
MARK = "# Domain conversion (kind iii):"
ALLOWED = {
    # benchmark: the conversion between the two sides' numbers (stated in the header too)
    "train_ato_odometry": "left 28.21 = 27.08 / 0.96 (the same ATP intervention speed on a tachometer reading 0.96 of true speed)",
    "turbine_startup_gearratio": "left 13.9755 = 1.05 x 13.31 (the same overspeed trip on a rotor-speed reading 1/1.05 of true speed)",
}


def domains(path):
    side, per = None, {"L": [], "R": []}
    for ln in open(path):
        m = re.match(r"^\[(Lsys|Rsys)(\.mode\.\w+)?\]", ln)
        if m:
            side = m.group(1)[0]
        elif ln.startswith("["):
            side = None
        if side and ln.startswith("evolve"):
            per[side].append(ln.split("=", 1)[1].strip())
    return per


def main():
    suite = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "benchmarks", "suite_v2")
    paths = sorted(glob.glob(os.path.join(suite, "*", "input.txt")))
    bad, one, conv = [], 0, 0
    for p in paths:
        b = os.path.basename(os.path.dirname(p))
        per = domains(p)
        lines = set(per["L"]) | set(per["R"])
        if not per["L"] or not per["R"]:
            bad.append(f"{b}: a side without an evolve line")
            continue
        if len(lines) == 1:
            one += 1
            continue
        if b in ALLOWED:
            hdr = [ln for ln in open(p) if ln.startswith(MARK)]
            if len(set(per["L"])) == 1 and len(set(per["R"])) == 1 and len(lines) == 2 and hdr:
                conv += 1
                continue
            why = "no header line '" + MARK + "'" if not hdr else "not one line per side"
            bad.append(f"{b}: kind (iii) exception, but {why}")
            continue
        bad.append(f"{b}: {len(lines)} distinct evolve lines (left {len(set(per['L']))}, right {len(set(per['R']))})")
    for b in ALLOWED:
        if not os.path.exists(os.path.join(suite, b, "input.txt")):
            bad.append(f"{b}: listed in ALLOWED but not in the suite")
    if bad:
        for x in bad:
            print("ONE DOMAIN: FAIL " + x)
        sys.exit(1)
    print(f"ONE DOMAIN: PASS ({len(paths)} benchmarks: {one} with one evolve domain, "
          f"{conv} kind (iii) with a stated conversion)")


if __name__ == "__main__":
    main()
