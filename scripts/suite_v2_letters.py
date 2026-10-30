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
  S stretching       the certificate needs a stretch other than 1, a positive one or 0 (stutter:
                     the right waits while the left runs a joint segment; the opt-in key
                     `stutter = true`, docs/STUTTER.md; 2026-10-30 the former letter W is folded
                     into S, as lambda = 0 is a special case of stretching). Credited when
                     (positive) RELCERT_SYNC=1 DECLINES and some left mode's cover has a positive
                     lambda != 1; for a file whose cover also has a stutter pairing the file at
                     lambda_min = lambda_max = 1 WITH the key kept must DECLINE too (RELCERT_SYNC
                     drops the stretch-0 candidate, so its decline alone may be the stutter's), or
                     (stutter) some cover has a stretch-0 pairing and the file without the key
                     DECLINES (at the same values).
                     (diagnostic S_lam1: the file with lambda_min = lambda_max = 1 and no
                     stutter, right-only segments still allowed, DECLINES)
  M multi-step cover some left mode's budget >= 2 and its replayed derivation takes a joint
                     step (matrix M2, the cover shape; 2026-10-30 owner's decision: the shape rule
                     is the official M, the refinement that also required a right mode change on
                     the replayed path is reverted). Information only, not a letter: the file
                     under RELCERT_SINGLE_STEP=1 (every cover capped at budget 1, one right control
                     step per left window) is reported in letters.json (diagnostic single_step)
  R right-only       some cover's replayed derivation has a right-only segment AND
                     RELCERT_NO_REPO=1 DECLINES (diagnostic R_cover: on the path at all)
  B branching        a joint step on the path has >= 2 distinct non-self retained successors
                     (matrix M3)
  P pruning          an edge is pruned AND RELCERT_NO_PRUNE=1 DECLINES (matrix M4)
  D mode-dependent   the stated requirement differs per mode, so the claim needs mode-dependent
                     rows: the rows differ, the handoffs are non-vacuous and unsat (matrix M5),
                     AND every uniform row set built from the file's own rows that keeps every
                     stated requirement DECLINES (each distinct row placed on every left mode; a
                     uniform row keeps the requirement of a mode when it implies that mode's row,
                     checked by Z3 over the reals; when no single row implies all, the conjunction
                     of the distinct rows is the uniform candidate). A weaker uniform row that
                     drops a stated requirement may certify without removing D (owner's rule of
                     2026-10-27). Diagnostics: D_rows = matrix M5 alone; D_strict = every uniform
                     row set built from the file's own rows DECLINES (the rule before 2026-10-27)
  I mode fact        RELCERT_NO_CUT=1 DECLINES (matrix no_cut_verdict)
  X committed subset RELCERT_NO_CHOICE=1 DECLINES

USED and NEEDED (owner's decision, 2026-10-30, replacing the batch-11 screens). Table 1 marks a
mechanism USED (open circle) or NEEDED (filled circle); two plain notions, no further screens.
USED: the mechanism appears in the certificate the tool produced (the emitted cover and
certificate records, as replayed by `scripts/suite_v2_matrix.py`), on a CERTIFIED file:
  S  some pairing's stretch is not 1 (stretch 0 included)
  M  a multi-step cover (matrix M2: budget >= 2 and a joint step on the replayed path)
  R  a right-only node in some cover
  B  a joint step with >= 2 distinct non-self retained successors (matrix M3)
  P  a pruned edge (a non-connection certificate in the cover), any pruned edge
  D  mode-dependent rows: the invariant's rows differ per left mode
  I  a checked cut (mode-fact atom) kept in the certificate, on any mode
  X  a committed successor subset (the emitted choice record is non-empty)
NEEDED: the ablation rule above: with the mechanism switched off the tool DECLINES (S: SYNC and the
lambda = 1 file; R: RELCERT_NO_REPO; P: RELCERT_NO_PRUNE; I: RELCERT_NO_CUT; X: RELCERT_NO_CHOICE;
D: the uniform-row test). M and B have no switch-off and are read off the cover shape, so for them
needed = used. Every needed letter must be used; a violation is printed as `NEEDED-NOT-USED` and
stops the run.
"""
import argparse, json, os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, HERE)
from suite_v2_matrix import parse_input, run, verdict_of, parse_cover  # noqa: E402
from inv_smt import atoms_of, show  # noqa: E402

LETTERS = ["S", "M", "R", "B", "P", "D", "I", "X"]

# Table 1 groups (2026-10-30): the suite by APPLICATION AREA, in this order (short labels so the
# table fits one column: Automotive = automotive and rail, Process = process and thermal, Energy =
# power and energy, Water tank = the running example and its two-speed variant). Every suite_v2 benchmark
# is listed under exactly one area; a benchmark listed nowhere (or twice) stops the script, so a new
# benchmark cannot silently fall out of the table. The wind turbine (turbine_startup_gearratio) is
# under power and energy; the turbofan ground start (engine_start_highidle) under aerospace.
AREAS = [
    ("Automotive", ["acc_spoof_lag", "acc_spoof_limp", "acc_tune_lag", "acc_tune_limp",
                             "platoon_linkloss", "platoon_profiles", "train_ato_odometry"]),
    ("Rovers", ["rover_terrain_2to4", "rover_terrain_4to6", "rover_ladder_2to3", "rover_ladder_3to6",
                "rover_ladder_6to8", "rover_ladder_8to12"]),
    ("Aerospace", ["quad_light_lag", "quad_light_profiles", "sat_detumble_phases", "sat_detumble_weak",
                   "sat3w_detumble_phases", "flaps_slow_approach", "engine_start_highidle"]),
    ("Process", ["reactor_feed_wireless", "extruder_pe100_manualstart", "boiler_purge_vfd",
                             "autoclave_liquid_steambank", "tank_dos_3to1", "molding_pack_checkring",
                             "bottling_fill_strainer", "furnace_program_timebase"]),
    ("Energy", ["h2_refuel_ambientbias", "hydro_rejection_gatecal", "turbine_startup_gearratio"]),
    ("Medical", ["ventilator_vc_cuffleak", "syringe_relay_prearm"]),
    ("Infrastructure", ["rampmeter_poll_2to1", "canal_gate_notches", "elevator_start_discbrake",
                        "gantry_speed_zones", "antenna_track_kvretune"]),
    ("Water tank", ["watertank", "watertank_twospeed"]),
    ("Literature", ["lit_csf21_vehicle_bus", "lit_csf21_vehicle_thermo", "lit_csf25_salt_tank_hold",
                    "lit_drl_lane_control", "lit_freedm_meter", "lit_girard08_robot",
                    "lit_gpt10_boost_converter", "lit_lz21_vehicle_position", "lit_nahs25_engine_cooling",
                    "lit_nahs25_salt_tank"]),
]
AREA_OF = {}
for _area, _names in AREAS:
    for _n in _names:
        if _n in AREA_OF:
            sys.exit(f"AREAS: {_n} listed twice ({AREA_OF[_n]}, {_area})")
        AREA_OF[_n] = _area


def area_of(name):
    if name not in AREA_OF:
        sys.exit(f"AREAS: benchmark {name} has no application area; add it to AREAS")
    return AREA_OF[name]


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
        elif re.match(r"^\s*stutter\s*=", line):
            continue
        out.append(line)
    return "\n".join(out) + "\n"


def variant_lambda1_key(text):
    """The file at lambda_min = lambda_max = 1 with the `stutter` key kept (stretch 0 still a
    candidate): declines only if a positive stretch other than 1 is needed."""
    out = []
    for line in text.splitlines():
        if re.match(r"^\s*lambda_min\s*=", line):
            line = "lambda_min = 1.0"
        elif re.match(r"^\s*lambda_max\s*=", line):
            line = "lambda_max = 1.0"
        out.append(line)
    return "\n".join(out) + "\n"


def variant_nostutter(text):
    """The file without the opt-in `stutter` key."""
    return "\n".join(l for l in text.splitlines() if not re.match(r"^\s*stutter\s*=", l)) + "\n"


def stutter_pairs(c):
    """The cover's pairings at stretch 0 (the matrix keeps a pairing's stretch when it differs
    from the window's)."""
    return [m for m, x in c.get("lam_pairs", {}).items() if x == "0"]


def positive_stretch_ne1(c):
    """Some pairing of the cover runs at a positive stretch other than 1: a listed pairing
    stretch outside {0, 1}, or the window's stretch (when not 1) carried by a pairing that is
    not listed. A cover without stutter pairings keeps the pre-stutter rule exactly."""
    if not stutter_pairs(c):
        return c.get("lam_float", 1.0) != 1.0 or bool(c.get("lam_pairs"))
    listed = c.get("lam_pairs", {})
    return any(x not in ("0", "1") for x in listed.values()) or (
        c.get("lam_float", 1.0) != 1.0 and any(m not in listed for m in c.get("flags", {})))


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


def z3_bin():
    for p in (os.environ.get("RELCERT_Z3"), "/opt/homebrew/bin/z3", "/usr/local/bin/z3", "/usr/bin/z3",
              shutil.which("z3")):
        if p and os.path.exists(p):
            return p
    raise SystemExit("z3 not found (set RELCERT_Z3)")


def row_atoms(row):
    return [show(x) for x in atoms_of(row, None, [])]


def implies(stronger, weaker):
    """Z3 over the reals: every point satisfying row `stronger` satisfies row `weaker`."""
    a, b = row_atoms(stronger), row_atoms(weaker)
    syms = sorted(set(re.findall(r"\b[LR]_[A-Za-z0-9_]+\b", " ".join(a + b))))
    q = "".join(f"(declare-const {s} Real)\n" for s in syms)
    q += f"(assert (and true {' '.join(a)}))\n(assert (not (and true {' '.join(b)})))\n(check-sat)\n"
    r = subprocess.run([z3_bin(), "-in"], input=q, capture_output=True, text=True, timeout=60)
    out = r.stdout.strip()
    if out not in ("sat", "unsat"):
        raise SystemExit(f"implication check inconclusive ({out!r}): {stronger} => {weaker}")
    return out == "unsat"


def conj_row(rows):
    return "smt2:(and " + " ".join(x for r in rows for x in row_atoms(r)) + ")"


def run_variant(relcert, text, tmpdir, tag, timeout):
    p = os.path.join(tmpdir, f"{tag}.txt")
    with open(p, "w") as f:
        f.write(text)
    _, out, _, _ = run([relcert, p], {"RELCERT_IMPLIED_CUT": "1"}, timeout)
    return verdict_of(out)[0]


def emit_cover_text(relcert, path, timeout, extra=None):
    """The emitted cover literal (`--emit-cover`, RELCERT_IMPLIED_CUT=1), or None when the run
    does not certify."""
    env = {"RELCERT_IMPLIED_CUT": "1"}
    env.update(extra or {})
    rc, out, _, _ = run([relcert, "--emit-cover", path, "x"], env, timeout)
    return out if rc == 0 and "def x" in out else None


def cover_signature(text, rec):
    """The structural part of an emitted cover that a derivation consumes: the pruned edges, and per
    left mode its stretch, budget, per-pairing stretches, admissible starts and the flags of the
    right modes on its replayed path (from the control record `rec`). The strata orders (which
    list cut atoms) and the flags of pairings no path uses are left out."""
    pc = parse_cover(text) if text else None
    if pc is None:
        return None
    pruned, covers = pc
    onp = {c["mL"]: set(c.get("modes_on_path", [])) for c in rec["covers"]}
    sig = [tuple(sorted(map(tuple, pruned)))]
    for c in covers:
        on = onp.get(c["mL"], set())
        sig.append((c["mL"], str(c["lam"]), c["budget"], tuple(sorted((k, str(v)) for k, v in c["lam_pairs"].items())),
                    tuple(c["admissible"]),
                    tuple(sorted((f["name"], f["jointOK"], f["dynPre"], f["dynPost"]) for f in c["flags"] if f["name"] in on))))
    return sig


def used_letters(r, cert):
    """The mechanisms the certificate found USES (module docstring), from the matrix record."""
    covs = r["covers"]
    cells = r["cells"]
    cut_kept = any(int(m.group(1)) > 0 for line in r.get("cut_lines", [])
                   for m in [re.match(r"\[cut\] [LR]\.\w+: (\d+) conjunct", line)] if m)
    return {
        "S": cert and any(positive_stretch_ne1(c) or stutter_pairs(c) for c in covs),
        "M": cells["M2"].startswith("yes"),
        "R": cert and any(c.get("right_only") for c in covs),
        "B": cells["M3"].startswith("yes"),
        "P": cert and bool(r.get("pruned")),
        "D": cert and "rows differ" in cells["M5"],
        "I": cert and cut_kept,
        "X": cert and r.get("choice_entries", 0) > 0,
    }


def inv_kind(shape):
    return "quadratic" if "quadratic" in shape else "linear"


TEX_HDR = """% GENERATED by scripts/suite_v2_letters.py (run by scripts/paper_numbers.sh); do not edit.
% Mechanism cells: \\mechNeeded = needed (the file declines with the mechanism switched off; M and B
% by the cover shape), \\mechUsed = used by the certificate found but not needed, blank = not used.
% Define both in the paper's macro file, e.g.
%   \\newcommand{\\mechNeeded}{$\\bullet$}   % mechanism needed by the certificate
%   \\newcommand{\\mechUsed}{$\\circ$}       % mechanism used, not needed
% Dyn/Inv use \\dyntypeL, \\dyntypeP, \\invtypeLin, \\invtypeQuad (the paper's macros).
"""


def tex_name(n):
    return "\\texttt{" + n.replace("_", "\\_") + "}"


def rng(vals):
    lo, hi = min(vals), max(vals)
    return f"{lo}" if lo == hi else f"{lo}--{hi}"


def group_order(rows):
    """Groups: the application areas of AREAS, in that order (only areas with a row)."""
    present = {x["group"] for x in rows}
    return [a for a, _ in AREAS if a in present]


def level(x, k):
    return "\\mechNeeded" if x["needed"][k] else ("\\mechUsed" if x["used"][k] else "")


def write_tables(out, rows):
    """Table 1 (by group) and the appendix per-benchmark table, as LaTeX snippets
    (docs/paper-numbers/table1.tex, table_per_benchmark.tex): one column per mechanism letter."""
    dyn = {"linear": "$\\dyntypeL$", "polynomial": "$\\dyntypeP$"}
    inv = {"linear": "$\\invtypeLin$", "quadratic": "$\\invtypeQuad$"}
    def dimstr(x):
        return f"{x['dimL']}" if x["dimL"] == x["dimR"] else f"{x['dimL']}/{x['dimR']}"
    groups = group_order(rows)
    lines = [TEX_HDR, "% Table 1: the suite by group; a group's cell is the strongest level among its members",
             "% (needed > used > none); the last two rows: needed and used counts per letter over the suite.",
             "\\begin{tabular}{@{}l c c c c c " + " ".join("c" for _ in LETTERS) + "@{}}", "\\toprule",
             "Group & \\# & Sync & Dim & Modes & Dyn/Inv & " + " & ".join(LETTERS) + " \\\\", "\\midrule"]
    for g in groups:
        xs = [x for x in rows if x["group"] == g]
        dims = [x["dimL"] for x in xs] + [x["dimR"] for x in xs]
        modes = f"{rng([x['modesL'] for x in xs])}/{rng([x['modesR'] for x in xs])}"
        dy = ",".join(dyn[d] for d in ("linear", "polynomial") if any(x["dyn"] == d for x in xs))
        iv = ",".join(inv[i] for i in ("linear", "quadratic") if any(x["inv"] == i for x in xs))
        cells = []
        for k in LETTERS:
            cells.append("\\mechNeeded" if any(x["needed"][k] for x in xs) else
                         ("\\mechUsed" if any(x["used"][k] for x in xs) else ""))
        nsync = sum(1 for x in xs if x["sync"] == "CERTIFIED")
        lines.append(f"{g} & {len(xs)} & {nsync} & {rng(dims)} & {modes} & {dy}/{iv} & " + " & ".join(cells) + " \\\\")
    lines.append("\\midrule")
    totn = " & ".join(f"{sum(1 for x in rows if x['needed'][k])}" for k in LETTERS)
    totu = " & ".join(f"{sum(1 for x in rows if x['used'][k])}" for k in LETTERS)
    nsync = sum(1 for x in rows if x["sync"] == "CERTIFIED")
    lines.append(f"Total needed & {len(rows)} & {nsync} & & & & {totn} \\\\")
    lines.append(f"Total used & & & & & & {totu} \\\\")
    lines += ["\\bottomrule", "\\end{tabular}", ""]
    lines.append("% Group mapping (benchmark -> application area, AREAS in scripts/suite_v2_letters.py):")
    for g in groups:
        lines.append(f"%   {g}: " + ", ".join(x["name"] for x in rows if x["group"] == g))
    open(f"{out}/table1.tex", "w").write("\n".join(lines) + "\n")
    pl = [TEX_HDR, "% Appendix: the benchmarks individually, ordered by application area (area printed at its first row).",
          "\\begin{tabular}{@{}l l c c c " + " ".join("c" for _ in LETTERS) + " r@{}}", "\\toprule",
          "Benchmark & Group & Dim & Modes & Inv & " + " & ".join(LETTERS) + " & Time (s) \\\\", "\\midrule"]
    for g in groups:
        first = True
        for x in sorted((x for x in rows if x["group"] == g), key=lambda x: x["name"]):
            cells = " & ".join(level(x, k) for k in LETTERS)
            pl.append(f"{tex_name(x['name'])} & {g if first else ''} & {dimstr(x)} & {x['modesL']}/{x['modesR']} & "
                      f"{inv[x['inv']]} & {cells} & {x['ms']/1000:.1f} \\\\")
            first = False
    pl += ["\\bottomrule", "\\end{tabular}", ""]
    open(f"{out}/table_per_benchmark.tex", "w").write("\n".join(pl) + "\n")


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
              "RELCERT_MAX_QUERIES", "RELCERT_SINGLE_STEP"):
        os.environ.pop(k, None)
    ctl = verdicts(f"{a.out}/control.txt")
    runs = {k: verdicts(f"{a.out}/{k}.txt") for k in ("sync", "nochoice", "noprune", "norepo")}
    # information only (not a letter): the single-step ablation, when its run exists
    single = verdicts(f"{a.out}/singlestep.txt") if os.path.exists(f"{a.out}/singlestep.txt") else {}
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
            lam_ne1 = any(positive_stretch_ne1(c) for c in r["covers"])
            stut = any(stutter_pairs(c) for c in r["covers"])
            nostut = run_variant(a.relcert, variant_nostutter(text), tmp, name + "_nostutter", a.timeout) if stut else "-"
            ro = any(c.get("right_only") for c in r["covers"])
            cells = r["cells"]
            v = {k: runs[k].get(name, ("MISSING", 0))[0] for k in runs}
            lam1 = run_variant(a.relcert, variant_lambda1(text), tmp, name + "_lam1", a.timeout) if lam_ne1 else "-"
            lam1key = (run_variant(a.relcert, variant_lambda1_key(text), tmp, name + "_lam1key", a.timeout)
                       if lam_ne1 and stut else "-")
            uni, keeps, own = {}, {}, set()
            if cells["M5"].startswith("yes"):
                distinct = []
                for k in prob["row_order"]:
                    if prob["rows"][k] not in distinct:
                        distinct.append(prob["rows"][k])
                keys = {}
                for k in prob["row_order"]:
                    keys.setdefault(prob["rows"][k], []).append(k)
                for i, row in enumerate(distinct):
                    lab = "/".join(keys[row])
                    uni[lab] = run_variant(a.relcert, variant_uniform(text, row), tmp, f"{name}_uni{i}", a.timeout)
                    keeps[lab] = all(implies(row, other) for other in distinct)
                    own.add(lab)
                if not any(keeps.values()):
                    uni["conj"] = run_variant(a.relcert, variant_uniform(text, conj_row(distinct)), tmp, f"{name}_uniconj", a.timeout)
                    keeps["conj"] = True
            L = {
                "S": cert and ((v["sync"] == "DECLINED" and lam_ne1 and (not stut or lam1key == "DECLINED"))
                               or (stut and nostut == "DECLINED")),
                "M": cells["M2"].startswith("yes"),
                "R": cert and ro and v["norepo"] == "DECLINED",
                "B": cells["M3"].startswith("yes"),
                "P": cells["M4"].startswith("yes"),
                "D": cells["M5"].startswith("yes") and any(keeps.values())
                     and all(x == "DECLINED" for k, x in uni.items() if keeps[k]),
                "I": cert and r["no_cut_verdict"] == "DECLINED",
                "X": cert and v["nochoice"] == "DECLINED",
            }
            diag = {
                "S_lam1": lam1 == "DECLINED", "lam1_verdict": lam1,
                "R_cover": ro, "D_rows": cells["M5"].startswith("yes"), "uniform_rows": uni,
                "uniform_keeps_all": keeps,
                "D_strict": cells["M5"].startswith("yes") and bool(own) and all(uni[k] == "DECLINED" for k in own),
                "P_noprune_declines": v["noprune"] == "DECLINED",
                "single_step": single.get(name, ("-", 0))[0],
            }
            if stut:
                diag["S_nostutter_verdict"] = nostut
                diag["S_lam1key_verdict"] = lam1key
            U = used_letters(r, cert)
            bad = [k for k in LETTERS if L[k] and not U[k]]
            if bad:
                print(f"NEEDED-NOT-USED {name}: {' '.join(bad)}", flush=True)
                sys.exit(f"{name}: needed but not used: {bad}")
            letters = " ".join(k for k in LETTERS if L[k])
            uletters = " ".join((f"**{k}**" if L[k] else k) for k in LETTERS if U[k])
            unn = " ".join(k for k in LETTERS if U[k] and not L[k])
            rec = {"name": name, "family": r["family"], "dimL": r["dimL"], "dimR": r["dimR"],
                   "modesL": r["modesL"], "modesR": r["modesR"], "inv": inv_kind(r["inv_shape"]),
                   "inv_shape": r["inv_shape"], "dyn": "polynomial" if (r["nonlinear_L"] or r["nonlinear_R"]) else "linear",
                   "mech": letters, "ms": ctl[name][1], "verdict": ctl[name][0],
                   "sync": v["sync"], "nochoice": v["nochoice"], "noprune": v["noprune"], "norepo": v["norepo"],
                   "nocut": r["no_cut_verdict"], "noimplied": r["no_implied_verdict"], "nolinear": r["no_linear_verdict"],
                   "lambdas": {c["mL"]: c["lam"] for c in r["covers"]},
                   "letters": L, "needed": L, "used": U, "group": area_of(name),
                   "mech_used": " ".join(k for k in LETTERS if U[k]), "diagnostics": diag}
            rows.append(rec)
            dl = [k for k, x in (("S_lam1", diag["S_lam1"]), ("R_cover", ro), ("D_rows", diag["D_rows"]),
                                 ("D_strict", diag["D_strict"])) if x]
            unis = ", ".join(f"{k}:{x}" + ("" if keeps[k] else " (drops a stated row)") for k, x in uni.items())
            table.append(f"| `{name}` | {r['family']} | {r['dimL']}/{r['dimR']} | {r['modesL']}/{r['modesR']} | {rec['inv']} | {letters or '--'} | {uletters or '--'} | {unn or '-'} | {ctl[name][1]/1000:.1f} | {v['sync']} | {lam1} | {v['norepo']} | {diag['single_step']} | {unis or '-'} | {' '.join(dl) or '-'} |")
            print(f"{name}: {letters or '--'} used {rec['mech_used'] or '--'} (lam1={lam1}, norepo={v['norepo']}, uniform={uni}, keeps_all={keeps})", flush=True)
    tot = {k: sum(1 for x in rows if x["letters"][k]) for k in LETTERS}
    totu = {k: sum(1 for x in rows if x["used"][k]) for k in LETTERS}
    nstrict = sum(1 for x in rows if x["diagnostics"]["D_strict"])
    json.dump({"rows": rows, "totals": tot, "totals_needed": tot, "totals_used": totu},
              open(f"{a.out}/letters.json", "w"), indent=1)
    json.dump([{k: x[k] for k in ("name", "family", "dimL", "dimR", "modesL", "modesR", "inv", "dyn", "mech", "mech_used", "ms")} for x in rows],
              open(f"{a.out}/suite_results.json", "w"), indent=1)
    with open(f"{a.out}/letters.md", "w") as f:
        f.write("| benchmark | family | dim L/R | modes L/R | inv | needed | used (needed in bold) | used, not needed | time (s) | SYNC | lambda=1 file | NO_REPO | SINGLE_STEP (info) | uniform rows | diagnostics |\n")
        f.write("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|\n")
        f.write("\n".join(table) + "\n\n")
        f.write("Totals (needed, the `letters` field and `\\numletter<L>`): " + ", ".join(f"{k} {tot[k]}" for k in LETTERS) + "\n\n")
        f.write("Totals (used, `\\numletter<L>used`): " + ", ".join(f"{k} {totu[k]}" for k in LETTERS) + "\n\n")
        f.write("Used and needed (2026-10-30): see the docstring of scripts/suite_v2_letters.py. Needed = the "
                "ablation rule (with the mechanism switched off the tool declines; M and B by the cover shape, so needed = used). "
                "Used = the mechanism appears in the certificate the tool produced (S a stretch other than 1, 0 included; M a "
                "multi-step cover; R a right-only node; B a joint step with >= 2 retained successors; P any pruned edge; D rows "
                "that differ per left mode; I a checked cut kept in the certificate; X a committed successor subset). No other "
                "screens (owner's decision 2026-10-30, replacing the batch-11 screens).\n\n")
        f.write("D rule (2026-10-27): the stated requirement differs per mode, so the claim needs mode-dependent rows: "
                "matrix M5 and every uniform row set from the file's own rows that keeps every stated requirement declines; "
                "a uniform row marked (drops a stated row) may certify without removing D. "
                f"Under the earlier strict rule (every uniform row set declines, diagnostic D_strict) D = {nstrict}.\n")
    write_tables(a.out, rows)
    print("TOTALS " + " ".join(f"{k}={tot[k]}" for k in LETTERS) + f" (D_strict={nstrict})")
    print("TOTALS_USED " + " ".join(f"{k}={totu[k]}" for k in LETTERS))


if __name__ == "__main__":
    main()
