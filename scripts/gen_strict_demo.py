#!/usr/bin/env python3
"""Emit the strict-atoms demo (benchmarks/strict_demo/watertank_strict) through the existing
generator path, without touching the suite_v2 aggregators.

* the data leaves (IR, cover, progress, choice, cuts) by `gen_v2_data.emit_leaves`, reading
  benchmarks/strict_demo instead of benchmarks/suite_v2 (the leaves land beside the suite's,
  named after the demo; no aggregator is rewritten, so the suite tables are unchanged);
* the generic-bridge instance by `gen_bridge.emit`, in the window form (the rows are the same
  in every left mode, as for the suite watertank), with the claim stated at the strict row:
  `VerdictsS` / `windowClaimS` / `theorem3_window_strict_of_records` (and the run form
  `theorem3_window_strict_of_run`), at the suite watertank's dimension 2. Assumption 1 is transported from the
  suite's `watertank` lemma: the demo's right model is the suite watertank's, checked in the
  kernel by the transport's `nR_eq`, `edges_ok`, `src_ok`.

Usage: python3 scripts/gen_strict_demo.py
Kernel check: lake build RelCertifier.InstancesV2.Bridge.WatertankStrict
Verdicts:     lake env lean scripts/strict_demo_verdicts.lean
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_v2_data as D
import gen_bridge as G

DEMO_DIR = "benchmarks/strict_demo"
B = "watertank_strict"
WF_FROM = "watertank"          # the suite benchmark with the same right model

D.SUITE = DEMO_DIR
G.SUITE = DEMO_DIR
D.HDR = D.HDR.replace("(suite_v2)", "(strict_demo)").replace(
    "Regenerate with `scripts/gen_v2_data.py {b}`.", "Regenerate with `scripts/gen_strict_demo.py`.")

_wf_info = G.wf_info
G.wf_info = lambda b: _wf_info(WF_FROM if b == B else b)

G.TEMPLATE = G.TEMPLATE.replace(
    "# `{b}` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py {b}`)",
    "# `{b}` (strict_demo) through the generic bridge at its strict rows (GENERATED —\n"
    "`scripts/gen_strict_demo.py`)").replace(
    "the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`\n"
    "discharges, `Emitted.verdicts_of_groups`).",
    "the verdicts assumed (`VerdictsS`: the strict groups `bridgeGroupsS`, read by\n"
    "`Emitted.verdictsS_of_groups`; a strict component's flow group is [route A, route B]).").replace(
    "import RelCertifier.Proofs.Encoding.Emitted.{form_mod}",
    "import RelCertifier.Proofs.Encoding.Emitted.StrictRun")

G.WINDOW_CLAIM = '''/-- The rows really carry a strict atom: the strictness mask of every window's row
(`x_L ≤ x_R + 3` closure, `x_R < x_L + 3.5` strict), decided in the kernel. -/
theorem masks : (List.range (nL IR)).map (maskOf IR {n}) = [[false, true], [false, true], [false, true]] := by
  decide +kernel
theorem not_collapse : noStrictRows IR {n} = false := by decide +kernel

/-- **Theorem 3 of `{b}` at its strict row** (window form): every strict verdict group of the
benchmark `unsat`. The claim carries the strict row (`windowClaimS`, `canonInvMS`). -/
theorem {b}_bridge (hv : VerdictsS IR {n} cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaimS IR {n} cX cov reg 0 1 2 dt :=
  theorem3_window_strict_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

/-- The same from a green strict run of the benchmark's groups (`bridgeGroupsS`). -/
theorem {b}_bridge_run {{gs : List (List (IForm {n}))}}
    (hrun : bridgeGroupsS IR {n} cX cov prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : windowClaimS IR {n} cX cov reg 0 1 2 dt :=
  theorem3_window_strict_of_run struct_ok hrun hok prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt
'''


def main():
    for d in ["BenchIR", "BenchCovers", "Cuts", "BenchProgress", "BenchChoice"]:
        os.makedirs(f"{D.OUT}/{d}", exist_ok=True)
    D.emit_leaves(B)
    print(f"  emitted leaves of {B}")
    n = 2          # the suite watertank's Assumption 1 dimension; the instance is emitted at n + 1 (the right clock)
    if not G.emit(B, n):
        sys.exit(f"{B}: bridge instance not emitted")
    # Assumption 1 is the suite watertank's lemma (the emitter names it after the benchmark)
    fn = f"{G.OUT}/{G.camel(B)}.lean"
    txt = open(fn).read().replace(f"{B}_wellFormedR", f"{WF_FROM}_wellFormedR")
    open(fn, "w").write(txt)
    print(f"  emitted RelCertifier/InstancesV2/Bridge/{G.camel(B)}.lean (dim {n + 1})")


if __name__ == "__main__":
    main()
