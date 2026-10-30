#!/usr/bin/env python3
"""Emit the stutter demo (benchmarks/stutter_demo/salt_tank_stutter, docs/STUTTER.md) through the
existing generator path, without touching the suite_v2 aggregators.

* the data leaves (IR, cover, progress, choice, cuts) by `gen_v2_data.emit_leaves`, reading
  benchmarks/stutter_demo instead of benchmarks/suite_v2 (the leaves land beside the suite's,
  named after the demo; no aggregator is rewritten, so the suite tables are unchanged); the IR
  carries `stutter := true` and the cover a stretch-0 pairing (`lamN = 0`);
* the generic-bridge instance by `gen_bridge.emit`, in the window form (the rows are the same in
  every left mode), at the suite salt tank's dimension 3 (+1, the right clock), with Theorem 3
  from the records (`Verdicts`) and from a green run of the groups (`bridgeGroups`). Assumption 1
  is transported from the suite's `lit_nahs25_salt_tank` lemma: the demo's right model is the
  suite file's, checked in the kernel by the transport's `nR_eq`, `edges_ok`, `src_ok`.

Usage: python3 scripts/gen_stutter_demo.py
Kernel check: lake build RelCertifier.InstancesV2.Bridge.SaltTankStutter
Verdicts:     lake env lean scripts/stutter_demo_verdicts.lean
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_v2_data as D
import gen_bridge as G

DEMO_DIR = "benchmarks/stutter_demo"
B = "salt_tank_stutter"
WF_FROM = "lit_nahs25_salt_tank"   # the suite benchmark with the same right model

D.SUITE = DEMO_DIR
G.SUITE = DEMO_DIR
D.HDR = D.HDR.replace("(suite_v2)", "(stutter_demo)").replace(
    "Regenerate with `scripts/gen_v2_data.py {b}`.", "Regenerate with `scripts/gen_stutter_demo.py`.")

_wf_info = G.wf_info
G.wf_info = lambda b: _wf_info(WF_FROM if b == B else b)

G.TEMPLATE = G.TEMPLATE.replace(
    "# `{b}` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py {b}`)",
    "# `{b}` (stutter_demo) through the generic bridge (GENERATED —\n"
    "`scripts/gen_stutter_demo.py`)\n\nThe attacked Off's pairing with the genuine On is a "
    "stretch-0 (stutter) segment: the\nrecord's `lamN = 0`, admitted by `timeOK` because the IR "
    "opts in (`stutter := true`).").replace(
    "import RelCertifier.Proofs.Encoding.Emitted.{form_mod}",
    "import RelCertifier.Proofs.Encoding.Emitted.{form_mod}\n"
    "import RelCertifier.Proofs.Encoding.Emitted.Run")

G.WINDOW_CLAIM = '''/-- The demo opts in, and its cover really uses a stretch-0 pairing (decided in the kernel). -/
theorem stutter_on : IR.stutter = true := by decide +kernel
theorem uses_stutter : (cov.covers.any fun lc => lc.strata.any (·.lamN == 0)) = true := by
  decide +kernel

/-- **Theorem 3 of `{b}`** (window form): every verdict group of the benchmark `unsat`. -/
theorem {b}_bridge (hv : Verdicts IR {n} cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR {n} cX cov reg 0 1 2 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

/-- The same from a green run of the benchmark's groups (`bridgeGroups`,
`scripts/stutter_demo_verdicts.lean`). -/
theorem {b}_bridge_run {{gs : List (List (IForm {n}))}}
    (hrun : bridgeGroups IR {n} cX cov prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : windowClaim IR {n} cX cov reg 0 1 2 dt :=
  {b}_bridge (verdicts_of_groups hrun hok) dt hdt
'''


def main():
    for d in ["BenchIR", "BenchCovers", "Cuts", "BenchProgress", "BenchChoice"]:
        os.makedirs(f"{D.OUT}/{d}", exist_ok=True)
    D.emit_leaves(B)
    fn = f"{D.OUT}/BenchIR/{B}.lean"
    txt = open(fn).read().replace(f"benchmarks/suite_v2/{B}/", f"{DEMO_DIR}/{B}/")
    open(fn, "w").write(txt)
    print(f"  emitted leaves of {B}")
    n = 3          # the suite salt tank's Assumption 1 dimension; the instance is emitted at n + 1
    if not G.emit(B, n):
        sys.exit(f"{B}: bridge instance not emitted")
    fn = f"{G.OUT}/{G.camel(B)}.lean"
    txt = open(fn).read().replace(f"{B}_wellFormedR", f"{WF_FROM}_wellFormedR")
    open(fn, "w").write(txt)
    print(f"  emitted RelCertifier/InstancesV2/Bridge/{G.camel(B)}.lean (dim {n + 1})")


if __name__ == "__main__":
    main()
