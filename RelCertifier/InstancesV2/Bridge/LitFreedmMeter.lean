/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_freedm_meter` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py lit_freedm_meter`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 3 and lifted to 4 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.LitFreedmMeter
import RelCertifier.InstancesV2.Cuts.lit_freedm_meter
import RelCertifier.InstancesV2.BenchCovers.lit_freedm_meter
import RelCertifier.InstancesV2.BenchProgress.lit_freedm_meter
import RelCertifier.InstancesV2.BenchChoice.lit_freedm_meter

namespace RelCertifier.Bridge.LitFreedmMeter

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.lit_freedm_meter_IRv2
abbrev cX := Oracle.lit_freedm_meter_cutsV2X
abbrev cov := lit_freedm_meter_coverV2
abbrev prog := Progress.lit_freedm_meter_coverV2_progress
abbrev ce := Choice.lit_freedm_meter_coverV2_choice

theorem struct_ok : structOK IR 4 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 4 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 4 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 3 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 4) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 4 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, proved directly over the bridge's automaton at dimension 3
(`V2LitFreedmMeter.lit_freedm_meter_wellFormedR_direct`), lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (V2LitFreedmMeter.lit_freedm_meter_wellFormedR_direct (prunedOf cov))) reg

/-- **Theorem 3 of `lit_freedm_meter`** (window form): every verdict group of the benchmark `unsat`. -/
theorem lit_freedm_meter_bridge (hv : Verdicts IR 4 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 4 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.LitFreedmMeter
