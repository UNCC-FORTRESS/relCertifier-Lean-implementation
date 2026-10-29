/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_csf25_salt_tank_hold` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py lit_csf25_salt_tank_hold`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 3 and lifted to 4 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.LitCsf25SaltTankHold
import RelCertifier.InstancesV2.Cuts.lit_csf25_salt_tank_hold
import RelCertifier.InstancesV2.BenchCovers.lit_csf25_salt_tank_hold
import RelCertifier.InstancesV2.BenchProgress.lit_csf25_salt_tank_hold
import RelCertifier.InstancesV2.BenchChoice.lit_csf25_salt_tank_hold

namespace RelCertifier.Bridge.LitCsf25SaltTankHold

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.lit_csf25_salt_tank_hold_IRv2
abbrev cX := Oracle.lit_csf25_salt_tank_hold_cutsV2X
abbrev cov := lit_csf25_salt_tank_hold_coverV2
abbrev prog := Progress.lit_csf25_salt_tank_hold_coverV2_progress
abbrev ce := Choice.lit_csf25_salt_tank_hold_coverV2_choice

theorem struct_ok : structOK IR 4 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 4 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 4 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 3 = true := by decide +kernel
/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 4) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 4 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, proved directly over the bridge's automaton at dimension 3
(`V2LitCsf25SaltTankHold.lit_csf25_salt_tank_hold_wellFormedR_direct`), lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (V2LitCsf25SaltTankHold.lit_csf25_salt_tank_hold_wellFormedR_direct (prunedOf cov))) reg

/-- **Theorem 3 of `lit_csf25_salt_tank_hold`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem lit_csf25_salt_tank_hold_bridge (hv : Verdicts IR 4 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 4 cX cov reg 0 1 2 3 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.LitCsf25SaltTankHold
