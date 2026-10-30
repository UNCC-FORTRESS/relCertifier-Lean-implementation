/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `salt_tank_stutter` (stutter_demo) through the generic bridge (GENERATED —
`scripts/gen_stutter_demo.py`)

The attacked Off's pairing with the genuine On is a stretch-0 (stutter) segment: the
record's `lamN = 0`, admitted by `timeOK` because the IR opts in (`stutter := true`).

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 3 and lifted to 4 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Run
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.LitNahs25SaltTank
import RelCertifier.InstancesV2.Cuts.salt_tank_stutter
import RelCertifier.InstancesV2.BenchCovers.salt_tank_stutter
import RelCertifier.InstancesV2.BenchProgress.salt_tank_stutter
import RelCertifier.InstancesV2.BenchChoice.salt_tank_stutter

namespace RelCertifier.Bridge.SaltTankStutter

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.salt_tank_stutter_IRv2
abbrev cX := Oracle.salt_tank_stutter_cutsV2X
abbrev cov := salt_tank_stutter_coverV2
abbrev prog := Progress.salt_tank_stutter_coverV2_progress
abbrev ce := Choice.salt_tank_stutter_coverV2_choice

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
(`V2LitNahs25SaltTank.lit_nahs25_salt_tank_wellFormedR_direct`), lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (V2LitNahs25SaltTank.lit_nahs25_salt_tank_wellFormedR_direct (prunedOf cov))) reg

/-- The demo opts in, and its cover really uses a stretch-0 pairing (decided in the kernel). -/
theorem stutter_on : IR.stutter = true := by decide +kernel
theorem uses_stutter : (cov.covers.any fun lc => lc.strata.any (·.lamN == 0)) = true := by
  decide +kernel

/-- **Theorem 3 of `salt_tank_stutter`** (window form): every verdict group of the benchmark `unsat`. -/
theorem salt_tank_stutter_bridge (hv : Verdicts IR 4 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 4 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

/-- The same from a green run of the benchmark's groups (`bridgeGroups`,
`scripts/stutter_demo_verdicts.lean`). -/
theorem salt_tank_stutter_bridge_run {gs : List (List (IForm 4))}
    (hrun : bridgeGroups IR 4 cX cov prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : windowClaim IR 4 cX cov reg 0 1 2 dt :=
  salt_tank_stutter_bridge (verdicts_of_groups hrun hok) dt hdt

end RelCertifier.Bridge.SaltTankStutter
