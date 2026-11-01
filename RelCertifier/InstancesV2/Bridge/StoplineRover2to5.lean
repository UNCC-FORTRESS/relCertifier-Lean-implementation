/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_rover_2to5` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py stopline_rover_2to5`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 5 and lifted to 6 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.StoplineRover2to5
import RelCertifier.InstancesV2.Cuts.stopline_rover_2to5
import RelCertifier.InstancesV2.BenchCovers.stopline_rover_2to5
import RelCertifier.InstancesV2.BenchProgress.stopline_rover_2to5
import RelCertifier.InstancesV2.BenchChoice.stopline_rover_2to5

namespace RelCertifier.Bridge.StoplineRover2to5

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.stopline_rover_2to5_IRv2
abbrev cX := Oracle.stopline_rover_2to5_cutsV2X
abbrev cov := stopline_rover_2to5_coverV2
abbrev prog := Progress.stopline_rover_2to5_coverV2_progress
abbrev ce := Choice.stopline_rover_2to5_coverV2_choice

theorem struct_ok : structOK IR 6 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 6 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 6 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 5 = true := by decide +kernel
theorem nR_eq : nR IR = StoplineRover2to5.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR StoplineRover2to5.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR StoplineRover2to5.GrG = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 5 (prunedOf cov)).modeAt q = some m' →
    ∃ m, StoplineRover2to5.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, StoplineRover2to5.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 6) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 6 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `StoplineRover2to5.stopline_rover_2to5_wellFormedR` at dimension 5 and lifted to 6. -/
theorem wellFormedR : WellFormedRIn (grOf IR 6 (prunedOf cov)) (guardR IR 6) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 5) pad_ok
    (wellFormedR_transport (StoplineRover2to5.stopline_rover_2to5_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- **Theorem 3 of `stopline_rover_2to5`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem stopline_rover_2to5_bridge (hv : Verdicts IR 6 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 6 cX cov reg 0 1 2 3 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.StoplineRover2to5
