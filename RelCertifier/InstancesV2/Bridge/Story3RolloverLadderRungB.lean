/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_ladder_rung_b` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py story3_rollover_ladder_rung_b`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 12 and lifted to 13 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.Story3RolloverRungB
import RelCertifier.InstancesV2.Cuts.story3_rollover_ladder_rung_b
import RelCertifier.InstancesV2.BenchCovers.story3_rollover_ladder_rung_b
import RelCertifier.InstancesV2.BenchProgress.story3_rollover_ladder_rung_b
import RelCertifier.InstancesV2.BenchChoice.story3_rollover_ladder_rung_b

namespace RelCertifier.Bridge.Story3RolloverLadderRungB

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.story3_rollover_ladder_rung_b_IRv2
abbrev cX := Oracle.story3_rollover_ladder_rung_b_cutsV2X
abbrev cov := story3_rollover_ladder_rung_b_coverV2
abbrev prog := Progress.story3_rollover_ladder_rung_b_coverV2_progress
abbrev ce := Choice.story3_rollover_ladder_rung_b_coverV2_choice

theorem struct_ok : structOK IR 13 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 13 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 13 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 12 = true := by decide +kernel
theorem nR_eq : nR IR = V2Story3RolloverRungBGuarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2Story3RolloverRungBGuarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2Story3RolloverRungBGuarded.GrG = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 12 (prunedOf cov)).modeAt q = some m' →
    ∃ m, V2Story3RolloverRungBGuarded.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, V2Story3RolloverRungBGuarded.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 13) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 13 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `V2Story3RolloverRungBGuarded.story3_rollover_ladder_rung_b_wellFormedR` at dimension 12 and lifted to 13. -/
theorem wellFormedR : WellFormedRIn (grOf IR 13 (prunedOf cov)) (guardR IR 13) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 12) pad_ok
    (wellFormedR_transport (V2Story3RolloverRungBGuarded.story3_rollover_ladder_rung_b_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- **Theorem 3 of `story3_rollover_ladder_rung_b`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem story3_rollover_ladder_rung_b_bridge (hv : Verdicts IR 13 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 13 cX cov reg 0 1 2 3 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.Story3RolloverLadderRungB
