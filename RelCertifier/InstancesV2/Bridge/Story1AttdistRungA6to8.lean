/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_a_6to8` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py story1_attdist_rung_a_6to8`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 8 and lifted to 9 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.Story1AttdistRungA
import RelCertifier.InstancesV2.Cuts.story1_attdist_rung_a_6to8
import RelCertifier.InstancesV2.BenchCovers.story1_attdist_rung_a_6to8
import RelCertifier.InstancesV2.BenchProgress.story1_attdist_rung_a_6to8
import RelCertifier.InstancesV2.BenchChoice.story1_attdist_rung_a_6to8

namespace RelCertifier.Bridge.Story1AttdistRungA6to8

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.story1_attdist_rung_a_6to8_IRv2
abbrev cX := Oracle.story1_attdist_rung_a_6to8_cutsV2X
abbrev cov := story1_attdist_rung_a_6to8_coverV2
abbrev prog := Progress.story1_attdist_rung_a_6to8_coverV2_progress
abbrev ce := Choice.story1_attdist_rung_a_6to8_coverV2_choice

theorem struct_ok : structOK IR 9 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 9 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 9 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 8 = true := by decide +kernel
theorem nR_eq : nR IR = Story1AttdistRungAGuarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR Story1AttdistRungAGuarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR Story1AttdistRungAGuarded.GrG = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 8 (prunedOf cov)).modeAt q = some m' →
    ∃ m, Story1AttdistRungAGuarded.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, Story1AttdistRungAGuarded.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 9) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 9 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `Story1AttdistRungAGuarded.story1_attdist_rung_a_6to8_wellFormedR` at dimension 8 and lifted to 9. -/
theorem wellFormedR : WellFormedRIn (grOf IR 9 (prunedOf cov)) (guardR IR 9) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 8) pad_ok
    (wellFormedR_transport (Story1AttdistRungAGuarded.story1_attdist_rung_a_6to8_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- **Theorem 3 of `story1_attdist_rung_a_6to8`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem story1_attdist_rung_a_6to8_bridge (hv : Verdicts IR 9 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 9 cX cov reg 0 1 2 3 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.Story1AttdistRungA6to8
