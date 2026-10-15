/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_rate` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py match_multi_rate`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Instances.WellFormed.MatchMultiRate
import RelCertifier.InstancesV2.BenchCovers.match_multi_rate
import RelCertifier.InstancesV2.BenchProgress.match_multi_rate

namespace RelCertifier.Bridge.MatchMultiRate

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.match_multi_rate_IRv2
abbrev cX := Oracle.match_multi_rate_cutsV2X
abbrev cov := match_multi_rate_coverV2
abbrev prog := Progress.match_multi_rate_coverV2_progress
abbrev ce := Choice.ChoiceEmitE.empty "match_multi_rate"

theorem struct_ok : structOK IR 2 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 2 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 2 cov ce = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = MatchMultiRateGuarded.GrPG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR MatchMultiRateGuarded.GrPG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR MatchMultiRateGuarded.GrPG = true := by decide +kernel

/-- The same modes in the generic automaton. -/
theorem modes_eq : ∀ q m', (grOf IR 2 (prunedOf cov)).modeAt q = some m' →
    ∃ m, MatchMultiRateGuarded.GrPG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, MatchMultiRateGuarded.GrPG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 2) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 2 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `MatchMultiRateGuarded.match_multi_rate_wellFormedR`. -/
theorem wellFormedR : WellFormedRIn (grOf IR 2 (prunedOf cov)) (guardR IR 2) reg (epsR IR) :=
  wellFormedR_transport (MatchMultiRateGuarded.match_multi_rate_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `match_multi_rate`** (window form): every verdict group of the benchmark `unsat`. -/
theorem match_multi_rate_bridge (hv : Verdicts IR 2 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 2 cX cov reg 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 (by decide) dt hdt

end RelCertifier.Bridge.MatchMultiRate
