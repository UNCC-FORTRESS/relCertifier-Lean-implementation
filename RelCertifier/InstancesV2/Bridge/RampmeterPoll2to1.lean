/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rampmeter_poll_2to1` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py rampmeter_poll_2to1`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 3 and lifted to 4 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.RampmeterPoll2to1
import RelCertifier.InstancesV2.Cuts.rampmeter_poll_2to1
import RelCertifier.InstancesV2.BenchCovers.rampmeter_poll_2to1
import RelCertifier.InstancesV2.BenchProgress.rampmeter_poll_2to1
import RelCertifier.InstancesV2.BenchChoice.rampmeter_poll_2to1

namespace RelCertifier.Bridge.RampmeterPoll2to1

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.rampmeter_poll_2to1_IRv2
abbrev cX := Oracle.rampmeter_poll_2to1_cutsV2X
abbrev cov := rampmeter_poll_2to1_coverV2
abbrev prog := Progress.rampmeter_poll_2to1_coverV2_progress
abbrev ce := Choice.rampmeter_poll_2to1_coverV2_choice

theorem struct_ok : structOK IR 4 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 4 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 4 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 3 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = V2RampmeterPoll2to1.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2RampmeterPoll2to1.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2RampmeterPoll2to1.Gr = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 3 (prunedOf cov)).modeAt q = some m' →
    ∃ m, V2RampmeterPoll2to1.Gr.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, V2RampmeterPoll2to1.Gr_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 4) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 4 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `V2RampmeterPoll2to1.rampmeter_poll_2to1_wellFormedR` at dimension 3 and lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (wellFormedR_transport (V2RampmeterPoll2to1.rampmeter_poll_2to1_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- **Theorem 3 of `rampmeter_poll_2to1`** (window form): every verdict group of the benchmark `unsat`. -/
theorem rampmeter_poll_2to1_bridge (hv : Verdicts IR 4 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 4 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.RampmeterPoll2to1
