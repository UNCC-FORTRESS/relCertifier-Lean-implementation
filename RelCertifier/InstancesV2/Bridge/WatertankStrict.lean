/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_strict` (strict_demo) through the generic bridge at its strict rows (GENERATED —
`scripts/gen_strict_demo.py`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 2 and lifted to 3 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.StrictRun
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.Watertank
import RelCertifier.InstancesV2.Cuts.watertank_strict
import RelCertifier.InstancesV2.BenchCovers.watertank_strict
import RelCertifier.InstancesV2.BenchProgress.watertank_strict
import RelCertifier.InstancesV2.BenchChoice.watertank_strict

namespace RelCertifier.Bridge.WatertankStrict

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.watertank_strict_IRv2
abbrev cX := Oracle.watertank_strict_cutsV2X
abbrev cov := watertank_strict_coverV2
abbrev prog := Progress.watertank_strict_coverV2_progress
abbrev ce := Choice.watertank_strict_coverV2_choice

theorem struct_ok : structOK IR 3 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 3 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 3 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 2 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
theorem nR_eq : nR IR = V2Watertank.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2Watertank.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2Watertank.Gr = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 2 (prunedOf cov)).modeAt q = some m' →
    ∃ m, V2Watertank.Gr.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, V2Watertank.Gr_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 3) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 3 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `V2Watertank.watertank_wellFormedR` at dimension 2 and lifted to 3. -/
theorem wellFormedR : WellFormedRIn (grOf IR 3 (prunedOf cov)) (guardR IR 3) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 2) pad_ok
    (wellFormedR_transport (V2Watertank.watertank_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- The rows really carry a strict atom: the strictness mask of every window's row
(`x_L ≤ x_R + 3` closure, `x_R < x_L + 3.5` strict), decided in the kernel. -/
theorem masks : (List.range (nL IR)).map (maskOf IR 3) = [[false, true], [false, true], [false, true]] := by
  decide +kernel
theorem not_collapse : noStrictRows IR 3 = false := by decide +kernel

/-- **Theorem 3 of `watertank_strict` at its strict row** (window form): every strict verdict group of the
benchmark `unsat`. The claim carries the strict row (`windowClaimS`, `canonInvMS`). -/
theorem watertank_strict_bridge (hv : VerdictsS IR 3 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaimS IR 3 cX cov reg 0 1 2 dt :=
  theorem3_window_strict_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

/-- The same from a green strict run of the benchmark's groups (`bridgeGroupsS`). -/
theorem watertank_strict_bridge_run {gs : List (List (IForm 3))}
    (hrun : bridgeGroupsS IR 3 cX cov prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : windowClaimS IR 3 cX cov reg 0 1 2 dt :=
  theorem3_window_strict_of_run struct_ok hrun hok prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.WatertankStrict
