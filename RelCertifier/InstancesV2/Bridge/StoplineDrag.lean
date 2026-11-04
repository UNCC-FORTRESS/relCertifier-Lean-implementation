/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_drag` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py stopline_drag`)

The right-only flow certificates are checked on the restricted mode of Lemma 4
(`docs/PRELANDING.md`; the IR records it, `prelanding = true`): the cover's right-only
nodes are pre-landing nodes, recorded in the pre-landing record `pl`, never as the cover's
`dynPre`/`dynPost` flags. The kernel merges them (`withPL`) for the cover graph; each node's
right-only pack is on its region (`dynRegion`: before the landing target of its reposition
certificate, the closed half-space past the stage list's last threshold; strict components on
the closure).

Theorem 3 (Soundness of Synthesis) of the benchmark from its emitted records, through the
`_pl` record-level theorems of Appendix B.1: the structural bundles decided in the
kernel on the merged cover (`struct_ok`, `prog_ok`, `covers_ok`, `pad_ok`), the data
gate `pl_ok` (the IR records the feature, the whole-domain flags are off), Assumption 1 from the suite's
lemma at dimension 15 lifted to 16 (the right clock), the verdicts assumed (`Verdicts`: the
groups `relcert-bridge-verdicts` discharges on the merged cover, `Emitted.verdicts_of_groups`).
The claim is over the emitted cover `cov`.
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Run
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.StoplineDrag
import RelCertifier.InstancesV2.Cuts.stopline_drag
import RelCertifier.InstancesV2.BenchCovers.stopline_drag
import RelCertifier.InstancesV2.BenchProgress.stopline_drag
import RelCertifier.InstancesV2.BenchChoice.stopline_drag
import RelCertifier.InstancesV2.BenchPrelanding.stopline_drag

namespace RelCertifier.Bridge.StoplineDrag

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.stopline_drag_IRv2
abbrev cX := Oracle.stopline_drag_cutsV2X
abbrev cov := stopline_drag_coverV2
abbrev prog := Progress.stopline_drag_coverV2_progress
abbrev ce := Choice.stopline_drag_coverV2_choice
abbrev pl := Preland.stopline_drag_coverV2_prelanding
/-- The cover graph's rows: the emitted cover with the pre-landing nodes merged in. -/
abbrev covM := withPL cov pl

/-- The data gate: the IR records the pre-landing feature and the emitted whole-domain flags are
all off. -/
theorem pl_ok : plOK IR cov pl = true := by decide +kernel
theorem struct_ok : structOK IR 16 covM cX = true := by decide +kernel
theorem prog_ok : progOK IR 16 covM prog = true := by decide +kernel
theorem covers_ok : coversOK IR 16 covM ce = true := by decide +kernel
theorem pad_ok : padOK IR 15 = true := by decide +kernel
theorem nR_eq : nR IR = StoplineDrag.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR StoplineDrag.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR StoplineDrag.GrG = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 15 (prunedOf cov)).modeAt q = some m' →
    ∃ m, StoplineDrag.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, StoplineDrag.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 16) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 16 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `StoplineDrag.stopline_drag_wellFormedR` at dimension 15 and lifted to 16. -/
theorem wellFormedR : WellFormedRIn (grOf IR 16 (prunedOf cov)) (guardR IR 16) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 15) pad_ok
    (wellFormedR_transport (StoplineDrag.stopline_drag_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- The run checked right-only nodes on the restricted mode, and its cover really uses such
pre-landing nodes (decided in the kernel). -/
theorem prelanding_on : IR.prelanding = true := by decide +kernel
theorem uses_prelanding : pl.nodes.isEmpty = false := by decide +kernel

/-- **Theorem 3 of `stopline_drag`** (mode-keyed form, the invariant keyed by the stored left mode as in
Eq. (9), over the emitted cover): every verdict group of the benchmark `unsat`. -/
theorem stopline_drag_bridge (hv : Verdicts IR 16 cX covM prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 16 cX cov reg 0 1 2 3 dt :=
  theorem3_keyed_of_records_pl pl_ok struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) dt hdt

/-- The same from a green run of the benchmark's groups (`bridgeGroups` on the merged cover,
`relcert-bridge-verdicts`). -/
theorem stopline_drag_bridge_run {gs : List (List (IForm 16))}
    (hrun : bridgeGroups IR 16 cX covM prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : keyedClaim IR 16 cX cov reg 0 1 2 3 dt :=
  stopline_drag_bridge (verdicts_of_groups hrun hok) dt hdt

end RelCertifier.Bridge.StoplineDrag
