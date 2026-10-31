/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `molding_pack_checkring` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py molding_pack_checkring`)

The pre-landing certificate is on (`docs/PRELANDING.md`, always on since 2026-10-31; the IR
records it, `prelanding = true`): the cover's right-only
nodes are pre-landing nodes, recorded in the pre-landing record `pl`, never as the cover's
`dynPre`/`dynPost` flags. The kernel merges them (`withPL`) for the cover graph; each node's
reposition pack is on its region (`dynRegion`: before its progress certificate's last threshold,
strict components on the closure).

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel on the merged cover (`struct_ok`, `prog_ok`, `covers_ok`, `pad_ok`), the data
gate `pl_ok` (the IR records the feature, the whole-domain flags are off), Assumption 1 from the suite's
lemma at dimension 3 lifted to 4 (the right clock), the verdicts assumed (`Verdicts`: the
groups `relcert-bridge-verdicts` discharges on the merged cover, `Emitted.verdicts_of_groups`).
The claim is over the emitted cover `cov`.
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Run
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.MoldingPackCheckring
import RelCertifier.InstancesV2.Cuts.molding_pack_checkring
import RelCertifier.InstancesV2.BenchCovers.molding_pack_checkring
import RelCertifier.InstancesV2.BenchProgress.molding_pack_checkring
import RelCertifier.InstancesV2.BenchChoice.molding_pack_checkring
import RelCertifier.InstancesV2.BenchPrelanding.molding_pack_checkring

namespace RelCertifier.Bridge.MoldingPackCheckring

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.molding_pack_checkring_IRv2
abbrev cX := Oracle.molding_pack_checkring_cutsV2X
abbrev cov := molding_pack_checkring_coverV2
abbrev prog := Progress.molding_pack_checkring_coverV2_progress
abbrev ce := Choice.molding_pack_checkring_coverV2_choice
abbrev pl := Preland.molding_pack_checkring_coverV2_prelanding
/-- The cover graph's rows: the emitted cover with the pre-landing nodes merged in. -/
abbrev covM := withPL cov pl

/-- The data gate: the IR records the pre-landing feature and the emitted whole-domain flags are
all off. -/
theorem pl_ok : plOK IR cov pl = true := by decide +kernel
theorem struct_ok : structOK IR 4 covM cX = true := by decide +kernel
theorem prog_ok : progOK IR 4 covM prog = true := by decide +kernel
theorem covers_ok : coversOK IR 4 covM ce = true := by decide +kernel
theorem pad_ok : padOK IR 3 = true := by decide +kernel
theorem nR_eq : nR IR = V2MoldingPackCheckring.Gr.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2MoldingPackCheckring.Gr = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2MoldingPackCheckring.Gr = true := by decide +kernel

/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR 3 (prunedOf cov)).modeAt q = some m' →
    ∃ m, V2MoldingPackCheckring.Gr.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, V2MoldingPackCheckring.Gr_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 4) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 4 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `V2MoldingPackCheckring.molding_pack_checkring_wellFormedR` at dimension 3 and lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (wellFormedR_transport (V2MoldingPackCheckring.molding_pack_checkring_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg

/-- The run had the pre-landing feature on, and its cover really uses pre-landing nodes (decided
in the kernel). -/
theorem prelanding_on : IR.prelanding = true := by decide +kernel
theorem uses_prelanding : pl.nodes.isEmpty = false := by decide +kernel

/-- **Theorem 3 of `molding_pack_checkring`** (mode-keyed form, over the emitted cover): every verdict group of the
benchmark `unsat`. -/
theorem molding_pack_checkring_bridge (hv : Verdicts IR 4 cX covM prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 4 cX cov reg 0 1 2 3 dt :=
  theorem3_keyed_of_records_pl pl_ok struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) dt hdt

/-- The same from a green run of the benchmark's groups (`bridgeGroups` on the merged cover,
`relcert-bridge-verdicts`). -/
theorem molding_pack_checkring_bridge_run {gs : List (List (IForm 4))}
    (hrun : bridgeGroups IR 4 cX covM prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : keyedClaim IR 4 cX cov reg 0 1 2 3 dt :=
  molding_pack_checkring_bridge (verdicts_of_groups hrun hok) dt hdt

end RelCertifier.Bridge.MoldingPackCheckring
