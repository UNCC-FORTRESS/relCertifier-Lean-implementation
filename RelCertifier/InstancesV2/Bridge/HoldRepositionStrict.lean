/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hold_reposition_strict` (prelanding_demo) through the generic bridge (GENERATED —
`scripts/gen_prelanding_demo.py`)

With the opt-in key `prelanding = true` (`docs/PRELANDING.md`) the cover's right-only nodes are
pre-landing nodes, recorded in the pre-landing record `pl`, never as the cover's
`dynPre`/`dynPost` flags. The kernel merges them (`withPL`) for the cover graph; each node's
reposition pack is on its region (`dynRegion`: before its progress certificate's last threshold,
strict components on the closure).

Theorem 3 of the benchmark from its emitted records at its strict row (the strict chain): the structural bundles decided in the
kernel on the merged cover (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), the data
gate `pl_ok` (the key is set, the whole-domain flags are off), Assumption 1 from the demo's own
lemma at dimension 3 lifted to 4 (the right clock), the verdicts assumed (`VerdictsS`: the groups
`scripts/prelanding_demo_verdicts.lean` discharges, `Emitted.verdictsS_of_groups`). The claim is over the
emitted cover `cov`.
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.StrictRun
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.HoldRepositionStrict
import RelCertifier.InstancesV2.Cuts.hold_reposition_strict
import RelCertifier.InstancesV2.BenchCovers.hold_reposition_strict
import RelCertifier.InstancesV2.BenchProgress.hold_reposition_strict
import RelCertifier.InstancesV2.BenchChoice.hold_reposition_strict
import RelCertifier.InstancesV2.BenchPrelanding.hold_reposition_strict

namespace RelCertifier.Bridge.HoldRepositionStrict

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.hold_reposition_strict_IRv2
abbrev cX := Oracle.hold_reposition_strict_cutsV2X
abbrev cov := hold_reposition_strict_coverV2
abbrev prog := Progress.hold_reposition_strict_coverV2_progress
abbrev ce := Choice.hold_reposition_strict_coverV2_choice
abbrev pl := Preland.hold_reposition_strict_coverV2_prelanding
/-- The cover graph's rows: the emitted cover with the pre-landing nodes merged in. -/
abbrev covM := withPL cov pl

/-- The data gate: the key is set and the emitted whole-domain flags are all off. -/
theorem pl_ok : plOK IR cov pl = true := by decide +kernel
theorem struct_ok : structOK IR 4 covM cX = true := by decide +kernel
theorem prog_ok : progOK IR 4 covM prog = true := by decide +kernel
theorem covers_ok : coversOK IR 4 covM ce = true := by decide +kernel
theorem pad_ok : padOK IR 3 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 4) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 4 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, proved directly over the bridge's automaton at dimension 3
(`V2HoldRepositionStrict.hold_reposition_strict_wellFormedR_direct`), lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (V2HoldRepositionStrict.hold_reposition_strict_wellFormedR_direct (prunedOf cov))) reg

/-- The demo opts in, and its cover really uses pre-landing nodes (decided in the kernel). -/
theorem prelanding_on : IR.prelanding = true := by decide +kernel
theorem uses_prelanding : pl.nodes.isEmpty = false := by decide +kernel

/-- The row really carries a strict atom (`y_L < y_R + 5` strict, `y_R ≤ 0` closure), decided in
the kernel; the strict chain applies. -/
theorem masks : (List.range (nL IR)).map (maskOf IR 4) = [[true, false]] := by decide +kernel
theorem not_collapse : noStrictRows IR 4 = false := by decide +kernel

/-- **Theorem 3 of `hold_reposition_strict`** (window form, over the emitted cover): every verdict group of the
benchmark `unsat`. -/
theorem hold_reposition_strict_bridge (hv : VerdictsS IR 4 cX covM prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaimS IR 4 cX cov reg 0 1 2 dt :=
  theorem3_window_strict_of_records_pl pl_ok struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

/-- The same from a green run of the benchmark's groups (`bridgeGroupsS`,
`scripts/prelanding_demo_verdicts.lean`). -/
theorem hold_reposition_strict_bridge_run {gs : List (List (IForm 4))}
    (hrun : bridgeGroupsS IR 4 cX covM prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : windowClaimS IR 4 cX cov reg 0 1 2 dt :=
  hold_reposition_strict_bridge (verdictsS_of_groups hrun hok) dt hdt

end RelCertifier.Bridge.HoldRepositionStrict
