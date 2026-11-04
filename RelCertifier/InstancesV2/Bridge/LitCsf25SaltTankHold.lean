/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_csf25_salt_tank_hold` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py lit_csf25_salt_tank_hold`)

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
lemma at dimension 3 lifted to 4 (the right clock), the verdicts assumed (`Verdicts`: the
groups `relcert-bridge-verdicts` discharges on the merged cover, `Emitted.verdicts_of_groups`).
The claim is over the emitted cover `cov`.
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Run
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.LitCsf25SaltTankHold
import RelCertifier.InstancesV2.Cuts.lit_csf25_salt_tank_hold
import RelCertifier.InstancesV2.BenchCovers.lit_csf25_salt_tank_hold
import RelCertifier.InstancesV2.BenchProgress.lit_csf25_salt_tank_hold
import RelCertifier.InstancesV2.BenchChoice.lit_csf25_salt_tank_hold
import RelCertifier.InstancesV2.BenchPrelanding.lit_csf25_salt_tank_hold

namespace RelCertifier.Bridge.LitCsf25SaltTankHold

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.lit_csf25_salt_tank_hold_IRv2
abbrev cX := Oracle.lit_csf25_salt_tank_hold_cutsV2X
abbrev cov := lit_csf25_salt_tank_hold_coverV2
abbrev prog := Progress.lit_csf25_salt_tank_hold_coverV2_progress
abbrev ce := Choice.lit_csf25_salt_tank_hold_coverV2_choice
abbrev pl := Preland.lit_csf25_salt_tank_hold_coverV2_prelanding
/-- The cover graph's rows: the emitted cover with the pre-landing nodes merged in. -/
abbrev covM := withPL cov pl

/-- The data gate: the IR records the pre-landing feature and the emitted whole-domain flags are
all off. -/
theorem pl_ok : plOK IR cov pl = true := by decide +kernel
theorem struct_ok : structOK IR 4 covM cX = true := by decide +kernel
theorem prog_ok : progOK IR 4 covM prog = true := by decide +kernel
theorem covers_ok : coversOK IR 4 covM ce = true := by decide +kernel
theorem pad_ok : padOK IR 3 = true := by decide +kernel
/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 4) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 4 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, proved directly over the bridge's automaton at dimension 3
(`V2LitCsf25SaltTankHold.lit_csf25_salt_tank_hold_wellFormedR_direct`), lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (V2LitCsf25SaltTankHold.lit_csf25_salt_tank_hold_wellFormedR_direct (prunedOf cov))) reg

/-- The run checked right-only nodes on the restricted mode, and its cover really uses such
pre-landing nodes (decided in the kernel). -/
theorem prelanding_on : IR.prelanding = true := by decide +kernel
theorem uses_prelanding : pl.nodes.isEmpty = false := by decide +kernel

/-- **Theorem 3 of `lit_csf25_salt_tank_hold`** (mode-keyed form, the invariant keyed by the stored left mode as in
Eq. (9), over the emitted cover): every verdict group of the benchmark `unsat`. -/
theorem lit_csf25_salt_tank_hold_bridge (hv : Verdicts IR 4 cX covM prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 4 cX cov reg 0 1 2 3 dt :=
  theorem3_keyed_of_records_pl pl_ok struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) dt hdt

/-- The same from a green run of the benchmark's groups (`bridgeGroups` on the merged cover,
`relcert-bridge-verdicts`). -/
theorem lit_csf25_salt_tank_hold_bridge_run {gs : List (List (IForm 4))}
    (hrun : bridgeGroups IR 4 cX covM prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : keyedClaim IR 4 cX cov reg 0 1 2 3 dt :=
  lit_csf25_salt_tank_hold_bridge (verdicts_of_groups hrun hok) dt hdt

end RelCertifier.Bridge.LitCsf25SaltTankHold
