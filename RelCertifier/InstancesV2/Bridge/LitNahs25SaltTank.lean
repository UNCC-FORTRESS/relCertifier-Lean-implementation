/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_nahs25_salt_tank` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py lit_nahs25_salt_tank`)

The pre-landing certificate is on (`docs/PRELANDING.md`, always on since 2026-10-31; the IR
records it, `prelanding = true`): the cover's right-only
nodes are pre-landing nodes, recorded in the pre-landing record `pl`, never as the cover's
`dynPre`/`dynPost` flags. The kernel merges them (`withPL`) for the cover graph; each node's
reposition pack is on its region (`dynRegion`: before its progress certificate's last threshold,
strict components on the closure).

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel on the merged cover (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), the data
gate `pl_ok` (the IR records the feature, the whole-domain flags are off), Assumption 1 from the suite's
lemma at dimension 3 lifted to 4 (the right clock), the verdicts assumed (`Verdicts`: the
groups `relcert-bridge-verdicts` discharges on the merged cover, `Emitted.verdicts_of_groups`).
The claim is over the emitted cover `cov`.
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Run
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.LitNahs25SaltTank
import RelCertifier.InstancesV2.Cuts.lit_nahs25_salt_tank
import RelCertifier.InstancesV2.BenchCovers.lit_nahs25_salt_tank
import RelCertifier.InstancesV2.BenchProgress.lit_nahs25_salt_tank
import RelCertifier.InstancesV2.BenchChoice.lit_nahs25_salt_tank
import RelCertifier.InstancesV2.BenchPrelanding.lit_nahs25_salt_tank

namespace RelCertifier.Bridge.LitNahs25SaltTank

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.lit_nahs25_salt_tank_IRv2
abbrev cX := Oracle.lit_nahs25_salt_tank_cutsV2X
abbrev cov := lit_nahs25_salt_tank_coverV2
abbrev prog := Progress.lit_nahs25_salt_tank_coverV2_progress
abbrev ce := Choice.lit_nahs25_salt_tank_coverV2_choice
abbrev pl := Preland.lit_nahs25_salt_tank_coverV2_prelanding
/-- The cover graph's rows: the emitted cover with the pre-landing nodes merged in. -/
abbrev covM := withPL cov pl

/-- The data gate: the IR records the pre-landing feature and the emitted whole-domain flags are
all off. -/
theorem pl_ok : plOK IR cov pl = true := by decide +kernel
theorem struct_ok : structOK IR 4 covM cX = true := by decide +kernel
theorem prog_ok : progOK IR 4 covM prog = true := by decide +kernel
theorem covers_ok : coversOK IR 4 covM ce = true := by decide +kernel
theorem pad_ok : padOK IR 3 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
/-- Stretch 0 is admitted for this file: the run had the stutter feature on (`stutter = true`,
the default) and the declared stretch range includes `0` (`lambda_min = 0`; `Run.stutterAllowed`,
batch 13), and its cover really uses a stretch-0 pairing (decided in the kernel). -/
theorem stutter_on : RelCertifier.Run.stutterAllowed IR = true := by decide +kernel
theorem uses_stutter : (cov.covers.any fun lc => lc.strata.any (·.lamN == 0)) = true := by
  decide +kernel
/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 4) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 4 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, proved directly over the bridge's automaton at dimension 3
(`V2LitNahs25SaltTank.lit_nahs25_salt_tank_wellFormedR_direct`), lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (V2LitNahs25SaltTank.lit_nahs25_salt_tank_wellFormedR_direct (prunedOf cov))) reg

/-- The run had the pre-landing feature on, and its cover really uses pre-landing nodes (decided
in the kernel). -/
theorem prelanding_on : IR.prelanding = true := by decide +kernel
theorem uses_prelanding : pl.nodes.isEmpty = false := by decide +kernel

/-- **Theorem 3 of `lit_nahs25_salt_tank`** (window form, over the emitted cover): every verdict group of the
benchmark `unsat`. -/
theorem lit_nahs25_salt_tank_bridge (hv : Verdicts IR 4 cX covM prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 4 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records_pl pl_ok struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

/-- The same from a green run of the benchmark's groups (`bridgeGroups` on the merged cover,
`relcert-bridge-verdicts`). -/
theorem lit_nahs25_salt_tank_bridge_run {gs : List (List (IForm 4))}
    (hrun : bridgeGroups IR 4 cX covM prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : windowClaim IR 4 cX cov reg 0 1 2 dt :=
  lit_nahs25_salt_tank_bridge (verdicts_of_groups hrun hok) dt hdt

end RelCertifier.Bridge.LitNahs25SaltTank
