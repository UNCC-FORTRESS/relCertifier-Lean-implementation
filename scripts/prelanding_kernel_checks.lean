/- Pre-landing kernel checks (docs/PRELANDING.md). Run:
`lake env lean scripts/prelanding_kernel_checks.lean` (after
`lake build RelCertifier.InstancesV2.Bridge.EngineCoolingPrelanding
RelCertifier.InstancesV2.Bridge.HoldRepositionStrict`).
* the axioms of Theorem 3 of both demos (from the records and from a green run), of the first-hit
  closers and of the region anchor lemmas: expected `[propext, Classical.choice, Quot.sound]` for
  the generic progress lemmas and the same plus `RelCertifier.z3_unsat_sound` for the rest;
* kernel facts: the strict demo's reposition node is on the pre-landing region with its strict
  component (index 0 of the node's order) marked for the closed region; without the key the
  same node's region is the whole domain (`dynRegionI = none`, the existing queries);
* kernel negatives: the data gate `plOK` rejects each record when the IR has the key off
  (`prelanding := false`); each emitted cover WITHOUT the pre-landing nodes merged fails
  `coversOK` (the nodes are needed). A green run prints only the axiom lines. -/
import RelCertifier.InstancesV2.Bridge.EngineCoolingPrelanding
import RelCertifier.InstancesV2.Bridge.HoldRepositionStrict
#print axioms RelCertifier.Bridge.EngineCoolingPrelanding.engine_cooling_prelanding_bridge
#print axioms RelCertifier.Bridge.EngineCoolingPrelanding.engine_cooling_prelanding_bridge_run
#print axioms RelCertifier.Bridge.HoldRepositionStrict.hold_reposition_strict_bridge
#print axioms RelCertifier.Bridge.HoldRepositionStrict.hold_reposition_strict_bridge_run
#print axioms RelCertifier.first_hit
#print axioms RelCertifier.repoProgress_two_reg
#print axioms RelCertifier.Emitted.AG_boxR
#print axioms RelCertifier.Emitted.AGS_boxR
open RelCertifier RelCertifier.Emitted in
example : (dynRegionI Bridge.HoldRepositionStrict.IR 4 Bridge.HoldRepositionStrict.covM
    Bridge.HoldRepositionStrict.prog 0 0 true).map (·.2.2) = some [true, false] := by
  decide +kernel
open RelCertifier RelCertifier.Emitted in
example : dynRegionI { Bridge.HoldRepositionStrict.IR with prelanding := false } 4
    Bridge.HoldRepositionStrict.covM Bridge.HoldRepositionStrict.prog 0 0 true = none := by
  decide +kernel
-- kernel negatives: the records with the key off fail the data gate
open RelCertifier RelCertifier.Emitted in
example : plOK { RelCertifier.Bridge.EngineCoolingPrelanding.IR with prelanding := false }
    RelCertifier.Bridge.EngineCoolingPrelanding.cov
    RelCertifier.Bridge.EngineCoolingPrelanding.pl = false := by
  decide +kernel
open RelCertifier RelCertifier.Emitted in
example : plOK { RelCertifier.Bridge.HoldRepositionStrict.IR with prelanding := false }
    RelCertifier.Bridge.HoldRepositionStrict.cov
    RelCertifier.Bridge.HoldRepositionStrict.pl = false := by
  decide +kernel
-- kernel negatives: without the pre-landing nodes the emitted covers do not close
open RelCertifier RelCertifier.Emitted in
example : coversOK RelCertifier.Bridge.EngineCoolingPrelanding.IR 4
    RelCertifier.Bridge.EngineCoolingPrelanding.cov
    RelCertifier.Bridge.EngineCoolingPrelanding.ce = false := by
  decide +kernel
open RelCertifier RelCertifier.Emitted in
example : coversOK RelCertifier.Bridge.HoldRepositionStrict.IR 4
    RelCertifier.Bridge.HoldRepositionStrict.cov
    RelCertifier.Bridge.HoldRepositionStrict.ce = false := by
  decide +kernel
