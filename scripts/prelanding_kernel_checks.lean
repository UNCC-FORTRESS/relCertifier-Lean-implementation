/- Pre-landing kernel checks (docs/PRELANDING.md). Run:
`lake env lean scripts/prelanding_kernel_checks.lean` (after
`lake build RelCertifier.InstancesV2.Bridge.EngineCoolingPrelanding`).
* the axioms of Theorem 3 of the demo (from the records and from a green run), of the
  first-hit closers and of the half-open anchor lemma: expected
  `[propext, Classical.choice, Quot.sound]` for the generic lemmas and
  `[propext, Classical.choice, Quot.sound, RelCertifier.z3_unsat_sound]` for the instance;
* kernel negatives: the data gate `plOK` rejects the demo's record when the IR has the key off
  (`prelanding := false`); the emitted cover WITHOUT the pre-landing nodes merged fails the
  cover check `coversOK` (the nodes are needed: the right-only kind is genuine). A green run
  prints only the axiom lines. -/
import RelCertifier.InstancesV2.Bridge.EngineCoolingPrelanding
#print axioms RelCertifier.Bridge.EngineCoolingPrelanding.engine_cooling_prelanding_bridge
#print axioms RelCertifier.Bridge.EngineCoolingPrelanding.engine_cooling_prelanding_bridge_run
#print axioms RelCertifier.first_hit
#print axioms RelCertifier.repoProgress_twoB
#print axioms RelCertifier.Emitted.AG_boxPLH
#print axioms RelCertifier.Emitted.theorem3_window_of_records_pl
-- kernel negative: the record with the key off fails the data gate
open RelCertifier RelCertifier.Emitted in
example : plOK { RelCertifier.Bridge.EngineCoolingPrelanding.IR with prelanding := false }
    RelCertifier.Bridge.EngineCoolingPrelanding.cov
    RelCertifier.Bridge.EngineCoolingPrelanding.pl = false := by
  decide +kernel
-- kernel negative: without the pre-landing nodes the emitted cover does not close
open RelCertifier RelCertifier.Emitted in
example : coversOK RelCertifier.Bridge.EngineCoolingPrelanding.IR 4
    RelCertifier.Bridge.EngineCoolingPrelanding.cov
    RelCertifier.Bridge.EngineCoolingPrelanding.ce = false := by
  decide +kernel
