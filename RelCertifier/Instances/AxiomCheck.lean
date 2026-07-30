/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Reproducible axiom audit

Re-run: `lake env lean RelCertifier/Instances/AxiomCheck.lean` (or read the build log — this module is in the
`RelCertifier` import root, so the `#print axioms` below re-emit on every `lake build`).

Expected output — the whole verified chain depends on the three standard Lean axioms; the single
trusted leaf `z3_unsat_sound` appears exactly where a `z3solve … = unsat` is turned into a flow
certificate (`flow_certified`, and anything constructing a `CoverCert` from it):

  cover_sound                            : [propext, Classical.choice, Quot.sound]
  check_sound                            : [propext, Classical.choice, Quot.sound]
  theorem3_faithful                      : [propext, Classical.choice, Quot.sound]
  rvalid_from_cert                       : [propext, Classical.choice, Quot.sound]
  decideCovered_implies_theorem3_faithful: [propext, Classical.choice, Quot.sound]
  flow_certified                         : [propext, Classical.choice, Quot.sound, z3_unsat_sound]
  segPres_from_flowCert                  : [propext, Classical.choice, Quot.sound, z3_unsat_sound]

For the per-benchmark audit — every certified benchmark's modal Theorem 3 and its axioms — see
`Instances/ModalBattery.lean`; for what to run and what to expect, `docs/CERTIFICATION-CHECK.md`.

`decideCovered_implies_theorem3_faithful` is parametric in `cert : CoverCert` (a `Prop`), so it does
NOT itself apply `z3_unsat_sound` — the leaf enters when that certificate is constructed per-mode via
`segPres_from_flowCert`/`flow_certified`. No `sorryAx`, no `native_decide` on any line below.
-/
import RelCertifier.Proofs.Encoding.BridgeDischarge
import RelCertifier.Proofs.Flow.StratifiedBarrier
import RelCertifier.Proofs.Soundness.CutLift

namespace RelCertifier

-- Cover / checker core (three standard axioms)
#print axioms cover_sound
#print axioms check_sound

-- Transition-faithful ∀∃ + the end-to-end seam (three standard axioms; parametric in the certificate)
#print axioms theorem3_faithful
#print axioms rvalid_from_cert
#print axioms decideCovered_implies_theorem3_faithful

-- The Z3 trust leaf (+ z3_unsat_sound), at every boundary where a verdict becomes a fact.
-- These are the ONLY shapes through which `z3_unsat_sound` reaches a benchmark theorem:
-- a flow certificate, a stratified-cut certificate, a viability face, or a cut atom.
#print axioms flow_certified
#print axioms segPres_from_flowCert
#print axioms stratified_barrier_sound
#print axioms cut_hcert

end RelCertifier
