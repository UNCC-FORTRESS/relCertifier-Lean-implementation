/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Reproducible axiom audit

Re-run: `lake env lean RelCertifier/InstancesV2/AxiomCheck.lean` (or read the build log — this module is in the
`RelCertifier` import root, so the `#print axioms` below re-emit on every `lake build`).

Expected output (Appendix B.4: eleven lines, eight at the three standard Lean axioms and three,
the flow-certificate, segment-preservation and mode-fact lemmas, with the single trusted leaf
`z3_unsat_sound` added, exactly where a `z3solve … = unsat` is turned into a fact):

  cover_sound                            : [propext, Classical.choice, Quot.sound]
  check_sound                            : [propext, Classical.choice, Quot.sound]
  theorem3_faithful                      : [propext, Classical.choice, Quot.sound]
  rvalid_from_cert                       : [propext, Classical.choice, Quot.sound]
  decideCovered_implies_theorem3_faithful: [propext, Classical.choice, Quot.sound]
  flow_certified                         : [propext, Classical.choice, Quot.sound, z3_unsat_sound]
  segPres_from_flowCert                  : [propext, Classical.choice, Quot.sound, z3_unsat_sound]
  stratified_barrier_sound               : [propext, Classical.choice, Quot.sound]
  cut_hcert                              : [propext, Classical.choice, Quot.sound, z3_unsat_sound]
  odeSol_stretch_iff (Lemma 1)           : [propext, Classical.choice, Quot.sound]
  odeSol_rightBlock_stretch_iff          : [propext, Classical.choice, Quot.sound]

For the per-benchmark audit (every suite_v2 benchmark's Theorem 3 and its axioms) see
`InstancesV2/WellFormedBattery.lean` (Assumption 1 of every right model, Appendix B.5) and the
bridge instances `InstancesV2/Bridge/*.lean` (Theorem 3 through the generic bridge); for what
to run and what to expect, `docs/CERTIFICATION-CHECK.md`.

`decideCovered_implies_theorem3_faithful` is parametric in `cert : CoverCert` (a `Prop`), so it does
NOT itself apply `z3_unsat_sound`; the leaf enters when that certificate is constructed per mode via
`segPres_from_flowCert`/`flow_certified`. `stratified_barrier_sound` (the rounds of Section 4.1)
takes its per-round facts as hypotheses and is likewise standard. No `sorryAx`, no
`native_decide` on any line below.
-/
import RelCertifier.Proofs.Encoding.BridgeDischarge
import RelCertifier.Proofs.Flow.StratifiedBarrier
import RelCertifier.Proofs.Soundness.CutLift
import RelCertifier.Proofs.Encoding.Stretching

namespace RelCertifier

-- Cover / checker core (three standard axioms)
#print axioms cover_sound
#print axioms check_sound

-- Transition-faithful ∀∃ + the end-to-end seam (three standard axioms; parametric in the certificate)
#print axioms theorem3_faithful
#print axioms rvalid_from_cert
#print axioms decideCovered_implies_theorem3_faithful

-- Where a verdict becomes a fact: a flow certificate (Lemma 2), its segment preservation, and
-- a mode-fact certificate (+ z3_unsat_sound); the rounds lemma between them takes its
-- per-round facts as hypotheses (three standard axioms).
#print axioms flow_certified
#print axioms segPres_from_flowCert
#print axioms stratified_barrier_sound
#print axioms cut_hcert

-- Lemma 1 (Time Stretching), λ ≥ 0, as stated (three standard axioms)
#print axioms odeSol_stretch_iff
#print axioms odeSol_rightBlock_stretch_iff

end RelCertifier
