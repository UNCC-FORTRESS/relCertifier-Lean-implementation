/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Multi-component covers (R5): `CoverCert` and `check_sound`, list-generalized

The checker layer (`Covered`, `RightReach`, `decideCovered`) is invariant-free; only the
certificate bundle and the preservation theorems mention the invariant term. This file
mirrors them for COMPONENT LISTS — the tool's real invariants (`invComponents`, up to 21
conjuncts) — with the segment fields discharged by the stratified multi-barrier layer
(`SegPreservesAllOn`, `segPresAll_from_strata_verdicts`), matching the stratified
`checkSeg`/`checkDynRepo` queries exactly.

`check_sound_multi` is the runner↔theorem connection for the full conjunction: the
kernel-replayed `decideCovered` (BenchCoverReplay) + the per-benchmark verdict bundle
give the ∀∃-throughout invariant of EVERY component simultaneously.
-/
import RelCertifier.Proofs.Flow.StratifiedBarrier
import RelCertifier.Checker.Checker

namespace RelCertifier
open DL

variable {n : ℕ}

/-- All components hold: the conjunction invariant. -/
def InvAllHolds (gs : List (Term (Var n))) (ω : State (Var n)) : Prop :=
  ∀ g ∈ gs, Term.eval g ω ≤ 0

/-- The multi-component certificate bundle — `CoverCert` with the invariant a list.
Joint and dynamic-reposition segments carry `SegPreservesAllOn` (discharged by the
stratified multi-barrier verdicts). There is no static reposition field. -/
structure CoverCertM (G : SearchGraph (Var n)) (gs : List (Term (Var n))) : Prop where
  segPres : ∀ q m, G.modeAt q = some m → m.jointOK = true →
    SegPreservesAllOn gs m.sys m.dom
  repoDynPresPre : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    SegPreservesAllOn gs m.dynSys m.dynDomPre
  repoDynPresPost : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    SegPreservesAllOn gs m.dynSys m.dynDomPost
  weightPos : ∀ m ∈ G.modes, 0 < m.weight

/-- **Preservation is per-segment, per component list** — the `pres` mirror. Along every
assembled right response, from a jointly-invariant entry, every component holds
throughout. Same induction as the single-`g` `pres`; each case consumes its list-field. -/
theorem pres_multi (G : SearchGraph (Var n)) (gs : List (Term (Var n)))
    (cert : CoverCertM G gs) :
    ∀ cfg ν ω, RightReach G cfg ν ω → InvAllHolds gs ν → InvAllHolds gs ω := by
  intro cfg ν ω hreach
  induction hreach with
  | refl => exact id
  | evolve m hm hj hsem _ ih =>
      intro hν; exact ih (cert.segPres _ m hm hj _ hν _ hsem)
  | jump m hm hj e he hsrc hlt hsem hguard _ ih =>
      intro hν; exact ih (cert.segPres _ m hm hj _ hν _ hsem)
  | repositionDynPre m hm hrepo e he hsrc hB hsem _ ih =>
      intro hν; exact ih (cert.repoDynPresPre _ m hm hrepo _ hν _ hsem)
  | repositionDynPost m hm hrepo e he hsrc hB hsem _ ih =>
      intro hν; exact ih (cert.repoDynPresPost _ m hm hrepo _ hν _ hsem)

/-- The ∀∃-throughout invariant, conjunction form. -/
def CoexecInvAllThroughout (G : SearchGraph (Var n)) (gs : List (Term (Var n)))
    (cfg : Config) (ν : State (Var n)) : Prop :=
  ∀ ω, RightReach G cfg ν ω → InvAllHolds gs ω

/-- **The runner↔theorem connection, multi-component.** The kernel-replayed
`decideCovered` + the certificate bundle give the throughout invariant of every
component simultaneously. (`decideCovered` governs existence/finiteness via
`decideCovered_sound`; preservation is `pres_multi`, `Covered`-free — same factoring
as the single-`g` `check_sound`.) -/
theorem check_sound_multi (G : SearchGraph (Var n)) (gs : List (Term (Var n)))
    (cert : CoverCertM G gs) (fuel : ℕ) (cfg : Config)
    (hchk : decideCovered G fuel cfg = true)
    (ν : State (Var n)) (hinit : InvAllHolds gs ν) :
    Covered G cfg ∧ CoexecInvAllThroughout G gs cfg ν :=
  ⟨decideCovered_sound G fuel cfg hchk,
   fun ω hreach => pres_multi G gs cert cfg ν ω hreach hinit⟩

end RelCertifier
