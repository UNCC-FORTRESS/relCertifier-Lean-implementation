/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The cover chain with strict components (extension `strict-atoms`)

Mirrors of the cover-level preservation for FLAGGED component lists (`HoldsAt`, strict
components kept `< 0`):

* `InvAllHoldsS` (the flagged `InvAllHolds`), its weakening to the closure and its collapse;
* `CoverCertMS`, `pres_multiS`, `check_sound_multiS` (`CoverMulti`);
* `CoverCertMCXS`, `pres_multi_cutXS`, `check_sound_multi_cutXS` (`CutLiftX`, the X channel:
  conditional staying of the cut atoms, guard-triggered reaches);
* `segPresAllS_cut_liftX` (the per-piece lift the modal instances consume).

The cut atoms stay closures (`≤ 0`); only the row components carry flags. Each mirror is
the existing induction with `HoldsAt` in place of `≤ 0`.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Soundness.CutLiftX
import RelCertifier.Proofs.Flow.StratifiedBarrierStrict

namespace RelCertifier
open DL

variable {n : ℕ}

/-- All flagged components hold: the strict conjunction invariant. -/
def InvAllHoldsS (ts : List (Bool × Term (Var n))) (ω : State (Var n)) : Prop :=
  ∀ c ∈ ts, HoldsAt c.1 c.2 ω

/-- Weakening to the closure. -/
theorem InvAllHoldsS.toClosure {ts : List (Bool × Term (Var n))} {ω : State (Var n)}
    (h : InvAllHoldsS ts ω) : InvAllHolds (ts.map Prod.snd) ω := by
  intro g hg
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
  exact (h c hc).le

/-- Collapse: every flag `false` is the existing invariant. -/
theorem invAllHoldsS_allFalse (gs : List (Term (Var n))) (ω : State (Var n)) :
    InvAllHoldsS (gs.map (fun g => (false, g))) ω ↔ InvAllHolds gs ω :=
  holdsAll_allFalse gs ω

/-! ## `CoverMulti`, flagged -/

/-- The flagged multi-component certificate bundle (`CoverCertM`). -/
structure CoverCertMS (G : SearchGraph (Var n)) (ts : List (Bool × Term (Var n))) : Prop where
  segPres : ∀ q m, G.modeAt q = some m → m.jointOK = true →
    SegPreservesAllOnS ts m.sys m.dom
  repoDynPresPre : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    SegPreservesAllOnS ts m.dynSys m.dynDomPre
  repoDynPresPost : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    SegPreservesAllOnS ts m.dynSys m.dynDomPost
  weightPos : ∀ m ∈ G.modes, 0 < m.weight

/-- `pres_multi`, flagged. -/
theorem pres_multiS (G : SearchGraph (Var n)) (ts : List (Bool × Term (Var n)))
    (cert : CoverCertMS G ts) :
    ∀ cfg ν ω, RightReach G cfg ν ω → InvAllHoldsS ts ν → InvAllHoldsS ts ω := by
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

/-- The flagged ∀∃-throughout invariant. -/
def CoexecInvAllThroughoutS (G : SearchGraph (Var n)) (ts : List (Bool × Term (Var n)))
    (cfg : Config) (ν : State (Var n)) : Prop :=
  ∀ ω, RightReach G cfg ν ω → InvAllHoldsS ts ω

/-- `check_sound_multi`, flagged. -/
theorem check_sound_multiS (G : SearchGraph (Var n)) (ts : List (Bool × Term (Var n)))
    (cert : CoverCertMS G ts) (fuel : ℕ) (cfg : Config)
    (hchk : decideCovered G fuel cfg = true)
    (ν : State (Var n)) (hinit : InvAllHoldsS ts ν) :
    Covered G cfg ∧ CoexecInvAllThroughoutS G ts cfg ν :=
  ⟨decideCovered_sound G fuel cfg hchk,
   fun ω hreach => pres_multiS G ts cert cfg ν ω hreach hinit⟩

/-! ## `CutLiftX`, flagged -/

/-- The flagged X-channel cut-narrowed certificate (`CoverCertMCX`): the cut atoms and their
staying facts are the existing ones; the segment fields preserve the flagged components. -/
structure CoverCertMCXS (G : SearchGraph (Var n)) (ts : List (Bool × Term (Var n)))
    (Gd : ℕ → Formula (Var n)) (cutL : List (CutAtomP n))
    (cutR : ℕ → List (CutAtomP n)) : Prop where
  hiffL : AtomsIff cutL
  hiffR : ∀ q, AtomsIff (cutR q)
  stayJL : ∀ q m, G.modeAt q = some m → m.jointOK = true → AtomsStayC cutL m.sys m.dom
  stayJR : ∀ q m, G.modeAt q = some m → m.jointOK = true → AtomsStayC (cutR q) m.sys m.dom
  stayDPreL : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    AtomsStayC cutL m.dynSys m.dynDomPre
  stayDPreR : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    AtomsStayC (cutR q) m.dynSys m.dynDomPre
  stayDPostL : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    AtomsStayC cutL m.dynSys m.dynDomPost
  stayDPostR : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    AtomsStayC (cutR q) m.dynSys m.dynDomPost
  entryR : ∀ q ν, Formula.sat (Gd q) ν → CutSat (cutR q) ν
  segPresC : ∀ q m, G.modeAt q = some m → m.jointOK = true →
    SegPreservesAllOnS ts m.sys
      (Formula.and m.dom (Formula.and (cutF cutL) (cutF (cutR q))))
  repoDynPresPreC : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    SegPreservesAllOnS ts m.dynSys
      (Formula.and m.dynDomPre (Formula.and (cutF cutL) (cutF (cutR q))))
  repoDynPresPostC : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    SegPreservesAllOnS ts m.dynSys
      (Formula.and m.dynDomPost (Formula.and (cutF cutL) (cutF (cutR q))))
  weightPos : ∀ m ∈ G.modes, 0 < m.weight

/-- Collapse: the existing certificate is the all-false flagged one. -/
theorem CoverCertMCX.toS {G : SearchGraph (Var n)} {gs : List (Term (Var n))}
    {Gd : ℕ → Formula (Var n)} {cutL : List (CutAtomP n)} {cutR : ℕ → List (CutAtomP n)}
    (c : CoverCertMCX G gs Gd cutL cutR) :
    CoverCertMCXS G (gs.map (fun g => (false, g))) Gd cutL cutR :=
  { hiffL := c.hiffL, hiffR := c.hiffR, stayJL := c.stayJL, stayJR := c.stayJR,
    stayDPreL := c.stayDPreL, stayDPreR := c.stayDPreR, stayDPostL := c.stayDPostL,
    stayDPostR := c.stayDPostR, entryR := c.entryR,
    segPresC := fun q m hm hj => (segPresAllOnS_allFalse _ _ _).mpr (c.segPresC q m hm hj),
    repoDynPresPreC := fun q m hm hj =>
      (segPresAllOnS_allFalse _ _ _).mpr (c.repoDynPresPreC q m hm hj),
    repoDynPresPostC := fun q m hm hj =>
      (segPresAllOnS_allFalse _ _ _).mpr (c.repoDynPresPostC q m hm hj),
    weightPos := c.weightPos }

/-- `pres_multi_cutX`, flagged. -/
theorem pres_multi_cutXS (G : SearchGraph (Var n)) (ts : List (Bool × Term (Var n)))
    (Gd : ℕ → Formula (Var n)) (cutL : List (CutAtomP n))
    (cutR : ℕ → List (CutAtomP n)) (cert : CoverCertMCXS G ts Gd cutL cutR) :
    ∀ cfg ν ω, RightReachG G Gd cfg ν ω →
      InvAllHoldsS ts ν → CutSat cutL ν → CutSat (cutR cfg.q) ν →
      InvAllHoldsS ts ω := by
  intro cfg ν ω hreach
  induction hreach with
  | refl => exact fun h _ _ => h
  | evolve m hm hj hsem _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2C cert.hiffL (cert.hiffR _)
        (cert.stayJL _ m hm hj) (cert.stayJR _ m hm hj) hsem hL hR
      exact ih (cert.segPresC _ m hm hj _ hν _ hrun)
        (cutSat_endpointC cutL cert.hiffL (cert.stayJL _ m hm hj) hsem hL)
        (cutSat_endpointC _ (cert.hiffR _) (cert.stayJR _ m hm hj) hsem hR)
  | jump m hm hj e he hsrc hlt hsem hguard hGd _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2C cert.hiffL (cert.hiffR _)
        (cert.stayJL _ m hm hj) (cert.stayJR _ m hm hj) hsem hL hR
      exact ih (cert.segPresC _ m hm hj _ hν _ hrun)
        (cutSat_endpointC cutL cert.hiffL (cert.stayJL _ m hm hj) hsem hL)
        (cert.entryR _ _ hGd)
  | repositionDynPre m hm hrepo e he hsrc hB hsem hGd _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2C cert.hiffL (cert.hiffR _)
        (cert.stayDPreL _ m hm hrepo) (cert.stayDPreR _ m hm hrepo) hsem hL hR
      exact ih (cert.repoDynPresPreC _ m hm hrepo _ hν _ hrun)
        (cutSat_endpointC cutL cert.hiffL (cert.stayDPreL _ m hm hrepo) hsem hL)
        (cert.entryR _ _ hGd)
  | repositionDynPost m hm hrepo e he hsrc hB hsem hGd _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2C cert.hiffL (cert.hiffR _)
        (cert.stayDPostL _ m hm hrepo) (cert.stayDPostR _ m hm hrepo) hsem hL hR
      exact ih (cert.repoDynPresPostC _ m hm hrepo _ hν _ hrun)
        (cutSat_endpointC cutL cert.hiffL (cert.stayDPostL _ m hm hrepo) hsem hL)
        (cert.entryR _ _ hGd)

/-- The flagged ∀∃-throughout invariant over guard-triggered reaches. -/
def CoexecInvAllThroughoutGS (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n))
    (ts : List (Bool × Term (Var n))) (cfg : Config) (ν : State (Var n)) : Prop :=
  ∀ ω, RightReachG G Gd cfg ν ω → InvAllHoldsS ts ω

/-- `check_sound_multi_cutX`, flagged. -/
theorem check_sound_multi_cutXS (G : SearchGraph (Var n)) (ts : List (Bool × Term (Var n)))
    (Gd : ℕ → Formula (Var n)) (cutL : List (CutAtomP n))
    (cutR : ℕ → List (CutAtomP n)) (cert : CoverCertMCXS G ts Gd cutL cutR)
    (fuel : ℕ) (cfg : Config) (hchk : decideCovered G fuel cfg = true)
    (ν : State (Var n)) (hinit : InvAllHoldsS ts ν)
    (hinitL : CutSat cutL ν) (hinitR : CutSat (cutR cfg.q) ν) :
    Covered G cfg ∧ CoexecInvAllThroughoutGS G Gd ts cfg ν :=
  ⟨decideCovered_sound G fuel cfg hchk,
   fun ω hreach => pres_multi_cutXS G ts Gd cutL cutR cert cfg ν ω hreach
     hinit hinitL hinitR⟩

/-- `segPresAll_cut_liftX`, flagged: the narrowed flagged preservation and the atoms'
conditional staying give flagged preservation over the bare domain. -/
theorem segPresAllS_cut_liftX {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {ts : List (Bool × Term (Var n))} {cutL cutRq : List (CutAtomP n)}
    (hiffL : AtomsIff cutL) (hiffR : AtomsIff cutRq)
    (hstayL : AtomsStayC cutL sys dom) (hstayR : AtomsStayC cutRq sys dom)
    (hnarrow : SegPreservesAllOnS ts sys
      (Formula.and dom (Formula.and (cutF cutL) (cutF cutRq)))) :
    ∀ ν, CutSat cutL ν → CutSat cutRq ν → (∀ c ∈ ts, HoldsAt c.1 c.2 ν) →
      ∀ ω, Program.sem (Program.ode sys dom) ν ω →
        (∀ c ∈ ts, HoldsAt c.1 c.2 ω) ∧ CutSat cutL ω ∧ CutSat cutRq ω := by
  intro ν hL hR hinv ω hsem
  exact ⟨hnarrow ν hinv ω (sem_ode_narrow2C hiffL hiffR hstayL hstayR hsem hL hR),
    cutSat_endpointC cutL hiffL hstayL hsem hL,
    cutSat_endpointC cutRq hiffR hstayR hsem hR⟩

end RelCertifier
