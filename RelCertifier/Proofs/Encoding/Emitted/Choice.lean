/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge, part 9: the chosen sets, from the emitted choice record

The existential mode choice (`docs/CHOICE-SOUNDNESS.md`, cases 3 and 4 of `CoveredX`): after a
joint or right-only segment of `q` the witness covers only a chosen subset of the successors,
and may hop into a chosen successor before a segment, each under a coverage query
`region ∧ ⋀_{q' ∈ S} ¬guard(q')` the tool found `unsat`. The record (`Choice.ChoiceEmitE`)
names the chosen sets; `chOfC` is the `ChoiceData` of a window from it; `coverageQueryOf`
rebuilds each entry's query from the tool's regions (`leftFacts`/`rightFacts`); `coverage_sound`
reads `unsat` as "some chosen successor's guard holds on the region". The regions are the
anchor's region facts (`regionF`), so the general theorem's `hRJ/hRR/hRS` are `AG_regionF`.
-/
import RelCertifier.Proofs.Encoding.Emitted.Progress
import RelCertifier.Trusted.ChoiceEmit

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL Parse Run Set Oracle Progress Choice

variable {n : ℕ}

section Defs

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE) (ce : ChoiceEmitE)

/-- The entries of window `l` at right mode `q` of a kind and setting. -/
def entriesAt (l q : ℕ) (k : ChoiceKind) (pre : Bool) : List ChoiceEntryE :=
  if q < nR p then
    ce.entries.filter (fun e => e.mL == (mLof p l).name && e.q == (mRof p q).name &&
      e.kind == k && (k == .joint || e.pre == pre))
  else []

def preOf : SrcSetting → Bool
  | SrcSetting.preJ => true
  | SrcSetting.postJ => false

/-- The window's choice data: the cover flags and the chosen sets by index. -/
def chOfC (l : ℕ) : ChoiceData :=
  { jointOK := fun q => (flagsOf p cov l q).jointOK,
    repoPre := fun q => (flagsOf p cov l q).dynPre,
    repoPost := fun q => (flagsOf p cov l q).dynPost,
    jointS := fun q => (entriesAt p ce l q .joint false).map (fun e => e.S.map (tgtIdx p)),
    repoS := fun q σ => (entriesAt p ce l q .repo (preOf σ)).map (fun e => e.S.map (tgtIdx p)),
    hopS := fun q σ => (entriesAt p ce l q .hop (preOf σ)).map (fun e => e.S.map (tgtIdx p)) }

/-- The coverage query of an entry, rebuilt from the records at the entry's window and mode
(by name). -/
def coverageQueryOf (e : ChoiceEntryE) : Option (IForm n) := do
  let l := modeIdx p.L.modes e.mL
  let q := modeIdx p.R.modes e.q
  let mL := mLof p l
  let mR := mRof p q
  let comps ← invComponents (vars p) n (rowOf p l)
  let aL ← ((cutAtomsOfX cX.L mL.name).map (·.atom)).mapM (lowerF (vars p) n Side.L)
  let aR ← ((cutAtomsOfX cX.R mR.name).map (·.atom)).mapM (lowerF (vars p) n Side.R)
  let cutL := aL.foldl IForm.and IForm.tt
  let cutR := aR.foldl IForm.and IForm.tt
  let guards ← e.S.mapM (fun nm => (p.R.modes.find? (·.name == nm)).bind
    (fun md => lowerF (vars p) n Side.R md.guard))
  pure (coverageQuery (regionOfEntry (vars p) n mL mR cutL cutR comps e) guards)

def CoverageVerd (e : ChoiceEntryE) : Prop :=
  ∃ q, coverageQueryOf p n cX e = some q ∧ z3solve q.toHost = Verdict.unsat

def CoverageAll : Prop := ∀ e ∈ ce.entries, CoverageVerd p n cX e

/-- The setting an entry's region is taken at. -/
def entryPre (e : ChoiceEntryE) : Bool := if e.kind == .joint then false else e.pre

end Defs

/-! ## Reading a coverage verdict -/

theorem sat_cutFold {vars : List String} {side : Side} {atoms : List CutAtomX} {fs : List (IForm n)}
    (h : (atoms.map (·.atom)).mapM (lowerF vars n side) = some fs) (y : State (Var n)) :
    CutSat (cutPairsX vars n side atoms) y → Formula.sat (fs.foldl IForm.and IForm.tt).toHost y := by
  intro hcut
  rw [sat_foldl_and]
  refine ⟨trivial, fun f hf => ?_⟩
  obtain ⟨a, ha, hlow⟩ := mapM_option_mem h f hf
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  have := hcut _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  simpa [hostAtomF, hlow] using this

theorem sat_lowGetD {vars : List String} {side : Side} (f : PForm) (y : State (Var n)) :
    Formula.sat (((lowerF vars n side f).map IForm.toHost).getD Formula.tt) y →
      Formula.sat ((lowerF vars n side f).getD IForm.tt).toHost y := by
  rcases lowerF vars n side f with _ | g <;> simp [IForm.toHost, Formula.sat]

/-- The region's host holds at a state of `RegionSat` (and, for a hop, of the mode's guard). -/
theorem sat_regionOfEntry {p : PProblem} {cX : EvolStrengtheningX} {mL mR : PMode} {row : PForm}
    {comps : List (ITerm n)} (hc : invComponents (vars p) n row = some comps)
    {aL aR : List (IForm n)}
    (hL : ((cutAtomsOfX cX.L mL.name).map (·.atom)).mapM (lowerF (vars p) n Side.L) = some aL)
    (hR : ((cutAtomsOfX cX.R mR.name).map (·.atom)).mapM (lowerF (vars p) n Side.R) = some aR)
    (e : ChoiceEntryE) (y : State (Var n))
    (hreg : RegionSat (vars p) n cX mL mR row (entryPre e) y)
    (hg : e.kind = .hop → Formula.sat (hostGuard (vars p) n Side.R mR) y) :
    Formula.sat (regionOfEntry (vars p) n mL mR (aL.foldl IForm.and IForm.tt)
      (aR.foldl IForm.and IForm.tt) comps e).toHost y := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hreg
  have hbase : ∀ pre, (pre = true → Formula.sat (hostGuard (vars p) n Side.L mL) y) →
      Formula.sat (IForm.and (leftFacts (vars p) n mL (aL.foldl IForm.and IForm.tt) comps pre)
        (rightFacts (vars p) n mR (aR.foldl IForm.and IForm.tt))).toHost y := by
    intro pre hpre
    refine ⟨?_, sat_lowGetD (vars := vars p) (side := Side.R) _ y h5, sat_cutFold hR y h6⟩
    unfold leftFacts
    have hb : Formula.sat (IForm.and (IForm.and ((lowerF (vars p) n Side.L mL.evolve).getD IForm.tt)
        (aL.foldl IForm.and IForm.tt))
        (comps.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) IForm.tt)).toHost y := by
      refine ⟨⟨sat_lowGetD (vars := vars p) (side := Side.L) _ y h1, sat_cutFold hL y h2⟩, ?_⟩
      rw [sat_foldl_le]
      refine ⟨trivial, fun c hcm => ?_⟩
      rw [hostComps_of_lower hc] at h3
      exact h3 _ (List.mem_map.mpr ⟨c, hcm, rfl⟩)
    cases pre with
    | false => simpa using hb
    | true => exact ⟨hb, sat_lowGetD (vars := vars p) (side := Side.L) _ y (hpre rfl)⟩
  unfold regionOfEntry
  rcases hk : e.kind with _ | _ | _
  · simp only
    exact hbase false (by simp)
  · simp only
    exact hbase e.pre (fun hp => h4 (by simpa [entryPre, hk] using hp))
  · simp only
    exact ⟨hbase e.pre (fun hp => h4 (by simpa [entryPre, hk] using hp)),
      sat_lowGetD (vars := vars p) (side := Side.R) _ y (hg hk)⟩

/-- A guard of the chosen list holds at a state of the region where no other does not: the
coverage query's reading. -/
theorem coverage_sound {p : PProblem} {cX : EvolStrengtheningX} {e : ChoiceEntryE}
    (hv : CoverageVerd p n cX e) :
    ∀ y, RegionSat (vars p) n cX (mLof p (modeIdx p.L.modes e.mL)) (mRof p (modeIdx p.R.modes e.q))
        (rowOf p (modeIdx p.L.modes e.mL)) (entryPre e) y →
      (e.kind = .hop → Formula.sat (hostGuard (vars p) n Side.R (mRof p (modeIdx p.R.modes e.q))) y) →
      ∃ nm ∈ e.S, ∃ md ∈ p.R.modes, md.name = nm ∧ Formula.sat (hostGuard (vars p) n Side.R md) y := by
  obtain ⟨q, hq, hz⟩ := hv
  unfold coverageQueryOf at hq
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at hq
  obtain ⟨comps, hc, aL, hL, aR, hR, guards, hguards, rfl⟩ := hq
  intro y hreg hg
  have hbase := sat_regionOfEntry hc hL hR e y hreg hg
  obtain ⟨g, hgm, hsat⟩ := land_of_unsat _ guards hz y hbase
  obtain ⟨nm, hnm, hlow⟩ := mapM_option_mem hguards g hgm
  simp only [Option.bind_eq_some_iff] at hlow
  obtain ⟨md, hfind, hlowg⟩ := hlow
  refine ⟨nm, hnm, md, List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind, ?_⟩
  rw [hostGuard_of_lower hlowg]; exact hsat

/-! ## The general theorem's coverage premises -/

section Proofs

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {ce : ChoiceEmitE}
  (hs : structOK p n cov cX = true)

omit hs in
theorem mem_entriesAt {l q : ℕ} {k : ChoiceKind} {pre : Bool} {e : ChoiceEntryE}
    (h : e ∈ entriesAt p ce l q k pre) :
    q < nR p ∧ e ∈ ce.entries ∧ e.mL = (mLof p l).name ∧ e.q = (mRof p q).name ∧ e.kind = k ∧
      (k = .joint ∨ e.pre = pre) := by
  unfold entriesAt at h
  split_ifs at h with hq
  · rw [List.mem_filter] at h
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    exact ⟨hq, h.1, h.2.1.1.1, h.2.1.1.2, h.2.1.2, h.2.2⟩
  · simp at h

include hs

/-- A declared mode is at its name's index. -/
theorem mRof_tgtIdx_of_mem {md : PMode} (hmd : md ∈ p.R.modes) :
    tgtIdx p md.name < nR p ∧ mRof p (tgtIdx p md.name) = md := by
  have hres' := hres hs
  simp only [namesResolve, Bool.and_eq_true, decide_eq_true_eq] at hres'
  have hlt : tgtIdx p md.name < nR p :=
    List.findIdx_lt_length.mpr ⟨md, hmd, by simp⟩
  refine ⟨hlt, ?_⟩
  have hname : (mRof p (tgtIdx p md.name)).name = md.name := by
    unfold mRof tgtIdx at hlt ⊢
    rw [List.getD_eq_getElem _ _ hlt]
    have := List.findIdx_getElem (p := fun m : PMode => m.name == md.name) (xs := p.R.modes)
      (w := hlt)
    simpa using this
  exact List.inj_on_of_nodup_map hres'.1.1 (mRof_mem hlt) hmd hname

/-- A guard of the chosen set (by index) from a named one. -/
theorem guard_of_named {l q : ℕ} {e : ChoiceEntryE}
    (he : e.mL = (mLof p l).name) (heq : e.q = (mRof p q).name)
    (hidxL : modeIdx p.L.modes (mLof p l).name = l) (hidxR : modeIdx p.R.modes (mRof p q).name = q)
    (hv : CoverageVerd p n cX e) (y : State (Var n))
    (hreg : RegionSat (vars p) n cX (mLof p l) (mRof p q) (rowOf p l) (entryPre e) y)
    (hg : e.kind = .hop → Formula.sat (guardR p n q) y) :
    ∃ q' ∈ e.S.map (tgtIdx p), Formula.sat (guardR p n q') y := by
  have := coverage_sound hv y (by rw [he, heq, hidxL, hidxR]; exact hreg)
    (by rw [heq, hidxR]; exact hg)
  obtain ⟨nm, hnm, md, hmd, hname, hsat⟩ := this
  refine ⟨tgtIdx p nm, List.mem_map.mpr ⟨nm, hnm, rfl⟩, ?_⟩
  rw [← hname]
  unfold guardR
  rw [(mRof_tgtIdx_of_mem hs hmd).2]
  exact hsat

end Proofs

end Emitted
end RelCertifier
