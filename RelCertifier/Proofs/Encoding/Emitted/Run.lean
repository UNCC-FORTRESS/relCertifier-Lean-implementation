/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge, part 7: the queries of a benchmark, as one list of groups

`bridgeGroups` builds, from the records alone, every query the instance's `Verdicts` rest on,
as groups of alternatives (a flow pack's component is discharged by any of its three routes;
every other group is a singleton). `verdicts_of_groups` reads a run in which every group has
an `unsat` member as the `Verdicts` structure. The runner (`VerdictsV2/RunBridge.lean`) issues
exactly `bridgeGroups`; so the runner's green light is the instance's hypothesis.
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.VerdictsV2.ModalDynX

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL Parse Run Oracle Bridge Progress

variable {n : ℕ}

/-- A group of alternatives is discharged when one member is `unsat`. -/
def GroupsOK (gs : List (List (IForm n))) : Prop :=
  ∀ g ∈ gs, ∃ q ∈ g, z3solve q.toHost = Verdict.unsat

theorem groupsOK_append {a b : List (List (IForm n))} (h : GroupsOK (a ++ b)) :
    GroupsOK a ∧ GroupsOK b :=
  ⟨fun g hg => h g (List.mem_append_left _ hg), fun g hg => h g (List.mem_append_right _ hg)⟩

theorem groupsOK_flatten {gss : List (List (List (IForm n)))} (h : GroupsOK gss.flatten) :
    ∀ gs ∈ gss, GroupsOK gs :=
  fun gs hgs g hg => h g (List.mem_flatten.mpr ⟨gs, hgs, hg⟩)

theorem mapM_range {β : Type} {f : ℕ → Option β} {k : ℕ} {l' : List β}
    (h : (List.range k).mapM f = some l') : ∀ i < k, ∃ y ∈ l', f i = some y :=
  fun i hi => mapM_option_forall h i (List.mem_range.mpr hi)

section Builders

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
  (prog : ProgressEmitE)

def stayGroups (side : Side) (m : PMode) (atoms : List CutAtomX) : Option (List (List (IForm n))) :=
  (List.range atoms.length).mapM (fun i => (stayQueryOf (vars p) n side m atoms i).map ([·]))

def nonConnGroups (q : ℕ) : Option (List (List (IForm n))) := do
  let gs ← (prunedTgts p cov q).mapM (fun t => do
    let cutR ← NonConn.cutOfAtoms (vars p) n ((cutAtomsOfX cX.R (mRof p q).name).map (·.atom))
    let (q1, q2) ← NonConn.queries (vars p) n cutR (mRof p q) (mRof p t)
    pure [[q1], [q2]])
  pure gs.flatten

def jointGroups (l q : ℕ) : Option (List (List (IForm n))) :=
  if (flagsOf p cov l q).jointOK then
    modalVerdXQueries p cX n (rowIdx p l) (strataOf p cov l q).order (lamQ p cov l q) l q
  else some []

def dynGroups (l q : ℕ) (pre : Bool) : Option (List (List (IForm n))) :=
  if (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) then
    (modalVerdDynXQueries p cX n (rowIdx p l)
      (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder)
      pre l q).map (·.map ([·]))
  else some []

def admGroups (l : ℕ) : Option (List (List (IForm n))) :=
  ((List.range (nR p)).filter (fun q => !(admissibleOf p cov l).contains q)).mapM (fun q =>
    (admQueryOf (vars p) n (rowOf p l) (mLof p l) (mRof p q)).map ([·]))

def handoffGroups (m' : ℕ) : Option (List (List (IForm n))) :=
  ((nextL p).getD m' []).mapM (fun t => (Handoff.queryOf p n (m', t)).map ([·]))

def progGroups (c : ProgressE) : Option (List (List (IForm n))) :=
  (progressQueriesOf p cX n (invRowOf p (modeIdx p.L.modes c.mL)) (modeIdx p.L.modes c.mL)
    (modeIdx p.R.modes c.mR) c).map (·.map ([·]))

/-- **Every query of the benchmark**, in groups. -/
def bridgeGroups : Option (List (List (IForm n))) := do
  let sL ← (List.range (nL p)).mapM (fun l =>
    stayGroups p n Side.L (mLof p l) (cutAtomsOfX cX.L (mLof p l).name))
  let sR ← (List.range (nR p)).mapM (fun q =>
    stayGroups p n Side.R (mRof p q) (cutAtomsOfX cX.R (mRof p q).name))
  let nc ← (List.range (nR p)).mapM (nonConnGroups p n cX cov)
  let jt ← (List.range (nL p)).mapM (fun l => (List.range (nR p)).mapM (jointGroups p n cX cov l))
  let dy ← (List.range (nL p)).mapM (fun l => (List.range (nR p)).mapM (fun q =>
    [true, false].mapM (dynGroups p n cX cov l q)))
  let ad ← (List.range (nL p)).mapM (admGroups p n cov)
  let ho ← (List.range (nL p)).mapM (handoffGroups p n)
  let pr ← prog.certs.mapM (progGroups p n cX)
  pure (sL.flatten ++ sR.flatten ++ nc.flatten ++ jt.flatten.flatten ++
    dy.flatten.flatten.flatten ++ ad.flatten ++ ho.flatten ++ pr.flatten)

end Builders

/-! ## Reading a green run -/

section Link

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}

theorem stayVerd_of_groups {side : Side} {m : PMode} {atoms : List CutAtomX}
    {gs : List (List (IForm n))} (h : stayGroups p n side m atoms = some gs) (hok : GroupsOK gs) :
    StayVerd (vars p) n side m atoms := by
  intro i hi
  obtain ⟨g, hg, hgi⟩ := mapM_range h i hi
  rcases hq : stayQueryOf (vars p) n side m atoms i with _ | q
  · rw [hq] at hgi; simp at hgi
  · rw [hq] at hgi
    simp only [Option.map_some, Option.some.injEq] at hgi
    obtain ⟨q', hq', hz⟩ := hok _ hg
    have hq'' : q' ∈ [q] := by first | (rw [← hgi] at hq'; exact hq') | (rw [hgi] at hq'; exact hq')
    rw [List.mem_singleton] at hq''; subst hq''
    exact ⟨_, rfl, hz⟩

theorem nonConnVerd_of_groups {q : ℕ} {gs : List (List (IForm n))}
    (h : nonConnGroups p n cX cov q = some gs) (hok : GroupsOK gs) :
    ∀ t ∈ prunedTgts p cov q,
      NonConnVerd (vars p) n (cutAtomsOfX cX.R (mRof p q).name) (mRof p q) (mRof p t) := by
  intro t ht
  unfold nonConnGroups at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at h
  obtain ⟨gss, hgss, rfl⟩ := h
  obtain ⟨g2, hg2, ht'⟩ := mapM_option_forall hgss t ht
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at ht'
  obtain ⟨cutR, hcut, ⟨q1, q2⟩, hq, hg2eq⟩ := ht'
  have hok' := groupsOK_flatten hok _ hg2
  have hmem1 : [q1] ∈ g2 := by first | (rw [← hg2eq]; simp) | (rw [hg2eq]; simp)
  have hmem2 : [q2] ∈ g2 := by first | (rw [← hg2eq]; simp) | (rw [hg2eq]; simp)
  obtain ⟨a, ha, hza⟩ := hok' [q1] hmem1
  obtain ⟨b, hb, hzb⟩ := hok' [q2] hmem2
  rw [List.mem_singleton] at ha hb
  subst ha; subst hb
  exact ⟨cutR, _, _, hcut, hq, hza, hzb⟩

theorem jointVerd_of_groups {l q : ℕ} {gs : List (List (IForm n))}
    (h : jointGroups p n cX cov l q = some gs) (hok : GroupsOK gs)
    (hj : (flagsOf p cov l q).jointOK = true) : JointVerd p n cX cov l q := by
  unfold jointGroups at h
  rw [if_pos hj] at h
  unfold JointVerd lam
  exact modalVerdX_of_queries h (fun i hi => hok _ (List.getElem_mem hi))

theorem dynVerd_of_groups {l q : ℕ} {pre : Bool} {gs : List (List (IForm n))}
    (h : dynGroups p n cX cov l q pre = some gs) (hok : GroupsOK gs)
    (hd : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true) :
    DynVerd p n cX cov l q pre := by
  unfold dynGroups at h
  rw [if_pos hd] at h
  rcases hq : modalVerdDynXQueries p cX n (rowIdx p l)
      (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder)
      pre l q with _ | qs
  · rw [hq] at h; simp at h
  · rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    unfold DynVerd
    refine modalVerdDynX_of_queries hq (fun i hi => ?_)
    obtain ⟨a, ha, hz⟩ := hok [qs[i]] (List.mem_map.mpr ⟨qs[i], List.getElem_mem hi, rfl⟩)
    rw [List.mem_singleton] at ha; subst ha
    exact hz

theorem admVerd_of_groups {l : ℕ} {gs : List (List (IForm n))}
    (h : admGroups p n cov l = some gs) (hok : GroupsOK gs) :
    ∀ q < nR p, q ∉ admissibleOf p cov l → AdmVerd (vars p) n (rowOf p l) (mLof p l) (mRof p q) := by
  intro q hq hmem
  have hqmem : q ∈ (List.range (nR p)).filter (fun q => !(admissibleOf p cov l).contains q) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hq, by simpa using hmem⟩
  obtain ⟨g, hg, hgq⟩ := mapM_option_forall h q hqmem
  rcases hq' : admQueryOf (vars p) n (rowOf p l) (mLof p l) (mRof p q) with _ | a
  · rw [hq'] at hgq; simp at hgq
  · rw [hq'] at hgq
    simp only [Option.map_some, Option.some.injEq] at hgq
    obtain ⟨a', ha', hz⟩ := hok _ hg
    have ha'' : a' ∈ [a] := by first | (rw [← hgq] at ha'; exact ha') | (rw [hgq] at ha'; exact ha')
    rw [List.mem_singleton] at ha''; subst ha''
    exact ⟨_, hq', hz⟩

theorem handoffVerd_of_groups {m' : ℕ} {gs : List (List (IForm n))}
    (h : handoffGroups p n m' = some gs) (hok : GroupsOK gs) :
    ∀ t ∈ (nextL p).getD m' [], HandoffVerd p n (m', t) := by
  intro t ht
  obtain ⟨g, hg, hgt⟩ := mapM_option_forall h t ht
  rcases hq : Handoff.queryOf p n (m', t) with _ | a
  · rw [hq] at hgt; simp at hgt
  · rw [hq] at hgt
    simp only [Option.map_some, Option.some.injEq] at hgt
    obtain ⟨a', ha', hz⟩ := hok _ hg
    have ha'' : a' ∈ [a] := by first | (rw [← hgt] at ha'; exact ha') | (rw [hgt] at ha'; exact ha')
    rw [List.mem_singleton] at ha''; subst ha''
    exact ⟨_, hq, hz⟩

theorem progVerd_of_groups {c : ProgressE} {gs : List (List (IForm n))}
    (h : progGroups p n cX c = some gs) (hok : GroupsOK gs) : ProgressVerd p cX n c := by
  unfold progGroups at h
  rcases hq : progressQueriesOf p cX n (invRowOf p (modeIdx p.L.modes c.mL)) (modeIdx p.L.modes c.mL)
      (modeIdx p.R.modes c.mR) c with _ | qs
  · rw [hq] at h; simp at h
  · rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨qs, hq, fun q hq' => ?_⟩
    obtain ⟨a, ha, hz⟩ := hok [q] (List.mem_map.mpr ⟨q, hq', rfl⟩)
    rw [List.mem_singleton] at ha; subst ha
    exact hz

/-- **A green run is the `Verdicts` structure.** -/
theorem verdicts_of_groups {gs : List (List (IForm n))}
    (h : bridgeGroups p n cX cov prog = some gs) (hok : GroupsOK gs) :
    Verdicts p n cX cov prog := by
  unfold bridgeGroups at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at h
  obtain ⟨sL, hsL, sR, hsR, nc, hnc, jt, hjt, dy, hdy, ad, had, ho, hho, pr, hpr, rfl⟩ := h
  obtain ⟨h1, h8⟩ := groupsOK_append hok
  obtain ⟨h1, h7⟩ := groupsOK_append h1
  obtain ⟨h1, h6⟩ := groupsOK_append h1
  obtain ⟨h1, h5⟩ := groupsOK_append h1
  obtain ⟨h1, h4⟩ := groupsOK_append h1
  obtain ⟨h1, h3⟩ := groupsOK_append h1
  obtain ⟨h1, h2⟩ := groupsOK_append h1
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨g, hg, hgl⟩ := mapM_range hsL l hl
    exact stayVerd_of_groups hgl (groupsOK_flatten h1 _ hg)
  · intro q hq
    obtain ⟨g, hg, hgq⟩ := mapM_range hsR q hq
    exact stayVerd_of_groups hgq (groupsOK_flatten h2 _ hg)
  · intro q hq
    obtain ⟨g, hg, hgq⟩ := mapM_range hnc q hq
    exact nonConnVerd_of_groups hgq (groupsOK_flatten h3 _ hg)
  · intro l hl q hq hj
    obtain ⟨gl, hgl, hl'⟩ := mapM_range hjt l hl
    obtain ⟨g, hg, hq'⟩ := mapM_range hl' q hq
    exact jointVerd_of_groups hq' (groupsOK_flatten h4 _ (List.mem_flatten.mpr ⟨gl, hgl, hg⟩)) hj
  · intro l hl q hq pre hd
    obtain ⟨gl, hgl, hl'⟩ := mapM_range hdy l hl
    obtain ⟨gq, hgq, hq'⟩ := mapM_range hl' q hq
    obtain ⟨g, hg, hpre⟩ := mapM_option_forall hq' pre (by cases pre <;> simp)
    exact dynVerd_of_groups hpre
      (groupsOK_flatten h5 _ (List.mem_flatten.mpr ⟨gq, List.mem_flatten.mpr ⟨gl, hgl, hgq⟩, hg⟩)) hd
  · intro l hl q hq hmem
    obtain ⟨g, hg, hgl⟩ := mapM_range had l hl
    exact admVerd_of_groups hgl (groupsOK_flatten h6 _ hg) q hq hmem
  · intro m' hm' t ht
    obtain ⟨g, hg, hgm⟩ := mapM_range hho m' hm'
    exact handoffVerd_of_groups hgm (groupsOK_flatten h7 _ hg) t ht
  · intro c hc
    obtain ⟨g, hg, hgc⟩ := mapM_option_forall hpr c hc
    exact progVerd_of_groups hgc (groupsOK_flatten h8 _ hg)

end Link

end Emitted
end RelCertifier
