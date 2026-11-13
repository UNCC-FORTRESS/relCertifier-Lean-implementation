/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The queries of a benchmark at its strict rows, as one list of groups

The strict-invariant exhibits of Appendix B.1 (rows with strict atoms, Eq. (8) with `< 0`)
are pinned like the other instances (Appendix B.4).

`bridgeGroupsS` is `bridgeGroups` with the strict flow packs (`modalVerdXQueriesS`: a strict
component's group is [route A, route B]) and the strict handoff queries
(`Handoff.queryOfS`); every other group is the existing one. `verdictsS_of_groups` reads a
green run as `VerdictsS`, the hypothesis of `theorem3_keyed_strict_of_records`.
`bridgeGroupsS_eq_of_noStrict`: without strict atoms the strict run issues exactly the
existing queries.
-/
import RelCertifier.Proofs.Encoding.Emitted.Run
import RelCertifier.Proofs.Encoding.Emitted.StrictKeyed
import RelCertifier.VerdictsV2.ModalXStrict

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL Parse Run Oracle Bridge Progress Choice

variable {n : ℕ}

section BuildersS

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
  (prog : ProgressEmitE) (ce : ChoiceEmitE)

def jointGroupsS (k : Option ℕ) (l q : ℕ) : Option (List (List (IForm n))) :=
  if (flagsOf p cov l q).jointOK then
    modalVerdXQueriesS k p cX n (rowIdx p l) (strataOf p cov l q).order (lamQ p cov l q) l q
  else some []

def handoffGroupsS (m' : ℕ) : Option (List (List (IForm n))) :=
  ((nextL p).getD m' []).mapM (fun t => (Handoff.queryOfS p n (m', t)).map ([·]))

/-- The strict flow groups: the strict joint packs and the right-only packs, sliced at `k` hops
(the groups the SOS oracle may answer, `docs/SOS-ORACLE.md`). -/
def bridgeGroupsFlowS (k : Option ℕ) : Option (List (List (IForm n))) := do
  let jt ← (List.range (nL p)).mapM (fun l => (List.range (nR p)).mapM (jointGroupsS p n cX cov k l))
  let dy ← (List.range (nL p)).mapM (fun l => (List.range (nR p)).mapM (fun q =>
    [true, false].mapM (dynGroups p n cX cov prog k l q)))
  pure (jt.flatten.flatten ++ dy.flatten.flatten.flatten)

/-- The groups after the strict flow packs: admissibility, the strict handoffs, progress and
coverage (Z3 only). -/
def bridgeGroupsPostS : Option (List (List (IForm n))) := do
  let ad ← (List.range (nL p)).mapM (admGroups p n cov)
  let ho ← (List.range (nL p)).mapM (handoffGroupsS p n)
  let pr ← prog.certs.mapM (progGroups p n cX)
  let cv ← ce.entries.mapM (coverageGroups p n cX)
  pure (ad.flatten ++ ho.flatten ++ pr.flatten ++ cv.flatten)

/-- **Every query of the benchmark at its strict rows**, in groups (`bridgeGroups` with the
strict flow packs and the strict handoffs: `bridgeGroupsPre ++ bridgeGroupsFlowS ++
bridgeGroupsPostS`). -/
def bridgeGroupsS (k : Option ℕ) : Option (List (List (IForm n))) := do
  let a ← bridgeGroupsPre p n cX cov
  let f ← bridgeGroupsFlowS p n cX cov prog k
  let b ← bridgeGroupsPostS p n cX cov prog ce
  pure (a ++ f ++ b)

end BuildersS

/-! ## Reading a green strict run -/

section LinkS

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}
  {ce : ChoiceEmitE}

theorem jointVerdS_of_groups {O : UnsatOracle (Var n)} {k : Option ℕ} {l q : ℕ}
    {gs : List (List (IForm n))}
    (h : jointGroupsS p n cX cov k l q = some gs) (hok : GroupsOK gs O)
    (hj : (flagsOf p cov l q).jointOK = true) : JointVerdS p n cX cov l q O := by
  unfold jointGroupsS at h
  rw [if_pos hj] at h
  unfold JointVerdS lam
  exact modalVerdXS_of_queries h (fun i hi => hok _ (List.getElem_mem hi))

theorem handoffVerdS_of_groups {m' : ℕ} {gs : List (List (IForm n))}
    (h : handoffGroupsS p n m' = some gs) (hok : GroupsOK gs) :
    ∀ t ∈ (nextL p).getD m' [], HandoffVerdS p n (m', t) := by
  intro t ht
  obtain ⟨g, hg, hgt⟩ := mapM_option_forall h t ht
  rcases hq : Handoff.queryOfS p n (m', t) with _ | a
  · rw [hq] at hgt; simp at hgt
  · rw [hq] at hgt
    simp only [Option.map_some, Option.some.injEq] at hgt
    obtain ⟨a', ha', hz⟩ := hok _ hg
    have ha'' : a' ∈ [a] := by first | (rw [← hgt] at ha'; exact ha') | (rw [hgt] at ha'; exact ha')
    rw [List.mem_singleton] at ha''; subst ha''
    exact ⟨_, hq, hz⟩

/-- **A green strict run is the `VerdictsS` structure**, oracle-generic (the flow groups by `O`,
the rest by Z3). -/
theorem verdictsS_of_groups_O {O : UnsatOracle (Var n)} {k : Option ℕ}
    {gP gF gQ : List (List (IForm n))}
    (hP : bridgeGroupsPre p n cX cov = some gP) (hokP : GroupsOK gP)
    (hF : bridgeGroupsFlowS p n cX cov prog k = some gF) (hokF : GroupsOK gF O)
    (hQ : bridgeGroupsPostS p n cX cov prog ce = some gQ) (hokQ : GroupsOK gQ) :
    VerdictsS p n cX cov prog ce O := by
  unfold bridgeGroupsPre at hP
  unfold bridgeGroupsFlowS at hF
  unfold bridgeGroupsPostS at hQ
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at hP hF hQ
  obtain ⟨sL, hsL, sR, hsR, nc, hnc, rfl⟩ := hP
  obtain ⟨jt, hjt, dy, hdy, rfl⟩ := hF
  obtain ⟨ad, had, ho, hho, pr, hpr, cv, hcv, rfl⟩ := hQ
  obtain ⟨h1, h3⟩ := groupsOK_append hokP
  obtain ⟨h1, h2⟩ := groupsOK_append h1
  obtain ⟨h4, h5⟩ := groupsOK_append hokF
  obtain ⟨h6, h9⟩ := groupsOK_append hokQ
  obtain ⟨h6, h8⟩ := groupsOK_append h6
  obtain ⟨h6, h7⟩ := groupsOK_append h6
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    exact jointVerdS_of_groups hq' (groupsOK_flatten h4 _ (List.mem_flatten.mpr ⟨gl, hgl, hg⟩)) hj
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
    exact handoffVerdS_of_groups hgm (groupsOK_flatten h7 _ hg) t ht
  · intro c hc
    obtain ⟨g, hg, hgc⟩ := mapM_option_forall hpr c hc
    exact progVerd_of_groups hgc (groupsOK_flatten h8 _ hg)
  · intro e he
    obtain ⟨g, hg, hge⟩ := mapM_option_forall hcv e he
    exact coverageVerd_of_groups hge (groupsOK_flatten h9 _ hg)

/-- **A green strict run is the `VerdictsS` structure.** -/
theorem verdictsS_of_groups {k : Option ℕ} {gs : List (List (IForm n))}
    (h : bridgeGroupsS p n cX cov prog ce k = some gs) (hok : GroupsOK gs) :
    VerdictsS p n cX cov prog ce := by
  unfold bridgeGroupsS at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at h
  obtain ⟨gP, hP, gF, hF, gQ, hQ, rfl⟩ := h
  obtain ⟨hok', hokQ⟩ := groupsOK_append hok
  obtain ⟨hokP, hokF⟩ := groupsOK_append hok'
  exact verdictsS_of_groups_O hP hokP hF hokF hQ hokQ

/-- **A green tagged strict run** (`RELCERT_SOS_SECS` set): the flow groups by Z3 or the exact
SOS checker (`GroupsOKT`), the rest by Z3; `VerdictsS … anyOracle` holds. -/
theorem verdictsS_of_tagged {k : Option ℕ} {gP gF gQ : List (List (IForm n))}
    (hP : bridgeGroupsPre p n cX cov = some gP) (hokP : GroupsOK gP)
    (hF : bridgeGroupsFlowS p n cX cov prog k = some gF) (hokF : GroupsOKT gF)
    (hQ : bridgeGroupsPostS p n cX cov prog ce = some gQ) (hokQ : GroupsOK gQ) :
    VerdictsS p n cX cov prog ce anyOracle :=
  verdictsS_of_groups_O hP hokP hF (groupsOK_any_of_tagged hokF) hQ hokQ

end LinkS

/-! ## Collapse: without strict atoms, the existing queries -/

theorem jointGroupsS_eq {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE}
    (h : noStrictRows p n = true) (k : Option ℕ) (l q : ℕ) :
    jointGroupsS p n cX cov k l q = jointGroups p n cX cov k l q := by
  unfold jointGroupsS jointGroups
  split_ifs
  · refine modalVerdXQueriesS_eq_of_allFalse k p cX n _ _ _ l q ?_
    intro fs hfs
    have hm := maskOf_allFalse h l
    unfold maskOf rowOf vars at hm
    rwa [hostFlags_of_lower hfs] at hm
  · rfl

theorem handoffGroupsS_eq {p : PProblem} (h : noStrictRows p n = true) (m' : ℕ) :
    handoffGroupsS p n m' = handoffGroups p n m' := by
  unfold handoffGroupsS handoffGroups
  congr 1
  funext t
  congr 1
  unfold Handoff.queryOfS Handoff.queryOf
  simp only [Option.bind_eq_bind]
  rcases hS : Handoff.invRowOf p (p.L.modes.getD (m', t).1 ⟨"", [], .tt, .tt, []⟩) with _ | rS
  · rfl
  rcases hT : Handoff.invRowOf p (p.L.modes.getD (m', t).2 ⟨"", [], .tt, .tt, []⟩) with _ | rT
  · rfl
  simp only [Option.bind_some]
  exact Handoff.ihandoffQueryS_eq_of_allFalse _ _ _ _ _ _ _ (invRow_allFalse h hS)
    (invRow_allFalse h hT)

/-- **Without strict atoms the strict run issues exactly the existing queries.** -/
theorem bridgeGroupsS_eq_of_noStrict {p : PProblem} {cX : EvolStrengtheningX}
    {cov : CoverEmitE} {prog : ProgressEmitE} {ce : ChoiceEmitE}
    (h : noStrictRows p n = true) (k : Option ℕ) :
    bridgeGroupsS p n cX cov prog ce k = bridgeGroups p n cX cov prog ce k := by
  have hj : jointGroupsS p n cX cov = jointGroups p n cX cov := by
    funext k l q; exact jointGroupsS_eq h k l q
  have hh : handoffGroupsS p n = handoffGroups p n := by
    funext m'; exact handoffGroupsS_eq h m'
  unfold bridgeGroupsS bridgeGroups bridgeGroupsFlowS bridgeGroupsFlow bridgeGroupsPostS
    bridgeGroupsPost
  rw [hj, hh]

/-- **Theorem 3 at strict rows from a green strict run**: if the runner's groups
(`bridgeGroupsS`) are all discharged (`GroupsOK`), the kernel-decided record facts hold, and
Assumption 1 holds on a right region kept by every right flow, then the strict mode-keyed claim
`keyedClaimS` holds for every `dt ≤ ε_L`. -/
theorem theorem3_keyed_strict_of_run {p : PProblem} {cX : EvolStrengtheningX}
    {cov : CoverEmitE} {prog : ProgressEmitE} {ce : ChoiceEmitE}
    (hs : structOK p n cov cX = true) {k : Option ℕ} {gs : List (List (IForm n))}
    (hrun : bridgeGroupsS p n cX cov prog ce k = some gs) (hok : GroupsOK gs)
    (hpo : progOK p n cov prog = true) (hcovers : coversOK p n cov ce = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ Set.range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (a b c d : Fin n) (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hdc : d ≠ c) (dt : ℝ) (hdt : dt ≤ epsL p) :
    keyedClaimS p n cX cov reg a b c d dt :=
  theorem3_keyed_strict_of_records hs (verdictsS_of_groups hrun hok) hpo hcovers hregR hinv hwf
    a b c d hba hca hcb hda hdb hdc dt hdt

/-- **Theorem 3 at a strict one-row benchmark from a green strict run** (window form): the same
hypotheses as `theorem3_keyed_strict_of_run` plus `rowsSame`, concluding `windowClaimS`. -/
theorem theorem3_window_strict_of_run {p : PProblem} {cX : EvolStrengtheningX}
    {cov : CoverEmitE} {prog : ProgressEmitE} {ce : ChoiceEmitE}
    (hs : structOK p n cov cX = true) {k : Option ℕ} {gs : List (List (IForm n))}
    (hrun : bridgeGroupsS p n cX cov prog ce k = some gs) (hok : GroupsOK gs)
    (hpo : progOK p n cov prog = true) (hcovers : coversOK p n cov ce = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ Set.range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (hsame : rowsSame p = true) (a b d : Fin n) (hab : a ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (dt : ℝ)
    (hdt : dt ≤ epsL p) :
    windowClaimS p n cX cov reg a b d dt :=
  theorem3_window_strict_of_records hs (verdictsS_of_groups hrun hok) hpo hcovers hregR hinv hwf
    hsame a b d hab hda hdb dt hdt

end Emitted
end RelCertifier
