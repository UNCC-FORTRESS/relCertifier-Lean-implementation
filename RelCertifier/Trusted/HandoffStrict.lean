/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The strict handoff query (extension `strict-atoms`)

`ihandoffQuery` negates the target row's CLOSURE (`⋀ tgt ≤ 0`): an UNSAT gives the target
row's closure only. For a target row with strict atoms the negated conjunction must carry the
strictness: `iinvConjS` conjoins `g < 0` for a flagged component and `g ≤ 0` otherwise (the
mask `Oracle.invStrictFlags`). The ANTECEDENT is the source row at its own mask (`iinvConjS`): the source row
holds strictly at the switch (the loop invariant is `FMS`), and a pointwise implication has no
boundary-vacuity issue (unlike route B, whose boundary antecedent must stay the closure). With
the closure antecedent a strict row could never hand off to itself.

With an all-false target mask the strict query is the existing one
(`ihandoffQueryS_eq_of_allFalse`), so for every current benchmark (no strict atom) the
strings coincide. New leaf; `Handoff.lean` is untouched.
-/
import RelCertifier.Trusted.Handoff
import RelCertifier.Trusted.InvStrictFlags

namespace RelCertifier.Handoff

open RelCertifier RelCertifier.Parse RelCertifier.Run

/-- The flagged conjunction of components over a base (the `iinvConj` fold, `<` where the
flag is set). -/
def iinvConjS {n : ℕ} : List (ITerm n) → List Bool → IForm n → IForm n
  | [], _, base => base
  | g :: gs, fs, base =>
      iinvConjS gs fs.tail
        (IForm.and base (IForm.cmp (if fs.headD false then .lt else .le) g (.rat 0)))

/-- With an all-false mask, `iinvConjS` is `iinvConj`. -/
theorem iinvConjS_allFalse {n : ℕ} (comps : List (ITerm n)) {fs : List Bool}
    (h : ∀ b ∈ fs, b = false) (base : IForm n) :
    iinvConjS comps fs base = iinvConj comps base := by
  induction comps generalizing fs base with
  | nil => rfl
  | cons g gs ih =>
      have hhd : fs.headD false = false := by
        cases fs with
        | nil => rfl
        | cons b bs => exact h b List.mem_cons_self
      have htl : ∀ b ∈ fs.tail, b = false := fun b hb => h b (List.mem_of_mem_tail hb)
      simp only [iinvConjS, hhd, Bool.false_eq_true, if_false]
      rw [ih htl]
      rfl

/-- The strict handoff query: `(⋀ src ∼ 0 ∧ ((evolve_src ∧ guard_tgt) ∧ evolve_R)) ∧
¬(⋀ tgt ∼ 0)`, each `∼` per its row's strictness mask. -/
def ihandoffQueryS (vars : List String) (n : ℕ)
    (invSrc evolveSrc guardTgt evolveR invTgt : PForm) : Option (IForm n) := do
  let cs ← Oracle.invComponents vars n invSrc
  let fs ← Oracle.invStrictFlags vars n invSrc
  let eL ← lowerF vars n Side.L evolveSrc
  let gT ← lowerF vars n Side.L guardTgt
  let eR ← lowerF vars n Side.R evolveR
  let ct ← Oracle.invComponents vars n invTgt
  let ft ← Oracle.invStrictFlags vars n invTgt
  pure (IForm.and (iinvConjS cs fs (IForm.and (IForm.and eL gT) eR))
    (IForm.neg (iinvConjS ct ft IForm.tt)))

/-- The strict handoff query of one declared transition (`queryOf`, strict target). -/
def queryOfS (p : PProblem) (n : ℕ) (tr : ℕ × ℕ) : Option (IForm n) := do
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mSrc := p.L.modes.getD tr.1 dm
  let mTgt := p.L.modes.getD tr.2 dm
  let invSrc ← invRowOf p mSrc
  let invTgt ← invRowOf p mTgt
  ihandoffQueryS p.L.stateVars n invSrc mSrc.evolve mTgt.guard (evolveR p) invTgt

/-- **Collapse**: rows without strict atoms give the existing query. -/
theorem ihandoffQueryS_eq_of_allFalse (vars : List String) (n : ℕ)
    (invSrc evolveSrc guardTgt evolveR invTgt : PForm)
    (hfsrc : ∀ fs, Oracle.invStrictFlags vars n invSrc = some fs → ∀ b ∈ fs, b = false)
    (hft : ∀ fs, Oracle.invStrictFlags vars n invTgt = some fs → ∀ b ∈ fs, b = false) :
    ihandoffQueryS vars n invSrc evolveSrc guardTgt evolveR invTgt
      = ihandoffQuery vars n invSrc evolveSrc guardTgt evolveR invTgt := by
  unfold ihandoffQueryS ihandoffQuery
  rcases h1 : Oracle.invComponents vars n invSrc with _ | cs
  · rfl
  obtain ⟨fs0, hfs0, -⟩ := Oracle.invStrictFlags_length vars n invSrc cs h1
  simp only [hfs0, Option.bind_eq_bind, Option.bind_some]
  rcases h2 : lowerF vars n Side.L evolveSrc with _ | eL
  · rfl
  rcases h3 : lowerF vars n Side.L guardTgt with _ | gT
  · rfl
  rcases h4 : lowerF vars n Side.R evolveR with _ | eR
  · rfl
  rcases h5 : Oracle.invComponents vars n invTgt with _ | ct
  · rfl
  obtain ⟨fs, hfs, -⟩ := Oracle.invStrictFlags_length vars n invTgt ct h5
  simp [hfs, iinvConjS_allFalse ct (hft fs hfs), iinvConjS_allFalse cs (hfsrc fs0 hfs0)]

end RelCertifier.Handoff
