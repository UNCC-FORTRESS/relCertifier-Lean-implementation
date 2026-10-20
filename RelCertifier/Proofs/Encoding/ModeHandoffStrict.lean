/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The mode-keyed handoff at strict rows (extension `strict-atoms`)

`ModeHandoff` is F-parametric (`hstep_modeKeyed` over `F : ℕ → Formula`), so the composed
theorem at strict rows is the existing one at `F l := FMS (row l)`. What is specialized to
the closure is the handoff hypothesis's discharge:

* in-kernel, `FM_mono` (nested rows) → `FMS_mono`: a target component may be strict only if
  the source carries it strict;
* by Z3, `handoff_of_unsat` → `handoff_of_unsatS` on the strict query
  (`Handoff.ihandoffQueryS`): the antecedent is the source row at its mask (it holds strictly
  at the switch), the negated target carries the target's mask, so the UNSAT gives the
  target's strict row (`handoff_FMS_of_unsatS`).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Encoding.StrictInv
import RelCertifier.Trusted.HandoffStrict

namespace RelCertifier
open DL Set

variable {n : ℕ}

/-- `FM_mono`, mask-selected: every target component is a source component, strict in the
source whenever it is strict in the target. -/
theorem FMS_mono {g₁ g₂ : Term (Var n)} {gs₁ gs₂ : List (Term (Var n))} {m₁ m₂ : List Bool}
    (hsub : ∀ c ∈ tagS (g₂ :: gs₂) m₂, ∃ b, (b, c.2) ∈ tagS (g₁ :: gs₁) m₁ ∧
      (c.1 = true → b = true)) {ν : State (Var n)}
    (h : Formula.sat (FMS g₁ gs₁ m₁) ν) : Formula.sat (FMS g₂ gs₂ m₂) ν := by
  rw [sat_FMS_iff] at h ⊢
  intro c hc
  obtain ⟨b, hb, himp⟩ := hsub c hc
  have hsrc := h _ hb
  rcases c with ⟨cb, c⟩
  cases cb
  · exact hsrc.le
  · rw [himp rfl] at hsrc; exact hsrc

/-- The flagged IR conjunction denotes the flagged components. -/
theorem sat_iinvConjS_toHost (comps : List (ITerm n)) (fs : List Bool) (base : IForm n)
    (σ : State (Var n)) :
    Formula.sat (Handoff.iinvConjS comps fs base).toHost σ ↔
      Formula.sat base.toHost σ ∧
        ∀ c ∈ tagS (comps.map ITerm.toHost) fs, HoldsAt c.1 c.2 σ := by
  induction comps generalizing fs base with
  | nil => simp [Handoff.iinvConjS]
  | cons g gs ih =>
      simp only [Handoff.iinvConjS]
      rw [ih]
      have hat : Formula.sat (IForm.cmp (if fs.headD false then CompOp.lt else CompOp.le) g
          (ITerm.rat 0)).toHost σ ↔ HoldsAt (fs.headD false) g.toHost σ := by
        cases fs.headD false <;>
          simp [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, HoldsAt]
      have hand : Formula.sat (IForm.and base (IForm.cmp
          (if fs.headD false then CompOp.lt else CompOp.le) g (ITerm.rat 0))).toHost σ ↔
          Formula.sat base.toHost σ ∧ HoldsAt (fs.headD false) g.toHost σ :=
        and_congr Iff.rfl hat
      rw [hand, List.map_cons, tagS_cons, List.forall_mem_cons]
      tauto

/-- **The strict handoff implication from a Z3 `unsat`.** The source enters at its own
mask, the conclusion is the target's flagged row. -/
theorem handoff_of_unsatS (cs ct : List (ITerm n)) (fs ft : List Bool) (eL gT eR : IForm n)
    (hz : z3solve (IForm.and (Handoff.iinvConjS cs fs (IForm.and (IForm.and eL gT) eR))
      (IForm.neg (Handoff.iinvConjS ct ft IForm.tt))).toHost = Verdict.unsat) :
    ∀ σ : State (Var n), (∀ c ∈ tagS (cs.map ITerm.toHost) fs, HoldsAt c.1 c.2 σ) →
      Formula.sat eL.toHost σ → Formula.sat gT.toHost σ → Formula.sat eR.toHost σ →
      ∀ c ∈ tagS (ct.map ITerm.toHost) ft, HoldsAt c.1 c.2 σ := by
  intro σ hsrc heL hg heR
  by_contra hneg
  apply z3_unsat_sound hz σ
  refine ⟨(sat_iinvConjS_toHost cs fs _ σ).mpr ⟨⟨⟨heL, hg⟩, heR⟩, hsrc⟩, ?_⟩
  show ¬ Formula.sat (Handoff.iinvConjS ct ft IForm.tt).toHost σ
  rw [sat_iinvConjS_toHost]
  exact fun h => hneg h.2

/-- The strict handoff at the rows' formulas: the source's `FMS` row, the source evolve, the
target guard and the right evolve give the target's `FMS` row. -/
theorem handoff_FMS_of_unsatS (cs ct : List (ITerm n)) (fs ft : List Bool)
    (eL gT eR : IForm n)
    (hz : z3solve (IForm.and (Handoff.iinvConjS cs fs (IForm.and (IForm.and eL gT) eR))
      (IForm.neg (Handoff.iinvConjS ct ft IForm.tt))).toHost = Verdict.unsat)
    {gS gT' : Term (Var n)} {gsS gsT : List (Term (Var n))}
    (hS : gS :: gsS = cs.map ITerm.toHost) (hT : gT' :: gsT = ct.map ITerm.toHost) :
    ∀ σ : State (Var n), Formula.sat (FMS gS gsS fs) σ →
      Formula.sat eL.toHost σ → Formula.sat gT.toHost σ → Formula.sat eR.toHost σ →
      Formula.sat (FMS gT' gsT ft) σ := by
  intro σ hsrc heL hg heR
  rw [sat_FMS_iff, hS] at hsrc
  rw [sat_FMS_iff, hT]
  exact handoff_of_unsatS cs ct fs ft eL gT eR hz σ hsrc heL hg heR

/-- `ihandoffQueryS` unfolded: its pieces, when it lowers. -/
theorem ihandoffQueryS_eq {vars : List String}
    {invSrc evolveSrc guardT evolveR invTgt : Parse.PForm} {q : IForm n}
    (hq : Handoff.ihandoffQueryS vars n invSrc evolveSrc guardT evolveR invTgt = some q) :
    ∃ cs fs eL gT eR ct ft, Oracle.invComponents vars n invSrc = some cs ∧
      Oracle.invStrictFlags vars n invSrc = some fs ∧
      Run.lowerF vars n Side.L evolveSrc = some eL ∧
      Run.lowerF vars n Side.L guardT = some gT ∧
      Run.lowerF vars n Side.R evolveR = some eR ∧
      Oracle.invComponents vars n invTgt = some ct ∧
      Oracle.invStrictFlags vars n invTgt = some ft ∧
      q = IForm.and (Handoff.iinvConjS cs fs (IForm.and (IForm.and eL gT) eR))
        (IForm.neg (Handoff.iinvConjS ct ft IForm.tt)) := by
  unfold Handoff.ihandoffQueryS at hq
  rcases h1 : Oracle.invComponents vars n invSrc with _ | cs
  · rw [h1] at hq; simp at hq
  rcases h0 : Oracle.invStrictFlags vars n invSrc with _ | fs
  · rw [h1, h0] at hq; simp at hq
  rcases h2 : Run.lowerF vars n Side.L evolveSrc with _ | eL
  · rw [h1, h0, h2] at hq; simp at hq
  rcases h3 : Run.lowerF vars n Side.L guardT with _ | gT
  · rw [h1, h0, h2, h3] at hq; simp at hq
  rcases h4 : Run.lowerF vars n Side.R evolveR with _ | eR
  · rw [h1, h0, h2, h3, h4] at hq; simp at hq
  rcases h5 : Oracle.invComponents vars n invTgt with _ | ct
  · rw [h1, h0, h2, h3, h4, h5] at hq; simp at hq
  rcases h6 : Oracle.invStrictFlags vars n invTgt with _ | ft
  · rw [h1, h0, h2, h3, h4, h5, h6] at hq; simp at hq
  rw [h1, h0, h2, h3, h4, h5, h6] at hq
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hq
  exact ⟨cs, fs, eL, gT, eR, ct, ft, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hq.symm⟩

end RelCertifier
