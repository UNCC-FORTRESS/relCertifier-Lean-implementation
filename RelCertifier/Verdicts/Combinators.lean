/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Verdict-column combinators

The cut-instance hypotheses assemble their queries from lowered components with four
combinators: the three route queries (mirrors in `Smt.lean`/`CutLift.lean`/
`Mirrors.lean`), the stratified domain fold (`strataDomHost`), the cut fold (`cutF`),
and plain `and`/`cmp` (whose `toHost` distribution is definitional). This file supplies
the IR mirrors and `toHost` lemmas for the folds, plus the two constant identities
(zero field, unit stretch) every mirror file needs.
-/
import RelCertifier.Verdicts.Mirrors
import RelCertifier.Proofs.Flow.StratifiedBarrier
import RelCertifier.Proofs.Soundness.CutCover

namespace RelCertifier

open DL

/-- IR mirror of `strataDomHost` (domain narrowed by proven earlier strata). -/
def istrataDomHost {n : ℕ} (D : IForm n) (pre : List (ITerm n)) : IForm n :=
  pre.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) D

theorem istrataDomHost_toHost {n : ℕ} (D : IForm n) (pre : List (ITerm n)) :
    (istrataDomHost D pre).toHost = strataDomHost D.toHost (pre.map ITerm.toHost) := by
  induction pre generalizing D with
  | nil => rfl
  | cons g pre ih =>
      show (istrataDomHost (IForm.and D (IForm.cmp .le g (.rat 0))) pre).toHost = _
      rw [ih]
      show strataDomHost (Formula.and D.toHost
        (Formula.cmp .le g.toHost (Term.const ((0:ℚ):ℝ)))) _ = _
      have h0 : (Term.const (((0:ℚ):ℝ)) : Term (Var n)) = Term.const 0 := by norm_num
      rw [h0]
      rfl

/-- IR mirror of the instance-side cut fold (`cutF` over the atoms' formulas). -/
def icutF {n : ℕ} (atoms : List (IForm n)) : IForm n :=
  atoms.foldl (fun d a => IForm.and d a) IForm.tt

theorem icutF_toHost {n : ℕ} :
    ∀ (atoms : List (IForm n)) (hostAtoms : List (CutAtomP n)),
      hostAtoms.map Prod.fst = atoms.map IForm.toHost →
      ∀ (accI : IForm n) (accH : Formula (Var n)), accI.toHost = accH →
      (atoms.foldl (fun d a => IForm.and d a) accI).toHost
        = hostAtoms.foldl (fun d a => Formula.and d a.1) accH := by
  intro atoms
  induction atoms with
  | nil =>
      intro hostAtoms hlen accI accH hacc
      cases hostAtoms with
      | nil => simpa using hacc
      | cons a t => simp at hlen
  | cons aI atoms ih =>
      intro hostAtoms hlen accI accH hacc
      cases hostAtoms with
      | nil => simp at hlen
      | cons aH t =>
          simp only [List.map_cons, List.cons.injEq] at hlen
          simp only [List.foldl_cons]
          exact ih t hlen.2 _ _ (by
            show Formula.and accI.toHost aI.toHost = Formula.and accH aH.1
            rw [hacc, hlen.1])

theorem icutF_toHost' {n : ℕ} (atoms : List (IForm n)) (hostAtoms : List (CutAtomP n))
    (hlen : hostAtoms.map Prod.fst = atoms.map IForm.toHost) :
    (icutF atoms).toHost = cutF hostAtoms :=
  icutF_toHost atoms hostAtoms hlen IForm.tt Formula.tt rfl

/-- The zero field's mirror. -/
theorem zeroField_toHost {n : ℕ} :
    (fun _ : Fin n => (ITerm.rat 0 : ITerm n).toHost)
      = (fun _ => (Term.const 0 : Term (Var n))) := by
  funext i
  show Term.const ((0:ℚ):ℝ) = Term.const 0
  norm_num

/-- The unit stretch's mirror. -/
theorem oneConst_toHost {n : ℕ} :
    (ITerm.rat 1 : ITerm n).toHost = (Term.const 1 : Term (Var n)) := by
  show Term.const ((1:ℚ):ℝ) = Term.const 1
  norm_num

end RelCertifier
