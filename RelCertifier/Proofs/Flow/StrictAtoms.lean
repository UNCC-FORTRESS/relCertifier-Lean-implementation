/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Strict atoms: the flag-selected atom formula (extension `strict-atoms`)

A component `g` of an invariant row is read as `g ≤ 0` (`invLe`) or, when its flag is set
(the atom was strict, `Oracle.invStrictFlags`), as `g < 0` (`invLt`). `invAt b g` selects the
formula, `HoldsAt b g ω` its scalar meaning; `tagS` pairs a component list with its mask (a
missing flag is `false`), `foldAt` conjoins flagged atoms over a base. Lightweight base of
the strict layer (imports only `Core.Reify`), so the flow-level files can use it.

New leaf; no upstream edits.
-/
import RelCertifier.Core.Reify

namespace RelCertifier
open DL Set

variable {n : ℕ}

/-! ## The strict atom and the flag-selected atom -/

/-- The strict invariant `g < 0` as a `Formula`. -/
def invLt (g : Term (Var n)) : Formula (Var n) := Formula.cmp CompOp.lt g (Term.const 0)

@[simp] theorem sat_invLt (g : Term (Var n)) (ω : State (Var n)) :
    Formula.sat (invLt g) ω ↔ Term.eval g ω < 0 := by
  simp only [invLt, Formula.sat, CompOp.interp, Term.eval]

/-- The atom formula of a component selected by its flag. -/
def invAt : Bool → Term (Var n) → Formula (Var n)
  | true, g => invLt g
  | false, g => invLe g

/-- The scalar meaning of a flagged component. -/
def HoldsAt : Bool → Term (Var n) → State (Var n) → Prop
  | true, g, ω => Term.eval g ω < 0
  | false, g, ω => Term.eval g ω ≤ 0

@[simp] theorem invAt_false (g : Term (Var n)) : invAt false g = invLe g := rfl
@[simp] theorem invAt_true (g : Term (Var n)) : invAt true g = invLt g := rfl

theorem sat_invAt (b : Bool) (g : Term (Var n)) (ω : State (Var n)) :
    Formula.sat (invAt b g) ω ↔ HoldsAt b g ω := by
  cases b <;> simp [invAt, HoldsAt]

theorem HoldsAt.le {b : Bool} {g : Term (Var n)} {ω : State (Var n)} (h : HoldsAt b g ω) :
    Term.eval g ω ≤ 0 := by
  cases b
  · exact h
  · exact le_of_lt h

theorem holdsAt_false {g : Term (Var n)} {ω : State (Var n)} :
    HoldsAt false g ω ↔ Term.eval g ω ≤ 0 := Iff.rfl

theorem holdsAt_true {g : Term (Var n)} {ω : State (Var n)} :
    HoldsAt true g ω ↔ Term.eval g ω < 0 := Iff.rfl

theorem invAt_fv (b : Bool) (g : Term (Var n)) : (invAt b g).fv = (invLe g).fv := by
  cases b <;> rfl

/-! ## Components paired with their flags -/

/-- Each component with its flag (a missing flag is `false`). -/
def tagS : List (Term (Var n)) → List Bool → List (Bool × Term (Var n))
  | [], _ => []
  | c :: cs, m => (m.headD false, c) :: tagS cs m.tail

@[simp] theorem tagS_nil (m : List Bool) : tagS ([] : List (Term (Var n))) m = [] := rfl
@[simp] theorem tagS_cons (c : Term (Var n)) (cs : List (Term (Var n))) (m : List Bool) :
    tagS (c :: cs) m = (m.headD false, c) :: tagS cs m.tail := rfl

theorem tagS_map_snd (cs : List (Term (Var n))) (m : List Bool) :
    (tagS cs m).map Prod.snd = cs := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih => simp [ih]

theorem mem_tagS_snd {cs : List (Term (Var n))} {m : List Bool} {c : Bool × Term (Var n)}
    (h : c ∈ tagS cs m) : c.2 ∈ cs := by
  rw [← tagS_map_snd cs m]; exact List.mem_map_of_mem h

theorem exists_mem_tagS {cs : List (Term (Var n))} (m : List Bool) {g : Term (Var n)}
    (h : g ∈ cs) : ∃ b, (b, g) ∈ tagS cs m := by
  rw [← tagS_map_snd cs m] at h
  obtain ⟨⟨b, g'⟩, hm, rfl⟩ := List.mem_map.mp h
  exact ⟨b, hm⟩

/-- An all-false mask tags every component `false`. -/
theorem tagS_allFalse (cs : List (Term (Var n))) {m : List Bool} (h : ∀ b ∈ m, b = false) :
    tagS cs m = cs.map (fun c => (false, c)) := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih =>
      have hhd : m.headD false = false := by
        cases m with
        | nil => rfl
        | cons b bs => exact h b List.mem_cons_self
      have htl : ∀ b ∈ m.tail, b = false := fun b hb => h b (List.mem_of_mem_tail hb)
      rw [tagS_cons, hhd, ih htl]; rfl

theorem tagS_append (cs ts : List (Term (Var n))) (m : List Bool) :
    tagS (cs ++ ts) m = tagS cs m ++ tagS ts (m.drop cs.length) := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append, tagS_cons, ih, List.length_cons]
      congr 2
      cases m <;> simp

/-! ## Folds of flagged atoms -/

/-- The fold of flagged atoms over a base formula. -/
def foldAt (ts : List (Bool × Term (Var n))) (B : Formula (Var n)) : Formula (Var n) :=
  ts.foldr (fun c acc => Formula.and (invAt c.1 c.2) acc) B

theorem sat_foldAt (ts : List (Bool × Term (Var n))) (B : Formula (Var n))
    (ν : State (Var n)) :
    Formula.sat (foldAt ts B) ν ↔ (∀ c ∈ ts, HoldsAt c.1 c.2 ν) ∧ Formula.sat B ν := by
  induction ts with
  | nil => simp [foldAt]
  | cons c ts ih =>
      show Formula.sat (invAt c.1 c.2) ν ∧ Formula.sat (foldAt ts B) ν ↔ _
      rw [ih, sat_invAt, List.forall_mem_cons]
      tauto

theorem foldAt_fv (ts : List (Bool × Term (Var n))) (B : Formula (Var n)) :
    (foldAt ts B).fv =
      ((ts.map Prod.snd).foldr (fun g acc => Formula.and (invLe g) acc) B).fv := by
  induction ts with
  | nil => rfl
  | cons c ts ih =>
      show (invAt c.1 c.2).fv ∪ (foldAt ts B).fv = (invLe c.2).fv ∪ _
      rw [invAt_fv, ih]

end RelCertifier
