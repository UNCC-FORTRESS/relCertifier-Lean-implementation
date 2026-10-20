/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Strictness flags of the invariant components (leaf, extension `strict-atoms`)

`invComponents` lowers every atom of a row to a component `g` read as `g ≤ 0`: a strict atom
(`<`, `>`) lowers to the same `g` as its closure. `invStrictFlags` records, per component and
in the SAME flatten order, whether the atom it came from was strict. It mirrors
`invComponents` case by case (same lowering checks, same failure cases), so the two succeed
together and have the same length (`invStrictFlags_length`).

A new leaf: `invComponents` and every query string are untouched.
-/
import RelCertifier.Trusted.InvComponents

namespace RelCertifier.Oracle

open RelCertifier.Parse RelCertifier.Run

/-- The strictness mask of a row, aligned with `invComponents` (`true` = strict atom). -/
def invStrictFlags (vars : List String) (n : ℕ) : PForm → Option (List Bool)
  | .tt => some []
  | .cmp op a b =>
      if op == "<=" || op == "<" then do
        let _ ← lowerE vars n Side.L a; let _ ← lowerE vars n Side.L b
        some [op == "<"]
      else if op == ">=" || op == ">" then do
        let _ ← lowerE vars n Side.L a; let _ ← lowerE vars n Side.L b
        some [op == ">"]
      else none
  | .and x y => do
      let lx ← invStrictFlags vars n x; let ly ← invStrictFlags vars n y
      some (lx ++ ly)
  | _ => none

/-- The mask exists exactly when the components do, with the same length. -/
theorem invStrictFlags_length (vars : List String) (n : ℕ) :
    ∀ (f : PForm) (cs : List (ITerm n)), invComponents vars n f = some cs →
      ∃ fs, invStrictFlags vars n f = some fs ∧ fs.length = cs.length := by
  intro f
  induction f with
  | tt => intro cs h; simp [invComponents] at h; subst h; exact ⟨[], rfl, rfl⟩
  | cmp op a b =>
      intro cs h
      unfold invComponents at h
      unfold invStrictFlags
      split_ifs at h ⊢ with h1 h2
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨ea, hea, eb, heb, rfl⟩ := h
        exact ⟨[op == "<"], by simp [hea, heb], rfl⟩
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨ea, hea, eb, heb, rfl⟩ := h
        exact ⟨[op == ">"], by simp [hea, heb], rfl⟩
  | and x y ihx ihy =>
      intro cs h
      simp only [invComponents, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨lx, hlx, ly, hly, rfl⟩ := h
      obtain ⟨fx, hfx, hlenx⟩ := ihx lx hlx
      obtain ⟨fy, hfy, hleny⟩ := ihy ly hly
      exact ⟨fx ++ fy, by simp [invStrictFlags, hfx, hfy], by simp [hlenx, hleny]⟩
  | or x y _ _ => intro cs h; simp [invComponents] at h
  | not x _ => intro cs h; simp [invComponents] at h


/-- The mask and the components have the same length whenever either lowers (and fail
together). -/
theorem invStrictFlags_map_length (vars : List String) (n : ℕ) :
    ∀ (f : PForm), (invStrictFlags vars n f).map List.length =
      (invComponents vars n f).map List.length := by
  intro f
  induction f with
  | tt => rfl
  | cmp op a b =>
      unfold invComponents invStrictFlags
      split_ifs <;>
        rcases ha : lowerE vars n Side.L a with _ | ea <;>
        rcases hb : lowerE vars n Side.L b with _ | eb <;> simp [ha, hb]
  | and x y ihx ihy =>
      simp only [invComponents, invStrictFlags]
      rcases hfx : invStrictFlags vars n x with _ | fx <;>
        rcases hcx : invComponents vars n x with _ | cx <;>
        rcases hfy : invStrictFlags vars n y with _ | fy <;>
        rcases hcy : invComponents vars n y with _ | cy <;>
        simp_all
  | or x y _ _ => rfl
  | not x _ => rfl

end RelCertifier.Oracle
