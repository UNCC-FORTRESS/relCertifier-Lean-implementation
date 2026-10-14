/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Segment existence for constant fields that mirror the left

`WellFormedFlowB` asks for a domain-staying right run from EVERY domain state, which a constant
field violates at the domain edge it points to (`v' = −0.04` from `v = 0`). The choice exhibits
need less: the right copies the left (same constant field, unit stretch, equal coordinates at the
segment start), so the right run is the left run read on the right coordinates, and it stays in
the right domain because the left run stays in the left one. `hExistSegB_constMirror` is that
argument; it needs no bound on the duration.
-/
import RelCertifier.Proofs.Flow.WellFormedFlow
import RelCertifier.Proofs.Encoding.SyncSwitch

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- A coordinate whose field is the constant `c` is affine along a run. -/
theorem run_affine_coord {s c : ℝ} {Φ : ℝ → State (Var n)} {x : Var n}
    (hder : ∀ t ∈ Icc (0 : ℝ) s, HasDerivWithinAt (fun u => Φ u x) c (Icc 0 s) t) :
    ∀ t ∈ Icc (0 : ℝ) s, Φ t x = Φ 0 x + c * t := by
  have hg : ∀ t ∈ Icc (0 : ℝ) s,
      HasDerivWithinAt (fun u => Φ u x - c * u) 0 (Icc 0 s) t := by
    intro t ht
    have h2 : HasDerivWithinAt (fun u : ℝ => c * u) c (Icc 0 s) t := by
      simpa using ((hasDerivAt_id t).const_mul c).hasDerivWithinAt
    have h3 := (hder t ht).sub h2
    rw [sub_self] at h3
    exact h3
  have hdiffOn : DifferentiableOn ℝ (fun u => Φ u x - c * u) (Icc 0 s) :=
    fun t ht => (hg t ht).differentiableWithinAt
  have hd0 : ∀ t ∈ Ico (0 : ℝ) s, derivWithin (fun u => Φ u x - c * u) (Icc 0 s) t = 0 := by
    intro t ht
    have hlt : (0 : ℝ) < s := lt_of_le_of_lt ht.1 ht.2
    exact (hg t ⟨ht.1, le_of_lt ht.2⟩).derivWithin
      ((uniqueDiffOn_Icc hlt) t ⟨ht.1, le_of_lt ht.2⟩)
  intro t ht
  have := constant_of_derivWithin_zero hdiffOn hd0 t ht
  simp only [mul_zero, sub_zero] at this
  linarith

/-- **Mirror existence.** Both sides have the constant field `c` and the stretch evaluates to 1,
so the right moves by the same displacement as the left. If the right domain holds wherever the
right has moved from `ν` as the left has from `ν` (inside the left domain), the right run exists
for any duration and stays in its domain. -/
theorem hExistSegB_constMirror (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (dt : ℝ) (ν : State (Var n)) (c : Fin n → ℝ)
    (hfL : ∀ i x, (fL i).eval x = c i) (hfR : ∀ i x, (fR i).eval x = c i)
    (hlam : ∀ x, lam.eval x = 1)
    (hmirror : ∀ x y : State (Var n), (∀ i, y (Rv i) - ν (Rv i) = x (Lv i) - ν (Lv i)) →
      Formula.sat domL x → Formula.sat domR y) :
    HExistSegB fL fR lam domL domR dt ν := by
  intro s ΦL hs0 _ hΦL0 hderL hmaskL hdomL
  -- the left coordinates are affine
  have haff : ∀ i, ∀ t ∈ Icc (0 : ℝ) s, ΦL t (Lv i) = ν (Lv i) + c i * t := by
    intro i t ht
    have hmem : (Lv i, fL i) ∈ leftBlock fL := List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have := run_affine_coord (s := s) (c := c i) (Φ := ΦL) (x := Lv i)
      (fun t ht => by simpa [hfL] using hderL t ht _ hmem) t ht
    rw [this, hΦL0]
  -- the right coordinates are not moved by the left run
  have hRfix : ∀ i, ΦL s (Rv i) = ν (Rv i) := by
    intro i
    refine hmaskL s (right_mem_Icc.mpr hs0) (Rv i) ?_
    intro hb
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hb
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    exact absurd hpe (by simp [Lv, Rv, Prod.ext_iff])
  let ΦR : ℝ → State (Var n) := fun t x =>
    match x with
    | (Side.R, i) => ν (Rv i) + c i * t
    | x => ΦL s x
  have hΦR_R : ∀ t i, ΦR t (Rv i) = ν (Rv i) + c i * t := fun _ _ => rfl
  have hΦR_other : ∀ t x, x.1 ≠ Side.R → ΦR t x = ΦL s x := by
    intro t x hx
    rcases x with ⟨sd, i⟩
    cases sd
    · rfl
    · exact absurd rfl hx
    · rfl
  refine ⟨ΦR, ?_, ?_, ?_, ?_⟩
  · funext x
    rcases x with ⟨sd, i⟩
    cases sd
    · rfl
    · show ν (Rv i) + c i * 0 = ΦL s (Rv i)
      rw [hRfix]; ring
    · rfl
  · intro t _ p hp
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
    simp only [Term.eval, AOp.interp, hlam, hfR, one_mul]
    show HasDerivWithinAt (fun u => ν (Rv i) + c i * u) (c i) (Icc 0 s) t
    simpa using (((hasDerivAt_id t).const_mul (c i)).const_add (ν (Rv i))).hasDerivWithinAt
  · intro t _ x hx
    refine hΦR_other t x ?_
    intro hR
    rcases x with ⟨sd, i⟩
    simp only at hR
    subst hR
    exact hx (List.mem_map.mpr ⟨(Rv i, _), List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, rfl⟩)
  · intro t ht
    refine hmirror (ΦL t) (ΦR t) ?_ (hdomL t ht)
    intro i
    rw [hΦR_R, haff i t ht]; ring

/-- **Existence from the start alone.** The right field is the constant `c` at stretch 1; if the
right domain holds at every right translate `ν + c·t` with `0 ≤ t ≤ dt`, the right run exists
for every segment duration up to `dt`. -/
theorem hExistSegB_constRight (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (dt : ℝ) (ν : State (Var n)) (c : Fin n → ℝ)
    (hfR : ∀ i x, (fR i).eval x = c i) (hlam : ∀ x, lam.eval x = 1)
    (hdom : ∀ t, 0 ≤ t → t ≤ dt → ∀ y : State (Var n),
      (∀ i, y (Rv i) = ν (Rv i) + c i * t) → Formula.sat domR y) :
    HExistSegB fL fR lam domL domR dt ν := by
  intro s ΦL hs0 hsdt _ _ hmaskL _
  have hRfix : ∀ i, ΦL s (Rv i) = ν (Rv i) := by
    intro i
    refine hmaskL s (right_mem_Icc.mpr hs0) (Rv i) ?_
    intro hb
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hb
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    exact absurd hpe (by simp [Lv, Rv, Prod.ext_iff])
  let ΦR : ℝ → State (Var n) := fun t x =>
    match x with
    | (Side.R, i) => ν (Rv i) + c i * t
    | x => ΦL s x
  have hΦR_other : ∀ t x, x.1 ≠ Side.R → ΦR t x = ΦL s x := by
    intro t x hx
    rcases x with ⟨sd, i⟩
    cases sd
    · rfl
    · exact absurd rfl hx
    · rfl
  refine ⟨ΦR, ?_, ?_, ?_, ?_⟩
  · funext x
    rcases x with ⟨sd, i⟩
    cases sd
    · rfl
    · show ν (Rv i) + c i * 0 = ΦL s (Rv i)
      rw [hRfix]; ring
    · rfl
  · intro t _ p hp
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
    simp only [Term.eval, AOp.interp, hlam, hfR, one_mul]
    show HasDerivWithinAt (fun u => ν (Rv i) + c i * u) (c i) (Icc 0 s) t
    simpa using (((hasDerivAt_id t).const_mul (c i)).const_add (ν (Rv i))).hasDerivWithinAt
  · intro t _ x hx
    refine hΦR_other t x ?_
    intro hR
    rcases x with ⟨sd, i⟩
    simp only at hR
    subst hR
    exact hx (List.mem_map.mpr ⟨(Rv i, _), List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, rfl⟩)
  · intro t ht
    exact hdom t ht.1 (le_trans ht.2 hsdt) (ΦR t) (fun i => rfl)

/-- **The affine right run of a constant field.** From `ρ`, for duration `r`, if every right
translate `ρ + c·t` (`0 ≤ t ≤ r`) is in the domain. -/
theorem odeSol_constRight (fR : Fin n → Term (Var n)) (domR : Formula (Var n))
    (ρ : State (Var n)) (r : ℝ) (hr : 0 ≤ r) (c : Fin n → ℝ)
    (hfR : ∀ i x, (fR i).eval x = c i)
    (hdom : ∀ t, 0 ≤ t → t ≤ r → ∀ y : State (Var n),
      (∀ i, y (Rv i) = ρ (Rv i) + c i * t) → Formula.sat domR y) :
    ∃ Φ, ODESol (rightBlock fR (Term.const 1)) domR ρ r Φ := by
  let ΦR : ℝ → State (Var n) := fun t x =>
    match x with
    | (Side.R, i) => ρ (Rv i) + c i * t
    | x => ρ x
  have hΦR_other : ∀ t x, x.1 ≠ Side.R → ΦR t x = ρ x := by
    intro t x hx
    rcases x with ⟨sd, i⟩
    cases sd
    · rfl
    · exact absurd rfl hx
    · rfl
  refine ⟨ΦR, hr, ?_, ?_, ?_, ?_⟩
  · funext x
    rcases x with ⟨sd, i⟩
    cases sd
    · rfl
    · show ρ (Rv i) + c i * 0 = ρ (Rv i)
      ring
    · rfl
  · intro t _ p hp
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
    simp only [Term.eval, AOp.interp, hfR, one_mul]
    show HasDerivWithinAt (fun u => ρ (Rv i) + c i * u) (c i) (Icc 0 r) t
    simpa using (((hasDerivAt_id t).const_mul (c i)).const_add (ρ (Rv i))).hasDerivWithinAt
  · intro t _ x hx
    refine hΦR_other t x ?_
    intro hR
    rcases x with ⟨sd, i⟩
    simp only at hR
    subst hR
    exact hx (List.mem_map.mpr ⟨(Rv i, _), List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, rfl⟩)
  · intro t ht
    exact hdom t ht.1 ht.2 (ΦR t) (fun i => rfl)

end RelCertifier
