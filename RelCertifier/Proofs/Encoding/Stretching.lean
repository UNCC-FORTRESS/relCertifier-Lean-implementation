/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Lemma 1 (Time Stretching), as stated in the paper

Paper (`lem:stretching`): for constant `λ ≥ 0`, `ξ` solves `x' = f(x)` on `[0, λt]` iff
`ζ(s) = ξ(λs)` solves `x' = λ f(x)` on `[0, t]`.

* `odeSol_stretch_iff` is that statement for an arbitrary ODE system (with its evolution
  domain, as `ODESol` carries it): `stretchSys λ sys` is `x' = λ f(x)`, every right-hand side
  multiplied by `Term.const λ`, exactly as `rightBlock` scales the right model.
* `odeSol_rightBlock_stretch_iff` is the same statement in the vocabulary of the chain: the
  real right model `rightBlock fR (Term.const 1)` on `[0, λt]` vs the stretched right block
  `rightBlock fR (Term.const λ)` on `[0, t]` (the hypothesis shape of `joint_of_sols_lam`).

`λ > 0`: chain rule both ways (`s ↦ λs` and its inverse `u ↦ u/λ`), the computation of
`sem_rightBlock_reparam`. `λ = 0`: `[0, λt]` is the point `{0}`, where every derivative claim
holds vacuously, and `ζ` is the constant `ξ 0`, a solution of `x' = 0·f(x)`; both sides
reduce to `ξ 0 = ω` and `ω` in the domain.

Related: `sem_rightBlock_reparam_iff` (`Reparam.lean`, `λ > 0`, the run relations of the
stretched and the real right block coincide) and `joint_of_sols_lam` (`SyncSwitch.lean`,
`λ ≥ 0`, the forward direction inside the joint-run construction used by Theorem 3).
-/
import RelCertifier.Proofs.Encoding.Reparam
import DLCalTiming.PlantT

namespace RelCertifier
open DL DLCalTiming Set

/-- The `λ`-stretched ODE system `x' = λ f(x)`: every right-hand side multiplied by the
constant `λ` (the scaling `rightBlock` applies to the right model). -/
def stretchSys {V : Type*} (lam : ℝ) (sys : ODESystem V) : ODESystem V :=
  sys.map (fun p => (p.1, Term.binop AOp.mul (Term.const lam) p.2))

/-- Stretching leaves the bound variables unchanged. -/
theorem stretchSys_bound {V : Type*} (lam : ℝ) (sys : ODESystem V) :
    (stretchSys lam sys).bound = sys.bound := by
  simp [stretchSys, ODESystem.bound, List.map_map, Function.comp_def]

/-- Membership in the stretched system: each equation is a stretched equation of `sys`. -/
theorem mem_stretchSys {V : Type*} {lam : ℝ} {sys : ODESystem V} {p : V × Term V}
    (hp : p ∈ stretchSys lam sys) :
    ∃ q ∈ sys, p = (q.1, Term.binop AOp.mul (Term.const lam) q.2) := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact ⟨q, hq, rfl⟩

/-- `{0}` has no accumulation point at `0`: any derivative claim within it holds. -/
private theorem hasDerivWithinAt_Icc_self_zero (f : ℝ → ℝ) (f' : ℝ) :
    HasDerivWithinAt f f' (Icc (0 : ℝ) 0) 0 := by
  have h : ¬AccPt (0 : ℝ) (Filter.principal (Icc (0 : ℝ) 0)) := by
    rw [accPt_principal_iff_nhdsWithin, Icc_self, sdiff_self, nhdsWithin_empty]
    exact fun hb => hb.ne rfl
  exact HasFDerivWithinAt.of_not_accPt h

/-- **Lemma 1 (Time Stretching).** For a constant `λ ≥ 0` (and `t ≥ 0`), `ξ` solves
`x' = f(x)` (with evolution domain `dom`, from `ω`) on `[0, λt]` iff `s ↦ ξ(λs)` solves
`x' = λ f(x)` on `[0, t]`. -/
theorem odeSol_stretch_iff {V : Type*} {sys : ODESystem V} {dom : Formula V} {ω : State V}
    {lam t : ℝ} {ξ : ℝ → State V} (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    ODESol sys dom ω (lam * t) ξ ↔
      ODESol (stretchSys lam sys) dom ω t (fun s => ξ (lam * s)) := by
  have hmaps : MapsTo (fun s : ℝ => lam * s) (Icc 0 t) (Icc 0 (lam * t)) :=
    fun s hs => ⟨mul_nonneg hlam hs.1, mul_le_mul_of_nonneg_left hs.2 hlam⟩
  constructor
  · -- `ζ = ξ ∘ (λ·)`: chain rule with the inner derivative `λ`
    intro H
    refine ⟨ht, by simpa using H.hΦ0, ?_, ?_, ?_⟩
    · intro s hs p hp
      obtain ⟨q, hq, rfl⟩ := mem_stretchSys hp
      have hσ : HasDerivWithinAt (fun s : ℝ => lam * s) lam (Icc 0 t) s := by
        simpa using ((hasDerivAt_id s).const_mul lam).hasDerivWithinAt
      have hcomp := HasDerivWithinAt.scomp s (H.hder (lam * s) (hmaps hs) q hq) hσ hmaps
      simp only [Term.eval, AOp.interp, smul_eq_mul] at hcomp ⊢
      exact hcomp
    · intro s hs x hx
      rw [stretchSys_bound] at hx
      exact H.hmask (lam * s) (hmaps hs) x hx
    · intro s hs
      exact H.hdom (lam * s) (hmaps hs)
  · intro H
    rcases hlam.eq_or_lt with hz | hpos
    · -- `λ = 0`: `[0, 0·t]` is a point; `ζ` is constant, so `ξ 0 = ω` and `ω ∈ dom`
      subst hz
      have h0 : ξ 0 = ω := by simpa using H.hΦ0
      have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_refl 0, ht⟩
      have hpt : ∀ u ∈ Icc (0 : ℝ) (0 * t), u = 0 := by
        intro u hu; rw [zero_mul] at hu; exact le_antisymm hu.2 hu.1
      refine ⟨by simp, h0, ?_, ?_, ?_⟩
      · intro u hu p _
        obtain rfl := hpt u hu
        rw [zero_mul]
        exact hasDerivWithinAt_Icc_self_zero _ _
      · intro u hu x _
        obtain rfl := hpt u hu
        rw [h0]
      · intro u hu
        obtain rfl := hpt u hu
        simpa using H.hdom 0 hmem0
    · -- `λ > 0`: `ξ = ζ ∘ (·/λ)`, chain rule with the inner derivative `1/λ`
      have hinv : MapsTo (fun u : ℝ => u / lam) (Icc 0 (lam * t)) (Icc 0 t) := by
        intro u hu
        refine ⟨div_nonneg hu.1 hpos.le, ?_⟩
        rw [div_le_iff₀ hpos, mul_comm]
        exact hu.2
      have hback : ∀ u, lam * (u / lam) = u := fun u => by field_simp
      refine ⟨mul_nonneg hlam ht, by simpa using H.hΦ0, ?_, ?_, ?_⟩
      · intro u hu q hq
        have hp : ((q.1, Term.binop AOp.mul (Term.const lam) q.2) : V × Term V)
            ∈ stretchSys lam sys := List.mem_map.mpr ⟨q, hq, rfl⟩
        have hd := H.hder (u / lam) (hinv hu) _ hp
        have hσ : HasDerivWithinAt (fun u : ℝ => u / lam) (1 / lam) (Icc 0 (lam * t)) u := by
          simpa using ((hasDerivAt_id u).div_const lam).hasDerivWithinAt
        have hcomp := HasDerivWithinAt.scomp u hd hσ hinv
        have hfun : (fun u => ξ u q.1) = (fun s => ξ (lam * s) q.1) ∘ fun u => u / lam := by
          funext v; simp only [Function.comp, hback]
        rw [hfun]
        refine hcomp.congr_deriv ?_
        simp only [Term.eval, AOp.interp, smul_eq_mul, hback]
        field_simp
      · intro u hu x hx
        rw [← stretchSys_bound lam sys] at hx
        have h := H.hmask (u / lam) (hinv hu) x hx
        simp only [hback] at h
        exact h
      · intro u hu
        have h := H.hdom (u / lam) (hinv hu)
        simp only [hback] at h
        exact h

/-- The stretched right block is the right model's vector field stretched by `λ`. -/
theorem rightBlock_const_eq_stretchSys {n : ℕ} (fR : Fin n → Term (Var n)) (lam : ℝ) :
    rightBlock fR (Term.const lam) =
      stretchSys lam ((List.finRange n).map fun i => (Rv i, fR i)) := by
  simp [rightBlock, stretchSys, List.map_map, Function.comp_def]

/-- **Lemma 1 (Time Stretching), in the chain's vocabulary.** For `λ ≥ 0` and `t ≥ 0`, `ξ`
solves the real right model `rightBlock fR (Term.const 1)` (domain `dom`) on `[0, λt]` iff
`s ↦ ξ(λs)` solves the stretched right block `rightBlock fR (Term.const λ)` on `[0, t]`. -/
theorem odeSol_rightBlock_stretch_iff {n : ℕ} {fR : Fin n → Term (Var n)}
    {dom : Formula (Var n)} {ω : State (Var n)} {lam t : ℝ} {ξ : ℝ → State (Var n)}
    (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    ODESol (rightBlock fR (Term.const 1)) dom ω (lam * t) ξ ↔
      ODESol (rightBlock fR (Term.const lam)) dom ω t (fun s => ξ (lam * s)) := by
  have h1 := odeSol_stretch_iff (sys := (List.finRange n).map fun i => (Rv i, fR i))
    (dom := dom) (ω := ω) (ξ := ξ) zero_le_one (mul_nonneg hlam ht)
  simp only [one_mul] at h1
  rw [rightBlock_const_eq_stretchSys, rightBlock_const_eq_stretchSys, ← h1]
  exact odeSol_stretch_iff hlam ht

end RelCertifier
