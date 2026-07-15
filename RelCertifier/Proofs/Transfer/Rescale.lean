/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The scaling-transfer lemma (seam #6): `GuardSettlingB` under state/time rescaling

The kernel settling certificates hold for the SCALED model (integer data: values ×σᵢ,
time in `dt`-units of `u` real seconds). The benchmark's own claim lives at real values
and real time. This file proves the transfer once and for all: if the scaled model's
per-mode settling obligation holds, so does the real one, PROVIDED the two sides
correspond — fields by the pushforward law `f(σ·x) = σᵢ·u·f'(x)` (exactly the
coefficient laws `Faithful` checks), guards/envelopes by satisfaction under the state
scaling. The witness flow transports by `Φ'(t) = σ⁻¹ · Φ(t/u)` (chain rule); staying and
landing transport pointwise. With `Faithful` (kernel, per benchmark) discharging the
correspondence numerically and this lemma discharging it analytically, the ×1000/w=u/2
"units" comments stop being trust-me math.
-/
import RelCertifier.Proofs.Soundness.GuardThreaded

namespace RelCertifier
open DL DLCalTiming DLRel Function Set

/-- Scale the RIGHT-side coordinates of a joint state by `σ` (L/Aux untouched). -/
def scaleState {n : ℕ} (σ : Fin n → ℝ) (ν : State (Var n)) : State (Var n) :=
  fun x => match x with
    | (Side.R, i) => σ i * ν (Side.R, i)
    | x => ν x

@[simp] theorem scaleState_R {n : ℕ} (σ : Fin n → ℝ) (ν : State (Var n)) (i : Fin n) :
    scaleState σ ν (Side.R, i) = σ i * ν (Side.R, i) := rfl

theorem scaleState_nonR {n : ℕ} (σ : Fin n → ℝ) (ν : State (Var n)) {x : Var n}
    (hx : ∀ i : Fin n, x ≠ (Side.R, i)) : scaleState σ ν x = ν x := by
  obtain ⟨sd, i⟩ := x
  cases sd with
  | R => exact absurd rfl (hx i)
  | L => rfl
  | Aux => rfl

/-- **Scaling transfer for the per-mode settling obligation.** `Gd'`/`domR'`/`fR'` are the
real-side guard map, envelope, and fields; the scaled side (`Gd`, `domR`, `fR`) satisfies
`GuardSettlingB` at the scaled duration `dts`, and the real side inherits it at the real
duration `u·dts`. Correspondence hypotheses:
* `hfield` — the pushforward law: evaluating the scaled field on a scaled state gives
  `σᵢ·u` times the real field on the raw state (`Faithful`'s coefficient conditions are
  precisely this law for the shape grammar);
* `hGd`, `hdom` — guard regions and envelope correspond under the state scaling. -/
theorem GuardSettlingB_rescale {n : ℕ} (G : SearchGraph (Var n))
    (Gd Gd' : ℕ → Formula (Var n)) (fR fR' : Fin n → Term (Var n))
    (domR domR' : Formula (Var n)) (σ : Fin n → ℝ) (u dts : ℝ) (q : ℕ)
    (hσ : ∀ i, σ i ≠ 0) (hu : 0 < u)
    (hfield : ∀ (i : Fin n) (ν : State (Var n)),
        Term.eval (fR i) (scaleState σ ν) = σ i * (u * Term.eval (fR' i) ν))
    (hGd : ∀ (q' : ℕ) (ν : State (Var n)),
        Formula.sat (Gd' q') ν ↔ Formula.sat (Gd q') (scaleState σ ν))
    (hdom : ∀ ν : State (Var n),
        Formula.sat domR' ν ↔ Formula.sat domR (scaleState σ ν))
    (hB : GuardSettlingB G Gd fR (Term.const 1) domR dts q) :
    GuardSettlingB G Gd' fR' (Term.const 1) domR' (u * dts) q := by
  intro base' hbase'
  obtain ⟨Φ, hΦ0, hderiv, hmask, hstay, q2, hq2, hland⟩ :=
    hB (scaleState σ base') ((hGd q base').mp hbase')
  -- the transported witness
  refine ⟨fun t => fun x => match x with
    | (Side.R, i) => (σ i)⁻¹ * Φ (t / u) (Side.R, i)
    | x => Φ (t / u) x, ?_, ?_, ?_, ?_, q2, hq2, ?_⟩
  case _ =>
    -- t = 0 recovers the base
    funext x
    obtain ⟨sd, i⟩ := x
    cases sd with
    | R =>
        show (σ i)⁻¹ * Φ (0 / u) (Side.R, i) = base' (Side.R, i)
        rw [zero_div, hΦ0, scaleState_R]
        have := hσ i
        field_simp
    | L => show Φ (0 / u) (Side.L, i) = base' (Side.L, i)
           rw [zero_div, hΦ0]; rfl
    | Aux => show Φ (0 / u) (Side.Aux, i) = base' (Side.Aux, i)
             rw [zero_div, hΦ0]; rfl
  case _ =>
    -- derivatives, by the chain rule and the pushforward law
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    have htu : t / u ∈ Icc (0 : ℝ) dts := by
      constructor
      · exact div_nonneg ht.1 hu.le
      · rw [div_le_iff₀ hu]
        calc t ≤ u * dts := ht.2
          _ = dts * u := by ring
    -- the scaled flow equals the scaling of the transported flow
    have hscale : ∀ s : ℝ, Φ s = scaleState σ (fun x => match x with
        | (Side.R, j) => (σ j)⁻¹ * Φ s (Side.R, j)
        | x => Φ s x) := by
      intro s
      funext x
      obtain ⟨sd, j⟩ := x
      cases sd with
      | R => show Φ s (Side.R, j) = σ j * ((σ j)⁻¹ * Φ s (Side.R, j))
             have := hσ j
             field_simp
      | L => rfl
      | Aux => rfl
    -- inner reparameterization t ↦ t/u
    have hinner : HasDerivWithinAt (fun t : ℝ => t / u) (1 / u) (Icc 0 (u * dts)) t :=
      (hasDerivAt_id t).div_const u |>.hasDerivWithinAt
    have houter := hderiv (t / u) htu ((Side.R, i),
      Term.binop .mul (Term.const 1) (fR i)) (by
        simp only [rightBlock, List.mem_map, List.mem_finRange]
        exact ⟨i, trivial, rfl⟩)
    have hmaps : MapsTo (fun t : ℝ => t / u) (Icc 0 (u * dts)) (Icc 0 dts) := by
      intro s hs
      constructor
      · exact div_nonneg hs.1 hu.le
      · rw [div_le_iff₀ hu]
        calc s ≤ u * dts := hs.2
          _ = dts * u := by ring
    have hcomp := HasDerivWithinAt.comp t houter hinner hmaps
    have h1 : HasDerivWithinAt (fun t : ℝ => (σ i)⁻¹ * Φ (t / u) (Side.R, i))
        ((σ i)⁻¹ * (Term.eval (Term.binop .mul (Term.const 1) (fR i)) (Φ (t / u))
          * (1 / u))) (Icc 0 (u * dts)) t := by
      have h := hcomp.const_mul ((σ i)⁻¹)
      simp only [Function.comp_def] at h
      push_cast at h
      convert h using 2
    -- rewrite the derivative value via the pushforward law
    have hval : (σ i)⁻¹ * (Term.eval (Term.binop .mul (Term.const 1) (fR i)) (Φ (t / u))
        * (1 / u))
        = Term.eval (Term.binop .mul (Term.const 1) (fR' i)) (fun x => match x with
            | (Side.R, j) => (σ j)⁻¹ * Φ (t / u) (Side.R, j)
            | x => Φ (t / u) x) := by
      have := hfield i (fun x => match x with
        | (Side.R, j) => (σ j)⁻¹ * Φ (t / u) (Side.R, j)
        | x => Φ (t / u) x)
      rw [← hscale (t / u)] at this
      simp only [Term.eval, AOp.interp] at this ⊢
      rw [this]
      have hσi := hσ i
      field_simp
      ring
    show HasDerivWithinAt (fun t : ℝ => (σ i)⁻¹ * Φ (t / u) (Side.R, i))
      (Term.eval (Term.binop .mul (Term.const 1) (fR' i)) (fun x => match x with
        | (Side.R, j) => (σ j)⁻¹ * Φ (t / u) (Side.R, j)
        | x => Φ (t / u) x)) (Icc 0 (u * dts)) t
    rw [← hval]
    push_cast
    exact h1
  case _ =>
    -- mask: non-bound coordinates frozen
    intro t ht x hx
    have hxR : ∀ i : Fin n, x ≠ (Side.R, i) := by
      intro i hxi
      exact hx (by
        rw [hxi]
        simp only [rightBlock, ODESystem.bound, List.map_map]
        exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    have htu : t / u ∈ Icc (0 : ℝ) dts := by
      constructor
      · exact div_nonneg ht.1 hu.le
      · rw [div_le_iff₀ hu]
        calc t ≤ u * dts := ht.2
          _ = dts * u := by ring
    have := hmask (t / u) htu x (by
      intro hmem
      simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map,
        List.mem_finRange] at hmem
      obtain ⟨i, -, rfl⟩ := hmem
      exact (hxR i) rfl)
    obtain ⟨sd, i⟩ := x
    cases sd with
    | R => exact absurd rfl (hxR i)
    | L =>
        show Φ (t / u) (Side.L, i) = base' (Side.L, i)
        rw [this]
        rfl
    | Aux =>
        show Φ (t / u) (Side.Aux, i) = base' (Side.Aux, i)
        rw [this]
        rfl
  case _ =>
    -- staying in the real envelope
    intro t ht
    have htu : t / u ∈ Icc (0 : ℝ) dts := by
      constructor
      · exact div_nonneg ht.1 hu.le
      · rw [div_le_iff₀ hu]
        calc t ≤ u * dts := ht.2
          _ = dts * u := by ring
    rw [hdom]
    have hscale : scaleState σ (fun x => match x with
        | (Side.R, j) => (σ j)⁻¹ * Φ (t / u) (Side.R, j)
        | x => Φ (t / u) x) = Φ (t / u) := by
      funext x
      obtain ⟨sd, j⟩ := x
      cases sd with
      | R => show σ j * ((σ j)⁻¹ * Φ (t / u) (Side.R, j)) = Φ (t / u) (Side.R, j)
             have := hσ j
             field_simp
      | L => rfl
      | Aux => rfl
    rw [hscale]
    exact hstay (t / u) htu
  case _ =>
    -- landing
    rw [hGd]
    have hdt : u * dts / u = dts := by field_simp
    have hscale : scaleState σ (fun x => match x with
        | (Side.R, j) => (σ j)⁻¹ * Φ (u * dts / u) (Side.R, j)
        | x => Φ (u * dts / u) x) = Φ dts := by
      rw [hdt]
      funext x
      obtain ⟨sd, j⟩ := x
      cases sd with
      | R => show σ j * ((σ j)⁻¹ * Φ dts (Side.R, j)) = Φ dts (Side.R, j)
             have := hσ j
             field_simp
      | L => rfl
      | Aux => rfl
    rw [hscale]
    exact hland

end RelCertifier
