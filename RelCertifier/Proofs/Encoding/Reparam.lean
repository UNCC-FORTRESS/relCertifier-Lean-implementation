/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# L7 — time reparametrization of stretched right runs

23 of 46 benchmarks certify with some window's λ ≠ 1, and λ varies per window within
one benchmark, while the right automaton has ONE fixed system per mode. The bridge:
for a POSITIVE CONSTANT stretch, the run relation of the stretched right block equals
the run relation of any other positive stretch — `sem` existentially quantifies the
duration, and runs biject under linear time scaling. With it, the Theorem 3 statement
quantifies over the REAL (λ = 1) automaton and each window's coupling converts its
stretched piece — without it the statement would be about a λ-stretched automaton,
which is not even well-defined when λ differs per window.

New leaf (imports `EnvelopeChain` for `rightBlock` context); no upstream edits.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain

namespace RelCertifier
open DL Set

variable {n : ℕ}

/-- **Time reparametrization.** A run of the `c`-stretched right block is a run of the
`d`-stretched right block (`c, d > 0`): rescale time by `c/d`. -/
theorem sem_rightBlock_reparam {fR : Fin n → Term (Var n)} {dom : Formula (Var n)}
    {ν μ : State (Var n)} (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (h : Program.sem (Program.ode (rightBlock fR (Term.const c)) dom) ν μ) :
    Program.sem (Program.ode (rightBlock fR (Term.const d)) dom) ν μ := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  have hscale : ∀ u, 0 ≤ u → u ≤ r * c / d → d * u / c ∈ Set.Icc (0:ℝ) r := by
    intro u hu0 hu2
    constructor
    · positivity
    · rw [div_le_iff₀ hc]
      have h2 : d * u ≤ d * (r * c / d) := mul_le_mul_of_nonneg_left hu2 hd.le
      have h3 : d * (r * c / d) = r * c := by field_simp
      linarith
  refine ⟨r * c / d, fun u => Φ (d * u / c), by positivity, by
      simp [hΦ0], ?_, ?_, ?_, ?_⟩
  · show Φ (d * (r * c / d) / c) = μ
    rw [show d * (r * c / d) / c = r from by field_simp]
    exact hΦr
  · -- derivatives: chain rule under the linear scaling
    intro u hu p hp
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
    have hmem : ((Rv i, Term.binop AOp.mul (Term.const c) (fR i)) : Var n × Term (Var n))
        ∈ rightBlock fR (Term.const c) :=
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have hΦder := hder (d * u / c) (hscale u hu.1 hu.2) _ hmem
    have hσ : HasDerivWithinAt (fun v : ℝ => d * v / c) (d / c)
        (Set.Icc 0 (r * c / d)) u := by
      have hda : HasDerivAt (fun v : ℝ => d * v / c) (d / c) u := by
        simpa using ((hasDerivAt_id u).const_mul d).div_const c
      exact hda.hasDerivWithinAt
    have hmaps : Set.MapsTo (fun v : ℝ => d * v / c) (Set.Icc 0 (r * c / d))
        (Set.Icc 0 r) := fun v hv => hscale v hv.1 hv.2
    have hcomp := HasDerivWithinAt.scomp u hΦder hσ hmaps
    have hval : Term.eval (Term.binop AOp.mul (Term.const d) (fR i)) (Φ (d * u / c))
        = (d / c) * Term.eval (Term.binop AOp.mul (Term.const c) (fR i))
            (Φ (d * u / c)) := by
      simp only [Term.eval, AOp.interp]
      field_simp
    show HasDerivWithinAt (fun v => Φ (d * v / c) (Rv i)) _ _ u
    rw [hval]
    have hfun : (fun v => Φ (d * v / c) (Rv i))
        = (fun s => Φ s (Rv i)) ∘ fun v => d * v / c := rfl
    rw [hfun]
    exact hcomp
  · -- mask: same bound set
    intro u hu x hx
    refine hmask (d * u / c) (hscale u hu.1 hu.2) x ?_
    intro hb
    refine hx ?_
    simp only [ODESystem.bound, rightBlock, List.map_map, List.mem_map] at hb ⊢
    obtain ⟨i, hi, hie⟩ := hb
    exact ⟨i, hi, hie⟩
  · -- domain: pointwise transported
    intro u hu
    exact hdom (d * u / c) (hscale u hu.1 hu.2)

/-- The two-sided form: the stretched and real right blocks have the SAME runs. -/
theorem sem_rightBlock_reparam_iff {fR : Fin n → Term (Var n)} {dom : Formula (Var n)}
    {ν μ : State (Var n)} (c : ℝ) (hc : 0 < c) :
    Program.sem (Program.ode (rightBlock fR (Term.const c)) dom) ν μ ↔
      Program.sem (Program.ode (rightBlock fR (Term.const 1)) dom) ν μ :=
  ⟨sem_rightBlock_reparam c 1 hc one_pos, sem_rightBlock_reparam 1 c one_pos hc⟩

end RelCertifier
