/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat3w_detumble_nominal`: Assumption 1 of the right model (style (a); the momentum band in the right evolve domain)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**The right evolve domain carries the momentum band `|h_i + J_i w_i| ≤ 2`** (the body's
momentum within the wheels' capacity, a constant of every design-model flow; since
2026-10-15). Without it `WellFormedR` would be false: the three
wheel momenta are bounded by the evolve domain (`|hᵢ| ≤ 2`) but driven by `DETUMBLE`
(`h₁' = w₁`, `h₂' = 2 w₂`, `h₃' = 2.5 w₃`, `w' = −w/2`), which conserves `h₁ + 2w₁`,
`h₂ + 4w₂`, `h₃ + 5w₃`. From `w₃ = 0.4`, `h₃ = 2`, the rest 0 (energy `0.8`, inside the
guard and the domain) no run of duration 1 exists: it would end at `h₃ = 4 − 2 e^{−1/2} > 2`
(clause (i) fails).

**With the band, Assumption 1 holds at every mode** (`sat3w_detumble_nominal_wellFormedR`, Z3-free), and
the band is kept by every mode's flow (`sat3w_detumble_nominal_band_invariant`): the active guard (`E ≤ 1`)
is forward invariant (each rate decays; style (a)); existence is the instance's explicit
solution `flowR_exists`, which stays in the domain because the conserved sums are constant.
`SAFE` (`E > 1`, frozen) holds still.
-/
import RelCertifier.InstancesV2.Modal.Sat3wDetumbleNominal
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Sat3wDetumbleNominal

open DL DLCalTiming DLRel Parse Set

theorem epsR_eq : epsR sat3w_detumble_nominal_IRv2 = 1 := by
  simp [epsR, sat3w_detumble_nominal_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vs 6 Side.R (mR q)

/-- The energy `E = 2 w1² + 4 w2² + 5 w3²`. -/
noncomputable def En (x : State (Var 6)) : ℝ :=
  x (Rv 0) * x (Rv 0) * 2 + x (Rv 1) * x (Rv 1) * 4 + x (Rv 2) * x (Rv 2) * 5

theorem sat_guardR0 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 0)) x ↔ En x ≤ 1 := by
  simp [hostGuard, mR, sat3w_detumble_nominal_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem sat_guardR1 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 1)) x ↔ 1 < En x := by
  simp [hostGuard, mR, sat3w_detumble_nominal_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem hp0' : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fR_safe (i : Fin 6) (x : State (Var 6)) : Term.eval (fR 1 i) x = 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mR, sat3w_detumble_nominal_IRv2, vs, Run.dynOf, Run.lowerE, hp0',
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem memR (q : ℕ) (i : Fin 6) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys := rightBlock_mem' _ _ i

theorem detumble_En {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (modeW 0).sys (modeW 0).dom x t Φ) : En (Φ t) ≤ En x := by
  have d0 := H.decay_sq_le (memR 0 0) (1/2) (by norm_num)
    (fun s _ => by rw [eval_unit_mul, fR0_eval])
  have d1 := H.decay_sq_le (memR 0 1) (1/2) (by norm_num)
    (fun s _ => by rw [eval_unit_mul, fR1_eval])
  have d2 := H.decay_sq_le (memR 0 2) (1/2) (by norm_num)
    (fun s _ => by rw [eval_unit_mul, fR2_eval])
  simp only [En]; nlinarith

/-- The three conserved momenta along a `DETUMBLE` run. -/
theorem detumble_hw {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (modeW 0).sys (modeW 0).dom x t Φ) :
    (1 * Φ t (Rv 3) + 2 * Φ t (Rv 0) = 1 * x (Rv 3) + 2 * x (Rv 0)) ∧
    (1 * Φ t (Rv 4) + 4 * Φ t (Rv 1) = 1 * x (Rv 4) + 4 * x (Rv 1)) ∧
    (1 * Φ t (Rv 5) + 5 * Φ t (Rv 2) = 1 * x (Rv 5) + 5 * x (Rv 2)) :=
  ⟨H.affine_const (memR 0 3) (memR 0 0) 1 2
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR3_eval, fR0_eval]; ring),
   H.affine_const (memR 0 4) (memR 0 1) 1 4
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR4_eval, fR1_eval]; ring),
   H.affine_const (memR 0 5) (memR 0 2) 1 5
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR5_eval, fR2_eval]; ring)⟩

theorem safe_const {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (modeW 1).sys (modeW 1).dom x t Φ) (i : Fin 6) : Φ t (Rv i) = x (Rv i) :=
  H.const (memR 1 i) (fun s _ => by rw [eval_unit_mul, fR_safe])

/-- **The momentum band is invariant** under both modes' flows. -/
theorem sat3w_detumble_nominal_band_invariant : RegionInvariant Gr nbF := by
  intro q m hm x t Φ hx H
  obtain ⟨hq, rfl⟩ := Gr_modeAt_inv hm
  rw [sat_nbF] at hx ⊢
  simp only [and_assoc] at hx ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx
  interval_cases q
  · obtain ⟨c1, c2, c3⟩ := detumble_hw H
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · simp only [safe_const H]
    exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- **Assumption 1 for `sat3w_detumble_nominal`** (Z3-free): the evolve domain carries the
momentum band `|hᵢ + Jᵢ wᵢ| ≤ 2`, a constant of every design-model flow, so the explicit
solution stays in the domain for a full period. -/
theorem sat3w_detumble_nominal_wellFormedR :
    WellFormedR Gr guardR (epsR sat3w_detumble_nominal_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · refine ⟨?_, ?_⟩
    · obtain ⟨Φ, h0, hder, hmask, hdom⟩ := flowR_exists x hd 1 (by norm_num)
      exact ⟨Φ, ⟨by norm_num, h0, hder, hmask, hdom⟩⟩
    · intro t Φ _ H
      have := detumble_En H
      have hgx := (sat_guardR0 x).mp hg
      exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR0 _).mpr (by linarith)⟩
  · refine ⟨⟨_, const_sol fR_safe hd (r := 1) (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    have hgx := (sat_guardR1 x).mp hg
    have hE : En (Φ t) = En x := by
      simp only [En, safe_const H 0, safe_const H 1, safe_const H 2]
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR1 _).mpr (by rw [hE]; exact hgx)⟩

/-- The witness: `w3 = 0.4`, `h3 = 2`, every other variable 0. -/
noncomputable def xw : State (Var 6) := fun y =>
  if y = Rv 2 then 2/5 else if y = Rv 5 then 2 else 0

end V2Sat3wDetumbleNominal
end RelCertifier
