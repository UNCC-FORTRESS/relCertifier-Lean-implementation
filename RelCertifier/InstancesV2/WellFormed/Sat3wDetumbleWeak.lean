/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat3w_detumble_weak`: Assumption 1 of the right model — on the momentum band (style (c))

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**`WellFormedR` is false as stated** (`sat3w_detumble_weak_wellFormedR_false`): the three
wheel momenta are bounded by the evolve domain (`|hᵢ| ≤ 2`) but driven by the three active
modes (`NOMINAL`, `ECONOMY`, `SURVIVAL`: `w' = −k w`, `h₁' = 2k w₁`, `h₂' = 4k w₂`,
`h₃' = 5k w₃`, `k = 0.5, 0.45, 0.42`), each of which conserves `h₁ + 2w₁`, `h₂ + 4w₂`,
`h₃ + 5w₃`. From `w₃ = 0.4`, `h₃ = 2`, the rest 0 (energy `0.8`, inside the
guard and the domain) no run of duration 1 exists: it would end at `h₃ = 4 − 2 e^{−1/2} > 2`
(clause (i) fails).

**On the momentum band `nbF` (the three conserved sums in `[−2, 2]`) Assumption 1 holds**
(`sat3w_detumble_weak_wellFormedR_onBand`, Z3-free) and the band is invariant under every
mode's flow (`sat3w_detumble_weak_band_invariant`): the active modes' common guard
(`E ≤ 1`) is forward invariant (each rate decays; style (a)); existence is the instance's explicit
solution `flowR_exists` on the band. `SAFE` (`E > 1`, frozen) holds still.
-/
import RelCertifier.InstancesV2.Modal.Sat3wDetumbleWeak
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Sat3wDetumbleWeak

open DL DLCalTiming DLRel Parse Set

theorem epsR_eq : epsR sat3w_detumble_weak_IRv2 = 1 := by
  simp [epsR, sat3w_detumble_weak_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vs 6 Side.R (mR q)

/-- The energy `E = 2 w1² + 4 w2² + 5 w3²`. -/
noncomputable def En (x : State (Var 6)) : ℝ :=
  x (Rv 0) * x (Rv 0) * 2 + x (Rv 1) * x (Rv 1) * 4 + x (Rv 2) * x (Rv 2) * 5

theorem sat_guardR0 (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR q)) x ↔ En x ≤ 1 := by
  interval_cases q <;>
  simp [hostGuard, mR, sat3w_detumble_weak_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem sat_guardR1 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 3)) x ↔ 1 < En x := by
  simp [hostGuard, mR, sat3w_detumble_weak_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem hp0' : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fR_safe (i : Fin 6) (x : State (Var 6)) : Term.eval (fR 3 i) x = 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mR, sat3w_detumble_weak_IRv2, vs, Run.dynOf, Run.lowerE, hp0',
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem memR (q : ℕ) (i : Fin 6) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys := rightBlock_mem' _ _ i

theorem detumble_En (q : ℕ) (hq : q < 3) {x : State (Var 6)} {t : ℝ}
    {Φ : ℝ → State (Var 6)} (H : ODESol (modeW q).sys (modeW q).dom x t Φ) :
    En (Φ t) ≤ En x := by
  have hk := kR_nonneg q
  have d0 := H.decay_sq_le (memR q 0) (kR q) hk (fun s _ => by rw [eval_unit_mul, fR0_eval q hq])
  have d1 := H.decay_sq_le (memR q 1) (kR q) hk (fun s _ => by rw [eval_unit_mul, fR1_eval q hq])
  have d2 := H.decay_sq_le (memR q 2) (kR q) hk (fun s _ => by rw [eval_unit_mul, fR2_eval q hq])
  simp only [En]; nlinarith

/-- The three conserved momenta along an active-mode run. -/
theorem detumble_hw (q : ℕ) (hq : q < 3) {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (modeW q).sys (modeW q).dom x t Φ) :
    (1 * Φ t (Rv 3) + 2 * Φ t (Rv 0) = 1 * x (Rv 3) + 2 * x (Rv 0)) ∧
    (1 * Φ t (Rv 4) + 4 * Φ t (Rv 1) = 1 * x (Rv 4) + 4 * x (Rv 1)) ∧
    (1 * Φ t (Rv 5) + 5 * Φ t (Rv 2) = 1 * x (Rv 5) + 5 * x (Rv 2)) :=
  ⟨H.affine_const (memR q 3) (memR q 0) 1 2
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR3_eval q hq, fR0_eval q hq]; ring),
   H.affine_const (memR q 4) (memR q 1) 1 4
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR4_eval q hq, fR1_eval q hq]; ring),
   H.affine_const (memR q 5) (memR q 2) 1 5
      (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR5_eval q hq, fR2_eval q hq]; ring)⟩

theorem safe_const {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (modeW 3).sys (modeW 3).dom x t Φ) (i : Fin 6) : Φ t (Rv i) = x (Rv i) :=
  H.const (memR 3 i) (fun s _ => by rw [eval_unit_mul, fR_safe])

/-- **The momentum band is invariant** under both modes' flows. -/
theorem sat3w_detumble_weak_band_invariant : RegionInvariant Gr nbF := by
  intro q m hm x t Φ hx H
  obtain ⟨hq, rfl⟩ := Gr_modeAt_inv hm
  rw [sat_nbF] at hx ⊢
  simp only [and_assoc] at hx ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx
  by_cases h3 : q < 3
  · obtain ⟨c1, c2, c3⟩ := detumble_hw q h3 H
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · obtain rfl : q = 3 := by omega
    simp only [safe_const H]
    exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- **Assumption 1 for `sat3w_detumble_weak` on the momentum band** (Z3-free). -/
theorem sat3w_detumble_weak_wellFormedR_onBand :
    WellFormedRIn Gr guardR nbF (epsR sat3w_detumble_weak_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd hnb
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  by_cases h3 : q < 3
  · refine ⟨?_, ?_⟩
    · obtain ⟨Φ, h0, hder, hmask, hdom⟩ := flowR_exists q h3 x hd hnb 1 (by norm_num)
      exact ⟨Φ, ⟨by norm_num, h0, hder, hmask, hdom⟩⟩
    · intro t Φ _ H
      have := detumble_En q h3 H
      have hgx := (sat_guardR0 q h3 x).mp hg
      exact ⟨edgeW q q, edge_mem q q (by interval_cases q <;> decide),
        (sat_guardR0 q h3 _).mpr (by linarith)⟩
  · obtain rfl : q = 3 := by omega
    refine ⟨⟨_, const_sol fR_safe hd (r := 1) (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    have hgx := (sat_guardR1 x).mp hg
    have hE : En (Φ t) = En x := by
      simp only [En, safe_const H 0, safe_const H 1, safe_const H 2]
    exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR1 _).mpr (by rw [hE]; exact hgx)⟩

/-- The witness: `w3 = 0.4`, `h3 = 2`, every other variable 0. -/
noncomputable def xw : State (Var 6) := fun y =>
  if y = Rv 2 then 2/5 else if y = Rv 5 then 2 else 0

/-- **Assumption 1 fails off the band**: from the witness no `NOMINAL` run of duration 1
exists. -/
theorem sat3w_detumble_weak_nominal_blocks :
    ¬ WellFormedRMode Gr guardR (epsR sat3w_detumble_weak_IRv2) 0 := by
  rw [epsR_eq]
  refine not_wellFormedR_of_noRun (x := xw) (Gr_modeAt 0 (by norm_num)) ?_ ?_ ?_
  · show Formula.sat (hostGuard vs 6 Side.R (mR 0)) xw
    rw [sat_guardR0 0 (by norm_num)]; simp [En, xw, Rv]; norm_num
  · show Formula.sat domR xw
    rw [sat_domR]; simp [xw, Rv]; norm_num
  · intro Φ H
    have hc := (detumble_hw 0 (by norm_num) H).2.2
    have hw := H.linear_exact (memR 0 2) (1/2) 0
      (fun s _ => by rw [eval_unit_mul, fR2_eval 0 (by norm_num)]; simp [kR])
    have hend := (sat_domR _).mp H.end_dom
    have he : Real.exp (-(1/2 * 1)) < 1 := by
      rw [Real.exp_lt_one_iff]; norm_num
    simp [xw, Rv] at hc hw
    have h5 : Φ 1 (Rv 5) ≤ 2 := by
      simp only [Rv] at hend ⊢; tauto
    rw [hw] at hc
    nlinarith

/-- **`sat3w_detumble_weak` violates Assumption 1 as stated** (the controller blocks at the
edge of the momentum band). -/
theorem sat3w_detumble_weak_wellFormedR_false :
    ¬ WellFormedR Gr guardR (epsR sat3w_detumble_weak_IRv2) :=
  not_wellFormedR_of_mode (by simp [Gr]) sat3w_detumble_weak_nominal_blocks

end V2Sat3wDetumbleWeak
end RelCertifier
