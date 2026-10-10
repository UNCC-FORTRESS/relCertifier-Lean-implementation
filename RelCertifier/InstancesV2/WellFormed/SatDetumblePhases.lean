/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_phases`: Assumption 1 of the right model — on the momentum band (style (c))

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**`WellFormedR` is false as stated** (`sat_detumble_phases_wellFormedR_false`): the wheel
momentum `h` is bounded by the evolve domain (`|h| ≤ 2`) but driven by `h' = 2.5 w3` in
`DETUMBLE`, and `h + 5 w3` is conserved by that flow. From `w1 = w2 = 0`, `w3 = 0.4`,
`h = 2` (energy `0.8`: inside `DETUMBLE`'s guard `2w1² + 4w2² + 5w3² ≤ 1`, inside the domain)
no run of duration 1 exists: it would end at `h = 4 − 2 e^{−1/2} > 2`, outside the domain
(clause (i) fails; the controller blocks). This is the model fact the Theorem 3 instance
already records (its region carries the nonblocking conjunct `nbF`).

**On the momentum band `nbF` (`−2 ≤ h + 5 w3 ≤ 2`) Assumption 1 holds**
(`sat_detumble_phases_wellFormedR_onBand`, Z3-free), and the band is invariant under every
mode's flow (`sat_detumble_phases_band_invariant`): `DETUMBLE`'s guard is forward invariant
(each rate decays, so the energy does not grow; style (a)); existence is the instance's
explicit solution `flowR_exists`, which needs exactly the band. `SAFE` (`E > 1`, frozen)
holds still.
-/
import RelCertifier.InstancesV2.Modal.SatDetumblePhases
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2SatDetumblePhases

open DL DLCalTiming DLRel Parse Set

theorem epsR_eq : epsR sat_detumble_phases_IRv2 = 1 := by
  simp [epsR, sat_detumble_phases_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 4) := hostGuard vs 4 Side.R (mR q)

/-- The energy `E = 2 w1² + 4 w2² + 5 w3²`. -/
noncomputable def En (x : State (Var 4)) : ℝ :=
  x (Rv 0) * x (Rv 0) * 2 + x (Rv 1) * x (Rv 1) * 4 + x (Rv 2) * x (Rv 2) * 5

theorem sat_guardR0 (x : State (Var 4)) :
    Formula.sat (hostGuard vs 4 Side.R (mR 0)) x ↔ En x ≤ 1 := by
  simp [hostGuard, mR, sat_detumble_phases_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem sat_guardR1 (x : State (Var 4)) :
    Formula.sat (hostGuard vs 4 Side.R (mR 1)) x ↔ 1 < En x := by
  simp [hostGuard, mR, sat_detumble_phases_IRv2, Run.lowerF, Run.lowerE, hp2, hp4, hp5, hp10,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, En]

theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fR_safe (i : Fin 4) (x : State (Var 4)) : Term.eval (fR 1 i) x = 0 := by
  fin_cases i <;>
    simp [fR, hostDyn, mR, sat_detumble_phases_IRv2, vs, Run.dynOf, Run.lowerE, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem memR (q : ℕ) (i : Fin 4) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys := rightBlock_mem' _ _ i

/-- Along any `DETUMBLE` run the energy does not grow. -/
theorem detumble_En {x : State (Var 4)} {t : ℝ} {Φ : ℝ → State (Var 4)}
    (H : ODESol (modeW 0).sys (modeW 0).dom x t Φ) : En (Φ t) ≤ En x := by
  have d0 := H.decay_sq_le (memR 0 0) (1/2) (by norm_num)
    (fun s _ => by rw [eval_unit_mul, fR0_eval])
  have d1 := H.decay_sq_le (memR 0 1) (1/2) (by norm_num)
    (fun s _ => by rw [eval_unit_mul, fR1_eval])
  have d2 := H.decay_sq_le (memR 0 2) (1/2) (by norm_num)
    (fun s _ => by rw [eval_unit_mul, fR2_eval])
  simp only [En]; nlinarith

/-- `h + 5 w3` is conserved along a `DETUMBLE` run. -/
theorem detumble_hw {x : State (Var 4)} {t : ℝ} {Φ : ℝ → State (Var 4)}
    (H : ODESol (modeW 0).sys (modeW 0).dom x t Φ) :
    1 * Φ t (Rv 3) + 5 * Φ t (Rv 2) = 1 * x (Rv 3) + 5 * x (Rv 2) :=
  H.affine_const (memR 0 3) (memR 0 2) 1 5
    (fun s _ => by rw [eval_unit_mul, eval_unit_mul, fR3_eval, fR2_eval]; ring)

theorem safe_const {x : State (Var 4)} {t : ℝ} {Φ : ℝ → State (Var 4)}
    (H : ODESol (modeW 1).sys (modeW 1).dom x t Φ) (i : Fin 4) : Φ t (Rv i) = x (Rv i) :=
  H.const (memR 1 i) (fun s _ => by rw [eval_unit_mul, fR_safe])

/-- **The momentum band is invariant** under both modes' flows. -/
theorem sat_detumble_phases_band_invariant : RegionInvariant Gr nbF := by
  intro q m hm x t Φ hx H
  obtain ⟨hq, rfl⟩ := Gr_modeAt_inv hm
  rw [sat_nbF] at hx ⊢
  interval_cases q
  · have := detumble_hw H; constructor <;> linarith [hx.1, hx.2]
  · rw [safe_const H 3, safe_const H 2]; exact hx

/-- **Assumption 1 for `sat_detumble_phases` on the momentum band** (Z3-free). -/
theorem sat_detumble_phases_wellFormedR_onBand :
    WellFormedRIn Gr guardR nbF (epsR sat_detumble_phases_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd hnb
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · refine ⟨?_, ?_⟩
    · obtain ⟨Φ, h0, hder, hmask, hdom⟩ := flowR_exists x hd hnb 1 (by norm_num)
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

/-- The witness: `w3 = 0.4`, `h = 2`, every other variable 0. -/
noncomputable def xw : State (Var 4) := fun y =>
  if y = Rv 2 then 2/5 else if y = Rv 3 then 2 else 0

/-- **Assumption 1 fails off the band**: from the witness (in `DETUMBLE`'s guard and the
evolve domain) no `DETUMBLE` run of duration 1 exists. -/
theorem sat_detumble_phases_detumble_blocks :
    ¬ WellFormedRMode Gr guardR (epsR sat_detumble_phases_IRv2) 0 := by
  rw [epsR_eq]
  refine not_wellFormedR_of_noRun (x := xw) (Gr_modeAt 0 (by norm_num)) ?_ ?_ ?_
  · show Formula.sat (hostGuard vs 4 Side.R (mR 0)) xw
    rw [sat_guardR0]; simp [En, xw, Rv]; norm_num
  · show Formula.sat domR xw
    rw [sat_domR]; simp [xw, Rv]; norm_num
  · intro Φ H
    have hc := detumble_hw H
    have hw := H.linear_exact (memR 0 2) (1/2) 0
      (fun s _ => by rw [eval_unit_mul, fR2_eval]; ring)
    have hend := (sat_domR _).mp H.end_dom
    have he : Real.exp (-(1/2 * 1)) < 1 := by
      rw [Real.exp_lt_one_iff]; norm_num
    simp [xw, Rv] at hc hw
    have h3 := hend.2
    rw [hw] at hc
    nlinarith

/-- **`sat_detumble_phases` violates Assumption 1 as stated** (the controller blocks at the
edge of the momentum band; see the module docstring). -/
theorem sat_detumble_phases_wellFormedR_false :
    ¬ WellFormedR Gr guardR (epsR sat_detumble_phases_IRv2) :=
  not_wellFormedR_of_mode (by simp [Gr]) sat_detumble_phases_detumble_blocks

end V2SatDetumblePhases
end RelCertifier
