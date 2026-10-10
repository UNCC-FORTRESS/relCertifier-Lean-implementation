/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_profiles`: Assumption 1 of the right model — PROVED (repaired model)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**`WellFormedR` holds** (`quad_light_profiles_wellFormedR`, Z3-free):

* `NORMAL`, `ECO`, `SPORT` (style (a)): the guard `0 ≤ w ≤ 3.2` (the climb controller's
  operating range up to the limiter threshold, the 2026-10-10 repair; it was `0 ≤ w ≤ 2.6`)
  is forward invariant under `w' = c − w²`, `c ∈ {3.6, 4, 4.4}` (barriers at both faces).
  Existence: the instance's viability route with the left held still, rescaled.
* `LIMIT` (`w > 3.2`, `w' = −2 w`, declared successors `[LIMIT, NORMAL]`: the limiter hands
  back to the NORMAL profile, `docs/SUITE-REDESIGN.md` §21): style (b). A run decays toward
  0 inside `[0, w₀] ⊆ [0, 3.5]`: it ends in `LIMIT`'s guard if above 3.2, else in `NORMAL`'s.

(Until 2026-10-10 `LIMIT`'s only successor was itself and the model was refuted here, from
`w = 3.3`: the run of duration 1 ends at `3.3 e^{−2} < 3.2`.)
-/
import RelCertifier.InstancesV2.Modal.QuadLightProfiles
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2QuadLightProfiles

open DL DLCalTiming DLRel Parse Set

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR quad_light_profiles_IRv2 = 1 := by
  simp [epsR, quad_light_profiles_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem sat_guardR0 (q : ℕ) (hq : q < 3) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 16/5 := by
  interval_cases q <;>
  simp [hostGuard, mR, quad_light_profiles_IRv2, Run.lowerF, Run.lowerE, hp00, hp32, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_guardR3 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 3)) ν ↔ 16/5 < ν (Rv 0) := by
  simp [hostGuard, mR, quad_light_profiles_IRv2, Run.lowerF, Run.lowerE, hp32, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem fR0_limit (x : State (Var 2)) : Term.eval (fR 3 0) x = 2 * (0 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem fR1_limit (x : State (Var 2)) : Term.eval (fR 3 1) x = 0 := by
  simp [fR, hostDyn, mR, quad_light_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 2)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- The instance's viability existence, with the left held still (`fL = 0`). -/
theorem es0 (q : ℕ) (hq : q < 3) (dt : ℝ) (hdt : 0 ≤ dt) (σ : State (Var 2))
    (hσ : Formula.sat domR σ) :
    HExistSegB (fun _ => Term.const 0) (fR q) (Term.const (lam 0)) Formula.tt domR dt σ := by
  have hR := (sat_domR σ).mp hσ
  refine HExistSegB_of_viability_stratified (fun _ => Term.const 0) (fR q)
    (Term.const (lam 0)) Formula.tt domR [faceLo, faceHi] [] [] 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fun _ => Term.const 0) _ hb
      obtain ⟨j, hj⟩ := faces_fv gT (by simpa using hgT) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro gT hgT x _ hface
      rcases List.mem_cons.mp hgT with rfl | hgT
      · exact hbndS_lo 0 q hq x hface
      · rw [List.mem_singleton] at hgT
        subst hgT
        exact hbndS_hi 0 q hq x hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro i hi; exact absurd hi (by simp))
    (by
      intro x hS _
      rw [sat_domR]
      exact faces_val x (fun gT hgT => hS gT (by simpa using hgT)))
    23 62 1 one_pos
    (fun ν0 h0 => hLip 0 q hq ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    (fun ν0 h0 => hfbnd 0 q hq ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    dt hdt σ
    (by
      intro gT hgT
      rcases List.mem_cons.mp hgT with rfl | hgT
      · simp only [faceLo, Term.eval, AOp.interp]; linarith [hR.1]
      · rw [List.mem_singleton] at hgT
        subst hgT
        simp only [faceHi, Term.eval, AOp.interp]; linarith [hR.2])
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))

/-- **Assumption 1 at `NORMAL`, `ECO`, `SPORT`** (style (a), Z3-free). -/
theorem quad_light_profiles_wellFormedR_modes (q : ℕ) (hq : q < 3) :
    WellFormedRMode Gr guardR (epsR quad_light_profiles_IRv2) q := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR0 q hq x).mp hg
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, H⟩ := exists_of_HExistSegB_zero (lam_pos 0) (es0 q hq (2/5) (by norm_num) x hd)
      (s := 2/5) (by norm_num) le_rfl
    rw [show (2/5 : ℝ) * lam 0 = 1 from by simp [lam]] at H
    exact ⟨Φ, H⟩
  · intro t Φ _ H
    have hf := fR0_eval q hq
    have hc := cRc_pos q hq
    have hc2 : cRc q ≤ 22/5 := cRc_le q hq
    have hup := H.coord_le_barrier 0 (16/5) (fun s _ hs => by
      rw [hf]; nlinarith) hgx.2
    have hlo := H.coord_ge_barrier 0 0 (fun s hs hs0 => by
      have := ((sat_domR s).mp hs).1
      rw [hf]; nlinarith) hgx.1
    exact ⟨edgeW q q, edge_mem q q (by interval_cases q <;> decide),
      (sat_guardR0 q hq _).mpr ⟨hlo, hup⟩⟩

/-- **Assumption 1 at `LIMIT`** (style (b)): the climb rate decays toward 0; every run of at
most one interval ends in `LIMIT`'s guard (`w > 3.2`) or in `NORMAL`'s (`0 ≤ w ≤ 3.2`). -/
theorem quad_light_profiles_wellFormedR_limit :
    WellFormedRMode Gr guardR (epsR quad_light_profiles_IRv2) 3 := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR3 x).mp hg
  have hdx := (sat_domR x).mp hd
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 2 0 (by norm_num) fR0_limit ?_ ?_ 1 (by norm_num)
    · intro i hi s
      match i, hi with
      | 1, _ => exact fR1_limit s
    · intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      rw [min_eq_right (by linarith)] at h1
      rw [max_eq_left (by linarith)] at h2
      exact ⟨h1, le_trans h2 hdx.2⟩
  · intro t Φ _ H
    have hmem : (Rv 0, Term.binop .mul (Term.const 1) (fR 3 0)) ∈ (modeW 3).sys :=
      rightBlock_mem' _ _ 0
    have hdn := H.linear_down hmem 2 0 (by norm_num)
      (fun s _ => by rw [eval_unit_mul, fR0_limit]) (by linarith)
    by_cases h3 : 16/5 < Φ t (Rv 0)
    · exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR3 _).mpr h3⟩
    · push_neg at h3
      exact ⟨edgeW 3 0, edge_mem 3 0 (by decide), (sat_guardR0 0 (by norm_num) _).mpr
        ⟨hdn.1, h3⟩⟩

/-- **`quad_light_profiles` satisfies Assumption 1** (every mode, Z3-free). -/
theorem quad_light_profiles_wellFormedR :
    WellFormedR Gr guardR (epsR quad_light_profiles_IRv2) := by
  intro q hq
  have hq4 : q < 4 := by simpa [Gr] using hq
  rcases (by omega : q < 3 ∨ q = 3) with h | rfl
  · exact quad_light_profiles_wellFormedR_modes q h
  · exact quad_light_profiles_wellFormedR_limit

end V2QuadLightProfiles
end RelCertifier
