/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_airframe_20`: Assumption 1 of the right model — FALSE (model defect)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**`WellFormedR` is false** (`quad_light_airframe_20_wellFormedR_false`): the sink `LIMIT`
(guard `w > 3`, flow `w' = −2 w`, declared successors `[LIMIT]` only) is left by its own
flow: from `w = 3.1` (inside the evolve domain `0 ≤ w ≤ 3.5`) the run of duration 1 ends at
`w = 3.1 e^{−2} < 3`, where no declared successor is enabled. (`LIMIT` is a pruned sink,
never entered by the Theorem 3 responses.)

**`CLIMB` satisfies Assumption 1** (`quad_light_airframe_20_wellFormedR_climb`, style (a),
Z3-free): the guard `0 ≤ w ≤ 2.6` is forward invariant under `w' = 4 − w²` (barriers at
both faces: `4 − w² ≤ 0` at `w ≥ 2.6`, `4 − w² ≥ 0` at `w = 0`). Existence: the instance's
viability route (both evolve faces strict, hand Lipschitz data), taken with the left held
still, and a time rescaling of the stretched run.
-/
import RelCertifier.InstancesV2.Modal.QuadLightAirframe20
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2QuadLightAirframe20

open DL DLCalTiming DLRel Parse Set

theorem hp30 : Run.parseRat "3.0" = some (3 : ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR quad_light_airframe_20_IRv2 = 1 := by
  simp [epsR, quad_light_airframe_20_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem sat_guardR0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 13/5 := by
  simp [hostGuard, mR, quad_light_airframe_20_IRv2, Run.lowerF, Run.lowerE, hp00, hp26, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_guardR1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔ 3 < ν (Rv 0) := by
  simp [hostGuard, mR, quad_light_airframe_20_IRv2, Run.lowerF, Run.lowerE, hp30, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem fR0_limit (x : State (Var 2)) : Term.eval (fR 1 0) x = 2 * (0 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, quad_light_airframe_20_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem fR1_limit (x : State (Var 2)) : Term.eval (fR 1 1) x = 0 := by
  simp [fR, hostDyn, mR, quad_light_airframe_20_IRv2, vs, Run.dynOf, Run.lowerE, hpm20,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 2)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- The instance's viability existence, with the left held still (`fL = 0`). -/
theorem es0 (dt : ℝ) (hdt : 0 ≤ dt) (σ : State (Var 2)) (hσ : Formula.sat domR σ) :
    HExistSegB (fun _ => Term.const 0) (fR 0) (Term.const (lam 0)) Formula.tt domR dt σ := by
  have hR := (sat_domR σ).mp hσ
  refine HExistSegB_of_viability_stratified (fun _ => Term.const 0) (fR 0)
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
      · exact hbndS_lo 0 0 (by norm_num) x hface
      · rw [List.mem_singleton] at hgT
        subst hgT
        exact hbndS_hi 0 0 (by norm_num) x hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro i hi; exact absurd hi (by simp))
    (by
      intro x hS _
      rw [sat_domR]
      exact faces_val x (fun gT hgT => hS gT (by simpa using hgT)))
    16 43 1 one_pos
    (fun ν0 h0 => hLip 0 0 (by norm_num) ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    (fun ν0 h0 => hfbnd 0 0 (by norm_num) ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
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

/-- **Assumption 1 at `CLIMB`** (style (a), Z3-free). -/
theorem quad_light_airframe_20_wellFormedR_climb :
    WellFormedRMode Gr guardR (epsR quad_light_airframe_20_IRv2) 0 := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR0 x).mp hg
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, H⟩ := exists_of_HExistSegB_zero (lam_pos 0) (es0 (4/7) (by norm_num) x hd)
      (s := 4/7) (by norm_num) le_rfl
    rw [show (4/7 : ℝ) * lam 0 = 1 from by simp [lam]] at H
    exact ⟨Φ, H⟩
  · intro t Φ _ H
    have hf := fR0_eval 0 (by norm_num)
    have hup := H.coord_le_barrier 0 (13/5) (fun s _ hs => by
      rw [hf]; simp only [cRc]; nlinarith) hgx.2
    have hlo := H.coord_ge_barrier 0 0 (fun s hs hs0 => by
      have := ((sat_domR s).mp hs).1
      rw [hf]; simp only [cRc]; nlinarith) hgx.1
    exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR0 _).mpr ⟨hlo, hup⟩⟩

/-- The witness state: `w = 3.1` (every other variable 0). -/
noncomputable def x31 : State (Var 2) := fun y => if y = Rv 0 then 31/10 else 0

/-- **Assumption 1 fails at `LIMIT`**: from `w = 3.1` the run of duration 1 ends at
`3.1 e^{−2} < 3`, outside `LIMIT`'s guard; `LIMIT`'s only declared successor is itself. -/
theorem quad_light_airframe_20_limit_blocks :
    ¬ WellFormedRMode Gr guardR (epsR quad_light_airframe_20_IRv2) 1 := by
  rw [epsR_eq]
  have he2 : Real.exp (-(2 * 1)) ≤ 1/3 := by
    have h := Real.add_one_le_exp 2
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at h ⊢; linarith
  have H : ODESol (rightBlock (fR 1) (Term.const 1)) domR x31 1
      (trajJ x31 0 (fun t => 0 + (x31 (Rv 0) - 0) * Real.exp (-(2 * t)))) :=
    trajJ_sol x31 0 _ 1 (by norm_num) (by simp)
      (fun t _ _ => by rw [fR0_limit]; simp only [trajJ_j]
                       exact hasDerivAt_expApproach 2 0 (x31 (Rv 0)) t)
      (fun i hi t _ _ => by
        match i, hi with
        | 1, _ => exact fR1_limit _)
      (fun t ht _ => by
        rw [sat_domR, trajJ_j]
        have h1 := Real.exp_pos (-(2 * t))
        have h2 : Real.exp (-(2 * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
        simp only [x31, if_true]
        constructor <;> nlinarith)
  refine not_wellFormedR_of_run (Gr_modeAt 1 (by norm_num)) ?_ ?_ le_rfl H ?_
  · show Formula.sat (hostGuard vs 2 Side.R (mR 1)) x31
    rw [sat_guardR1]; simp [x31]; norm_num
  · show Formula.sat domR x31
    rw [sat_domR]; simp [x31]; norm_num
  · intro e he hsat
    have hl := edgesFrom_list he
    have ht : e.tgt = 1 := by simp [edgeList] at hl; exact hl
    rw [ht] at hsat
    have := (sat_guardR1 _).mp hsat
    simp only [trajJ_j, x31, if_true] at this
    nlinarith

/-- **`quad_light_airframe_20` violates Assumption 1** (a model defect: the sink `LIMIT`
blocks). -/
theorem quad_light_airframe_20_wellFormedR_false :
    ¬ WellFormedR Gr guardR (epsR quad_light_airframe_20_IRv2) :=
  not_wellFormedR_of_mode (by simp [Gr]) quad_light_airframe_20_limit_blocks

end V2QuadLightAirframe20
end RelCertifier
