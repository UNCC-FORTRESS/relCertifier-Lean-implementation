/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_linkloss` — Theorem 3 over the GUARDED right automaton is FALSE (every `dt > 0`)

`V2Platoon3Linkloss.platoon3_linkloss_modeKeyed` proves the mode-keyed Theorem 3 over the
`⊤`-guarded right graph `Gr` at the cut region. This file states the strengthened statement —
the right automaton GUARDED (every edge tests the lowered guard of the mode it enters, `GrG`),
the loop invariant carrying the mode-consistent region `gregion q = guard q ∧ region q` — and
proves it false for every window length `dt > 0`: no legal witness exists.

**Why.** The deployed's `FOLLOW` row is the EXACT refinement up to the 1 m offset
(`Δr_i + ρ_j (Δg_i + 1) = 0` for both roots), so after a `FOLLOW` window the reference's state
is determined: `g_i^R = g_i^L + 1`, `r_i^R = r_i^L`, whatever the reference did. The left edge
tests its guard BEFORE the window (`?guard ; u_L := FOLLOW ; window`), so the deployed may leave
its guard box during the window; the reference's guard box is the deployed's shifted by 1, so
the determined reference state then lies outside `FOLLOW`'s guard, and the AEB sinks have the
empty region. Witness: the deployed at links `(33, 1)`, `(25, −1)`, `(29, 0)`, the reference at
`(34, 1)`, `(26, −1)`, `(30, 0)` in `FOLLOW`; a `FOLLOW` window of length `T = min(dt, 1)`
carries `g₁^L = 29 + 12 u − 8 u²` (`u = e^{−T/4} ∈ (1/2, 1)`) above 33, so `g₁^R > 34`.
-/
import RelCertifier.InstancesV2.Modal.Platoon3Linkloss
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Instances.GuardedPins

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Platoon3LinklossRefuted

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle V2Platoon3Linkloss GPins

/-! ## The guarded right automaton and the mode-consistent region -/

noncomputable def edgeG (s t : ℕ) : REdge (Var 6) :=
  { src := s, tgt := t, guard := hostGuard vs 6 Side.R (mR t), pruned := false }

noncomputable def GrG : SearchGraph (Var 6) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeG e.1 e.2) }

theorem GrG_len : GrG.modes.length = 4 := rfl

/-- The mode-consistent region: the right mode's lowered guard and its kept cut atoms. -/
noncomputable def gregion (q : ℕ) : Formula (Var 6) :=
  regionG (fun q => hostGuard vs 6 Side.R (mR q)) region q

/-! ## The `FOLLOW` row, evaluated -/

theorem comps0_eval (x : State (Var 6)) : (comps 0).map (fun c => Term.eval c x) =
    [x (Lv 1) - x (Rv 1) + 4⁻¹ * (x (Lv 0) - x (Rv 0) + 1),
      -(4⁻¹ * (x (Lv 0) - x (Rv 0) + 1)) + (x (Rv 1) - x (Lv 1)),
      x (Lv 1) - x (Rv 1) + 2⁻¹ * (x (Lv 0) - x (Rv 0) + 1),
      -(2⁻¹ * (x (Lv 0) - x (Rv 0) + 1)) + (x (Rv 1) - x (Lv 1)),
      x (Lv 3) - x (Rv 3) + 4⁻¹ * (x (Lv 2) - x (Rv 2) + 1),
      -(4⁻¹ * (x (Lv 2) - x (Rv 2) + 1)) + (x (Rv 3) - x (Lv 3)),
      x (Lv 3) - x (Rv 3) + 2⁻¹ * (x (Lv 2) - x (Rv 2) + 1),
      -(2⁻¹ * (x (Lv 2) - x (Rv 2) + 1)) + (x (Rv 3) - x (Lv 3)),
      x (Lv 5) - x (Rv 5) + 4⁻¹ * (x (Lv 4) - x (Rv 4) + 1),
      -(4⁻¹ * (x (Lv 4) - x (Rv 4) + 1)) + (x (Rv 5) - x (Lv 5)),
      x (Lv 5) - x (Rv 5) + 2⁻¹ * (x (Lv 4) - x (Rv 4) + 1),
      -(2⁻¹ * (x (Lv 4) - x (Rv 4) + 1)) + (x (Rv 5) - x (Lv 5))] := by
  have e1 : ("L_g1".drop 2).copy = "g1" := by decide
  have e2 : ("R_g1".drop 2).copy = "g1" := by decide
  have e3 : ("L_r1".drop 2).copy = "r1" := by decide
  have e4 : ("R_r1".drop 2).copy = "r1" := by decide
  have e5 : ("L_g2".drop 2).copy = "g2" := by decide
  have e6 : ("R_g2".drop 2).copy = "g2" := by decide
  have e7 : ("L_r2".drop 2).copy = "r2" := by decide
  have e8 : ("R_r2".drop 2).copy = "r2" := by decide
  have e9 : ("L_g3".drop 2).copy = "g3" := by decide
  have e10 : ("R_g3".drop 2).copy = "g3" := by decide
  have e11 : ("L_r3".drop 2).copy = "r3" := by decide
  have e12 : ("R_r3".drop 2).copy = "r3" := by decide
  simp [comps, hostComps, platoon3_linkloss_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    List.findIdx?_cons, hq0_0, hq1_0, hq0_25, hq0_5, hq5_0, hq1_5, hq3_0, hq6_0, ITerm.toHost,
    Term.eval, AOp.interp, Lv, Rv]

theorem eval_getD0 (i : ℕ) (x : State (Var 6)) :
    Term.eval ((comps 0).getD i c0) x = ((comps 0).map (fun c => Term.eval c x)).getD i 0 := by
  have h := List.getD_map (fun c => Term.eval c x) (l := comps 0) (n := i) (d := c0)
  simp only [c0, Term.eval] at h
  exact h.symm

theorem sat_canonInvM_bi (g' : Term (Var 6)) (gs' : List (Term (Var 6))) (a b : State (Var 6)) :
    RFormula.sat (canonInvM g' gs') (a, b) ↔
      ∀ c ∈ g' :: gs', Term.eval c (fun x => if x.1 = Side.R then b x else a x) ≤ 0 := by
  induction gs' with
  | nil => simp [canonInvM, sat_canonInv_bi]
  | cons h t ih =>
      show RFormula.sat (RFormula.and (canonInv h) (canonInvM g' t)) (a, b) ↔ _
      rw [RFormula.sat, sat_canonInv_bi, ih]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

/-! ## The witness and the deployed's `FOLLOW` window -/

/-- Deployed links `(33, 1)`, `(25, −1)`, `(29, 0)` in `FOLLOW` (`u_L = 0`); reference links
`(34, 1)`, `(26, −1)`, `(30, 0)` in `FOLLOW` (`mv = 0`); every other coordinate 0. -/
noncomputable def σ0 : State (Var 6) :=
  fun y => if y = Lv 0 then 33 else if y = Lv 1 then 1 else if y = Lv 2 then 25
    else if y = Lv 3 then -1 else if y = Lv 4 then 29
    else if y = Rv 0 then 34 else if y = Rv 1 then 1 else if y = Rv 2 then 26
    else if y = Rv 3 then -1 else if y = Rv 4 then 30 else 0

noncomputable def φL (t : ℝ) : Fin 6 → ℝ :=
  ![gS 29 33 1 t, rS 29 33 1 t, gS 29 25 (-1) t, rS 29 25 (-1) t, gS 29 29 0 t, rS 29 29 0 t]

theorem φL_0 (t : ℝ) : φL t 0 = gS 29 33 1 t := rfl
theorem φL_1 (t : ℝ) : φL t 1 = rS 29 33 1 t := rfl
theorem φL_5 (t : ℝ) : φL t 5 = rS 29 29 0 t := rfl

noncomputable def trajL (t : ℝ) : State (Var 6) :=
  fun y => if y.1 = Side.L then φL t y.2 else if y = tg then t else σ0 y

theorem trajL_L (t : ℝ) (i : Fin 6) : trajL t (Lv i) = φL t i := by simp [trajL, Lv]
theorem trajL_tg (t : ℝ) : trajL t tg = t := by simp [trajL]
theorem trajL_uL (t : ℝ) : trajL t uL = 0 := by simp [trajL, σ0, Lv, Rv]

theorem left_ode (T : ℝ) (hT : 0 ≤ T) :
    Program.sem (Program.ode (DLCalTiming.clk tg (leftBlock (fL 0))) domL)
      (Function.update σ0 tg 0) (trajL T) := by
  refine ⟨T, trajL, hT, ?_, rfl, ?_, ?_, ?_⟩
  · funext y
    obtain ⟨s, i⟩ := y
    cases s with
    | L =>
        rw [Function.update_of_ne (by simp [Prod.ext_iff])]
        show trajL 0 (Lv i) = σ0 (Lv i)
        rw [trajL_L]
        fin_cases i <;> simp [φL, gS_zero, rS_zero, σ0, Lv, Rv]
    | R =>
        rw [Function.update_of_ne (by simp [Prod.ext_iff])]
        simp [trajL]
    | Aux =>
        by_cases h : ((Side.Aux, i) : Var 6) = tg
        · rw [h, trajL_tg, Function.update_self]
        · rw [Function.update_of_ne h]; simp [trajL, h]
  · intro t ht p hp
    simp only [DLCalTiming.clk, leftBlock, List.mem_append, List.mem_map, List.mem_finRange,
      true_and, List.mem_singleton] at hp
    rcases hp with ⟨i, rfl⟩ | rfl
    · obtain ⟨f0, f1, f2, f3, f4, f5⟩ := fL_field0 (trajL t)
      fin_cases i
      · show HasDerivWithinAt (fun u => trajL u (Lv 0)) (Term.eval (fL 0 0) (trajL t)) _ t
        rw [f0]; simp only [trajL_L, φL]
        exact (gS_hasDeriv 29 33 1 t).hasDerivWithinAt
      · show HasDerivWithinAt (fun u => trajL u (Lv 1)) (Term.eval (fL 0 1) (trajL t)) _ t
        rw [f1]; simp only [trajL_L, φL]
        exact (rS_hasDeriv 29 33 1 t).hasDerivWithinAt
      · show HasDerivWithinAt (fun u => trajL u (Lv 2)) (Term.eval (fL 0 2) (trajL t)) _ t
        rw [f2]; simp only [trajL_L, φL]
        exact (gS_hasDeriv 29 25 (-1) t).hasDerivWithinAt
      · show HasDerivWithinAt (fun u => trajL u (Lv 3)) (Term.eval (fL 0 3) (trajL t)) _ t
        rw [f3]; simp only [trajL_L, φL]
        exact (rS_hasDeriv 29 25 (-1) t).hasDerivWithinAt
      · show HasDerivWithinAt (fun u => trajL u (Lv 4)) (Term.eval (fL 0 4) (trajL t)) _ t
        rw [f4]; simp only [trajL_L, φL]
        exact (gS_hasDeriv 29 29 0 t).hasDerivWithinAt
      · show HasDerivWithinAt (fun u => trajL u (Lv 5)) (Term.eval (fL 0 5) (trajL t)) _ t
        rw [f5]; simp only [trajL_L, φL]
        exact (rS_hasDeriv 29 29 0 t).hasDerivWithinAt
    · show HasDerivWithinAt (fun u => trajL u tg) (Term.eval (Term.const 1) (trajL t)) _ t
      simp only [Term.eval, trajL_tg]
      exact hasDerivWithinAt_id t _
  · intro t _ x hx
    have hxL : x.1 ≠ Side.L := by
      intro h
      obtain ⟨s, i⟩ := x
      simp only at h
      subst h
      exact hx (by simp [DLCalTiming.clk, ODESystem.bound, leftBlock, Lv])
    have hxtg : x ≠ tg := by
      rintro rfl; exact hx (by simp [DLCalTiming.clk, ODESystem.bound, leftBlock])
    rw [Function.update_of_ne hxtg]
    simp [trajL, hxL, hxtg]
  · intro t ht
    have a1 := E1_pos t
    have a2 := E2_pos t
    have b1 := E1_le t ht.1
    have b2 := E2_le t ht.1
    simp only [domL, hostEvolve, mL, platoon3_linkloss_IRv2, vs]
    simp [Run.lowerF, Run.lowerE, hq0_0, hq60_0, hqm10_0, hq10_0, Run.resolveVar,
      List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
      and_assoc]
    have h5 : φL t 5 = rS 29 29 0 t := rfl
    simp only [show ∀ i : Fin 6, ((Side.L, i) : Var 6) = Lv i from fun _ => rfl, trajL_L, h5]
    simp only [φL, gS, rS, Q1, Q2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]
    norm_num
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem sat_guardL0 : Formula.sat (hostGuard vs 6 Side.L (mL 0)) σ0 := by
  simp [hostGuard, mL, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, gp_25_0, gp_33_0,
    gp_m1_0, gp_1_0, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, σ0, Lv, Rv]
  norm_num

/-- One left step: from `FOLLOW`, the edge `FOLLOW → FOLLOW` (guard at `σ0`), the `FOLLOW`
window run for `T ≤ dt`. -/
theorem left_step (dt T : ℝ) (hT : 0 ≤ T) (hTdt : T ≤ dt) :
    Program.sem (leftAutomatonBody (A dt) uL) σ0 (trajL T) := by
  have hσuL : σ0 uL = 0 := by simp [σ0, Lv, Rv]
  refine Or.inl ⟨σ0, ⟨rfl, by simp [modeIs, Formula.sat, CompOp.interp, Term.eval, hσuL]⟩, ?_⟩
  rw [A_succ, nextL_eq]
  refine Or.inl ⟨σ0, ⟨rfl, ?_⟩, σ0, ?_, ?_⟩
  · rw [A_guard dt 0 (by norm_num)]; exact sat_guardL0
  · rw [sem_assign]
    exact ⟨by simp [Term.eval, hσuL], fun _ _ => rfl⟩
  · rw [A_window dt 0 (by norm_num)]
    refine ⟨σ0, ⟨rfl, sat_guardL0⟩, ?_⟩
    rw [sem_windowSeg_one]
    refine ⟨Function.update σ0 tg 0, ?_, trajL T, left_ode T hT, ?_⟩
    · exact ⟨by simp [Term.eval], fun y hy => Function.update_of_ne hy _ _⟩
    · exact ⟨rfl, by rw [sat_clkGuard, trajL_tg]; exact hTdt⟩

/-! ## The start and the refutation -/

theorem sat_rimp (a b : RFormula (Var 6)) (ω : BiState (Var 6)) :
    RFormula.sat (RFormula.imp a b) ω ↔ (RFormula.sat a ω → RFormula.sat b ω) := by
  simp only [RFormula.imp, RFormula.or, RFormula.sat]
  tauto

theorem guard_g1 (x : State (Var 6)) (h : Formula.sat (hostGuard vs 6 Side.R (mR 0)) x) :
    x (Rv 0) ≤ 34 := by
  simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, gp_26_0, gp_34_0,
    gp_m1_0, gp_1_0, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc] at h
  exact h.2.1

theorem sat_guardR0_σ0 : Formula.sat (hostGuard vs 6 Side.R (mR 0)) σ0 := by
  simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, gp_26_0, gp_34_0,
    gp_m1_0, gp_1_0, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, σ0, Lv, Rv]
  norm_num

theorem region0_σ0 : Formula.sat (region 0) σ0 := by
  rw [sat_region_lt 0 (by norm_num)]
  intro a ha
  refine (hiffR 0 (by norm_num) a ha σ0).mpr ?_
  have hmem : a.2 ∈ termsW Rv pR pR pR := by
    rw [← cR_terms0]; exact List.mem_map_of_mem ha
  have hall : ∀ t ∈ termsW Rv pR pR pR, Term.eval t σ0 ≤ 0 := by
    simp only [termsW, linT, derT, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    simp [linLe, linGe, linQ, thrLe, thrGe, Term.eval, AOp.interp, σ0, Lv, Rv, pR]
    norm_num
  exact hall _ hmem

theorem rows0_σ0 : RFormula.sat (ϕRow 0) (σ0, σ0) := by
  show RFormula.sat (canonInvM (g 0) (gs 0)) (σ0, σ0)
  rw [sat_canonInvM_bi]
  simp only [ite_self]
  have hall : ∀ i < 12, Term.eval ((comps 0).getD i c0) σ0 ≤ 0 := by
    intro i hi
    rw [eval_getD0, comps0_eval]
    interval_cases i <;> simp [σ0, Lv, Rv] <;> norm_num
  intro c hc
  simp only [g, gs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact hall _ (by norm_num)

/-- **The guarded mode-keyed Theorem 3 of `platoon3_linkloss` is false**: the statement of
`platoon3_linkloss_modeKeyed`, with the right automaton guarded and the loop invariant carrying
the mode-consistent region `gregion = guard ∧ region`, fails for every window length `dt > 0`. -/
theorem platoon3_linkloss_guarded_false (dt : ℝ) (hdt : 0 < dt) :
    ¬ RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody GrG mv)
      (psiK uL ϕRow (A dt).numModes domL domR
        (mvRegionR mv gregion GrG.modes.length))) := by
  intro hvalid
  have h := (RFormula_sat_imp _ _ (σ0, σ0)).mp (hvalid (σ0, σ0))
  have hpre : RFormula.sat (psiK uL ϕRow (A dt).numModes domL domR
      (mvRegionR mv gregion GrG.modes.length)) (σ0, σ0) := by
    rw [A_numModes]
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · -- the mode-keyed rows: `u_L = 0` (FOLLOW)
      refine ⟨(sat_rimp _ _ _).mpr (fun _ => rows0_σ0), (sat_rimp _ _ _).mpr (fun h1 => ?_),
        trivial⟩
      exfalso
      have : σ0 uL = 1 := by simpa [modeIs, Formula.sat, CompOp.interp, Term.eval] using h1
      simp [σ0, Lv, Rv] at this
    · show Formula.sat domL σ0
      simp only [domL, hostEvolve, mL, platoon3_linkloss_IRv2, vs]
      simp [Run.lowerF, Run.lowerE, hq0_0, hq60_0, hqm10_0, hq10_0, Run.resolveVar,
        List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
        σ0, Lv, Rv]
      norm_num
    · show Formula.sat domR σ0
      rw [sat_domR]; simp [Box, σ0, Lv, Rv]; norm_num
    · show Formula.sat (mvRegion mv gregion GrG.modes.length) σ0
      rw [sat_mvRegion]
      exact ⟨0, by simp [GrG], by simp [σ0, Lv, Rv],
        sat_regionG.mpr ⟨sat_guardR0_σ0, region0_σ0⟩⟩
    · show Formula.sat (mvValid uL 2) σ0
      rw [sat_mvValid]
      exact ⟨0, by norm_num, by simp [σ0, Lv, Rv]⟩
  have hfa := h hpre
  set T : ℝ := min dt 1 with hT
  have hT0 : 0 < T := lt_min hdt one_pos
  have hT1 : T ≤ 1 := min_le_right _ _
  have hTdt : T ≤ dt := min_le_left _ _
  have hleft : RProgram.sem (RProgram.biprog (Program.star (leftAutomatonBody (A dt) uL))
      (Program.test Formula.tt)) (σ0, σ0) (trajL T, σ0) := by
    refine ⟨Relation.ReflTransGen.single (left_step dt T hT0.le hTdt), rfl, trivial⟩
  have hdia := hfa (trajL T, σ0) hleft
  apply hdia
  rintro ⟨ωL, ωR⟩ ⟨hL, -⟩ hΦ
  obtain ⟨rfl, -⟩ := hL
  -- the reference's mode at the end, in its guard
  have hreg : Formula.sat (mvRegion mv gregion GrG.modes.length) ωR := hΦ.1.2
  rw [sat_mvRegion] at hreg
  obtain ⟨q, hq4, -, hgq⟩ := hreg
  have hgq' := sat_regionG.mp hgq
  by_cases hq1 : q < 1
  swap
  · exact not_sat_region_sink q hq1 ωR hgq'.2
  obtain rfl : q = 0 := by omega
  have hR34 := guard_g1 ωR hgq'.1
  -- the `FOLLOW` row at the end (`u_L = 0`)
  have hmk := hΦ.1.1.1
  rw [A_numModes] at hmk
  have hrow0 : RFormula.sat (ϕRow 0) (trajL T, ωR) :=
    (sat_rimp _ _ _).mp hmk.1 (by
      show Formula.sat (modeIs uL 0) (trajL T)
      simp [modeIs, Formula.sat, CompOp.interp, Term.eval, trajL_uL])
  have hrows := (sat_canonInvM_bi (g 0) (gs 0) (trajL T) ωR).mp hrow0
  have hr : ∀ i ∈ [0, 1, 2, 3], Term.eval ((comps 0).getD i c0)
      (fun x => if x.1 = Side.R then ωR x else trajL T x) ≤ 0 := by
    intro i hi
    apply hrows
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [g, gs, List.mem_cons, List.not_mem_nil, or_false]
    rcases hi with rfl | rfl | rfl | rfl <;> simp
  have r0 := hr 0 (by simp)
  have r1 := hr 1 (by simp)
  have r2 := hr 2 (by simp)
  have r3 := hr 3 (by simp)
  rw [eval_getD0, comps0_eval] at r0 r1 r2 r3
  simp only [List.getD_cons_zero, List.getD_cons_succ] at r0 r1 r2 r3
  have hLs : ∀ i : Fin 6, (Lv i : Var 6).1 = Side.L := fun _ => rfl
  have hRs : ∀ i : Fin 6, (Rv i : Var 6).1 = Side.R := fun _ => rfl
  simp only [hLs, hRs, if_true, reduceCtorEq, if_false] at r0 r1 r2 r3
  -- the rows pin `g₁^R = g₁^L + 1`
  have hpin : ωR (Rv 0) = trajL T (Lv 0) + 1 := by linarith
  -- and the deployed's `g₁` ends above 33
  have hgL : 33 < trajL T (Lv 0) := by
    rw [trajL_L, φL_0]
    simp only [gS, Q1, Q2]
    have hE1 : E1 T = E2 T * E2 T := by
      simp only [E1, E2]; rw [← Real.exp_add]; ring_nf
    have hu1 : E2 T < 1 := by
      simp only [E2]; rw [Real.exp_lt_one_iff]; linarith
    have hu2 : 3/4 ≤ E2 T := by
      simp only [E2]; have := Real.add_one_le_exp (-(1/4) * T); linarith
    rw [hE1]
    nlinarith
  linarith


end V2Platoon3LinklossRefuted
end RelCertifier
