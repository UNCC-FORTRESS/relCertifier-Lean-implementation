/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_zones` (suite_v2) — the guarded Theorem 3 is FALSE as stated

`V2RoverPatrolZones.rover_patrol_zones_modeKeyed` proves the mode-keyed Theorem 3 over the
`⊤`-guarded right graph `Gr`. This file shows that the same statement over the GUARDED right
automaton (`GrG`: every edge tests the lowered guard of the mode it enters) is false for every
window length `dt > 0`.

The witness bi-state: the left in `SLOW` (`u_L = SLOW`) at `v_L = 0.35`, `s_L = 10`; the right
in `SLOW` (`mv = SLOW`) at `v_R = 0.35`, `s_R = 60`. The loop invariant holds there: the
`SLOW` row (`v_L ≤ v_R`, `s_L ≤ s_R + 0.5`), both envelopes, and `SLOW`'s region (its kept
cut atoms `s_R ≥ 0`, `0.3 ≤ v_R ≤ 0.6` — nothing bounds `s_R` above). Along `SLOW`'s flow
`s_R` does not decrease and `v_R` stays at least `0.35`, so none of `SLOW`'s successors is ever
enabled (`MEDIUM_ECO`, `MEDIUM_BRISK`: `s < 50`; `SLOW`: `s < 20`; `STALL`: `v < 0.2`): the
guarded right has no step. One iteration of the left automaton (`SLOW → SLOW`, the window run
for `dt`) raises `v_L` to `0.48 − 0.13 e^{−1.25 dt} > 0.35 = v_R`, breaking the `SLOW` row.
-/
import RelCertifier.InstancesV2.Modal.RoverPatrolZones
import RelCertifier.Proofs.Encoding.GuardedSwitch

namespace RelCertifier
namespace V2RoverPatrolZonesCounterexample

open DL DLCalTiming DLRel Parse Set V2RoverPatrolZones

set_option linter.unusedSimpArgs false

/-! ## The guarded right graph -/

noncomputable def edgeG (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The file's right automaton (the modes and `next` lists of `Gr`), guarded. -/
noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := Gr.modes, edges := edgeList.map (fun e => edgeG e.1 e.2) }

theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vs 3 Side.R (mR e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

theorem GrG_edges : GrG.edges.map (fun e => (e.src, e.tgt)) =
    Gr.edges.map (fun e => (e.src, e.tgt)) := by
  simp [GrG, Gr, edgeG, edgeW, List.map_map, Function.comp_def]

/-- Every successor of `SLOW` needs `s_R < 50` or `v_R < 0.2`. -/
theorem guard_blocked (t : ℕ) (ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 4) (x : State (Var 3))
    (hs : 50 ≤ x (Rv 1)) (hv : 1/5 ≤ x (Rv 0)) :
    ¬ Formula.sat (hostGuard vs 3 Side.R (mR t)) x := by
  intro h
  rcases ht with rfl | rfl | rfl | rfl <;>
  · simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
      hp03, hp06, hp09, hp11, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
      ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv] at h
    linarith [h]

/-! ## The right cannot move from `SLOW` at `s_R ≥ 50`, `v_R ≥ 0.2` -/

theorem no_step {σ μ : State (Var 3)} (hmv : σ mv = 0) (hs : 50 ≤ σ (Rv 1))
    (hv : 1/5 ≤ σ (Rv 0)) (_hvle : σ (Rv 0) ≤ 3/5)
    (h : Program.sem (rightAutomatonBody GrG mv) σ μ) : False := by
  obtain ⟨p, hp, hsem⟩ := bigChoiceP_sem_forward h
  simp only [List.mem_filterMap, List.mem_range] at hp
  obtain ⟨q, -, hqm⟩ := hp
  rcases hm : GrG.modeAt q with _ | m
  · rw [hm] at hqm; simp at hqm
  rw [hm] at hqm
  simp only [Option.map_some, Option.some.injEq] at hqm
  subst hqm
  obtain ⟨σ1, ⟨hσ1, htest⟩, κ, hflow, hedge⟩ := hsem
  subst hσ1
  have hq0 : q = 0 := by
    simp only [modeIs, Formula.sat, CompOp.interp, Term.eval] at htest
    rw [hmv] at htest
    exact_mod_cast htest.symm
  subst hq0
  have hm0 : m = modeW 0 := by simpa [SearchGraph.modeAt, GrG, Gr] using hm.symm
  subst hm0
  have hsκ : σ (Rv 1) ≤ κ (Rv 1) :=
    ode_coord_mono hflow (f := Term.binop .mul (Term.const 1) (fR 0 1))
      (List.mem_map.mpr ⟨1, List.mem_finRange 1, rfl⟩)
      (fun s hs' => by
        simp only [Term.eval, AOp.interp]
        rw [fR1_eval 0 (by norm_num)]
        have := ((sat_domR s).mp hs').1
        linarith)
  obtain ⟨r, hr, hvκ⟩ := ode_linear_coord hflow (x := Rv 0)
    (f := Term.binop .mul (Term.const 1) (fR 0 0))
    (List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩) 1 (3/5)
    (fun s _ => by
      simp only [Term.eval, AOp.interp]
      rw [fR0_eval 0 (by norm_num)]
      simp [capL, capQ])
  have he0 := Real.exp_pos (-(1 * r))
  have he1 : Real.exp (-(1 * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hvκ' : 1/5 ≤ κ (Rv 0) := by rw [hvκ]; nlinarith
  obtain ⟨p2, hp2, hsem2⟩ := bigChoiceP_sem_forward hedge
  simp only [List.mem_map] at hp2
  obtain ⟨e, he, rfl⟩ := hp2
  obtain ⟨κ1, ⟨hκ1, hg⟩, -⟩ := hsem2
  subst hκ1
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  have hsrc : e.src = 0 := by simpa using (List.mem_filter.mp he).2
  simp only [GrG, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  have hg' : Formula.sat (hostGuard vs 3 Side.R (mR p.2)) κ := hg
  have hsrc' : p.1 = 0 := hsrc
  have h50 : 50 ≤ κ (Rv 1) := by linarith
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact guard_blocked 1 (by norm_num) κ h50 hvκ' hg'
  · exact guard_blocked 2 (by norm_num) κ h50 hvκ' hg'
  · exact guard_blocked 0 (by norm_num) κ h50 hvκ' hg'
  · exact guard_blocked 4 (by norm_num) κ h50 hvκ' hg'
  all_goals exact absurd hsrc' (by norm_num)

theorem star_frozen {σ μ : State (Var 3)} (hmv : σ mv = 0) (hs : 50 ≤ σ (Rv 1))
    (hv : 1/5 ≤ σ (Rv 0)) (hvle : σ (Rv 0) ≤ 3/5)
    (h : Relation.ReflTransGen (Program.sem (rightAutomatonBody GrG mv)) σ μ) : μ = σ := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hstep, -⟩
  · exact h.symm
  · exact (no_step hmv hs hv hvle hstep).elim

/-! ## The left `SLOW` window, explicitly -/

/-- The witness state: left `v = 0.35`, `s = 10`, `u_L = SLOW`; right `v = 0.35`, `s = 60`,
`mv = SLOW`; every other coordinate 0. -/
noncomputable def σ0 : State (Var 3) :=
  fun y => if y = Lv 0 then 7/20 else if y = Lv 1 then 10 else if y = Rv 0 then 7/20
    else if y = Rv 1 then 60 else 0

noncomputable def traj (t : ℝ) : State (Var 3) :=
  fun y => if y = Lv 0 then 12/25 - 13/100 * Real.exp (-(5/4 * t))
    else if y = Lv 1 then 10 + 12/25 * t - 13/125 * (1 - Real.exp (-(5/4 * t)))
    else if y = tg then t else σ0 y

theorem tg_ne_L (i : Fin 3) : tg ≠ Lv i := by simp [Lv, Prod.ext_iff]

theorem traj_L0 (t : ℝ) : traj t (Lv 0) = 12/25 - 13/100 * Real.exp (-(5/4 * t)) := by
  simp [traj]
theorem traj_L1 (t : ℝ) :
    traj t (Lv 1) = 10 + 12/25 * t - 13/125 * (1 - Real.exp (-(5/4 * t))) := by
  simp [traj, show (Lv 1 : Var 3) ≠ Lv 0 from by simp [Lv, Prod.ext_iff]]
theorem traj_tg (t : ℝ) : traj t tg = t := by simp [traj, tg_ne_L]
theorem traj_other (t : ℝ) {y : Var 3} (h0 : y ≠ Lv 0) (h1 : y ≠ Lv 1) (h2 : y ≠ tg) :
    traj t y = σ0 y := by simp [traj, h0, h1, h2]

theorem fL0_2_eval (x : State (Var 3)) : Term.eval (fL 0 2) x = 0 := by
  simp [fL, hostDyn, mL, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp125, hp048,
    hp072, hp088, hp12, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Lv]

theorem left_ode (dt : ℝ) (hdt : 0 ≤ dt) :
    Program.sem (Program.ode (DLCalTiming.clk tg (leftBlock (fL 0))) domL)
      (Function.update σ0 tg 0) (traj dt) := by
  refine ⟨dt, traj, hdt, ?_, rfl, ?_, ?_, ?_⟩
  · funext y
    by_cases h0 : y = Lv 0
    · subst h0; simp [traj, σ0, tg_ne_L]; norm_num
    by_cases h1 : y = Lv 1
    · subst h1; simp [traj_L1, σ0, Function.update_of_ne (tg_ne_L 1).symm,
        show (Lv 1 : Var 3) ≠ Lv 0 from by simp [Lv, Prod.ext_iff]]
    by_cases h2 : y = tg
    · subst h2; simp [traj_tg]
    rw [traj_other 0 h0 h1 h2, Function.update_of_ne h2]
  · intro t ht p hp
    simp only [DLCalTiming.clk, leftBlock, List.mem_append, List.mem_map, List.mem_finRange,
      true_and, List.mem_singleton] at hp
    have hexp : HasDerivWithinAt (fun u : ℝ => Real.exp (-(5/4 * u)))
        (Real.exp (-(5/4 * t)) * (-(5/4 * 1))) (Icc 0 dt) t :=
      (((hasDerivAt_id t).const_mul (5/4)).neg.exp).hasDerivWithinAt
    rcases hp with ⟨i, rfl⟩ | rfl
    · fin_cases i
      · show HasDerivWithinAt (fun u => traj u (Lv 0)) (Term.eval (fL 0 0) (traj t)) _ t
        rw [fL0_eval 0 (by norm_num), traj_L0]
        have h := (hexp.const_mul (13/100)).const_sub (12/25)
        refine (h.congr (fun y _ => traj_L0 y) (traj_L0 t)).congr_deriv ?_
        simp [cLv, cLQ]; ring
      · show HasDerivWithinAt (fun u => traj u (Lv 1)) (Term.eval (fL 0 1) (traj t)) _ t
        rw [fL1_eval 0 (by norm_num), traj_L0]
        have hid := hasDerivWithinAt_id t (Icc (0:ℝ) dt)
        have h := ((hid.const_mul (12/25)).const_add 10).sub
          ((hexp.const_sub 1).const_mul (13/125))
        refine (h.congr (fun y _ => by rw [traj_L1]; simp) (by rw [traj_L1]; simp)).congr_deriv
          ?_
        simp; ring
      · show HasDerivWithinAt (fun u => traj u (Lv 2)) (Term.eval (fL 0 2) (traj t)) _ t
        rw [fL0_2_eval]
        have hL2 : ∀ u, traj u (Lv 2) = 0 := fun u => by
          rw [traj_other u (by simp [Lv, Prod.ext_iff]) (by simp [Lv, Prod.ext_iff])
            (tg_ne_L 2).symm]
          simp [σ0, Lv, Rv, Prod.ext_iff]
        exact (hasDerivWithinAt_const t (Icc (0:ℝ) dt) (0:ℝ)).congr (fun y _ => hL2 y) (hL2 t)
    · show HasDerivWithinAt (fun u => traj u tg) (Term.eval (Term.const 1) (traj t)) _ t
      simp only [Term.eval]
      exact (hasDerivWithinAt_id t (Icc (0:ℝ) dt)).congr (fun y _ => traj_tg y) (traj_tg t)
  · intro t ht x hx
    have h0 : x ≠ Lv 0 := by
      rintro rfl; exact hx (by simp [DLCalTiming.clk, ODESystem.bound, leftBlock])
    have h1 : x ≠ Lv 1 := by
      rintro rfl; exact hx (by simp [DLCalTiming.clk, ODESystem.bound, leftBlock])
    have h2 : x ≠ tg := by
      rintro rfl; exact hx (by simp [DLCalTiming.clk, ODESystem.bound, leftBlock])
    rw [traj_other t h0 h1 h2, Function.update_of_ne h2]
  · intro t ht
    have he0 := Real.exp_pos (-(5/4 * t))
    have he1 : Real.exp (-(5/4 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    rw [sat_domL, traj_L0, traj_L1]
    refine ⟨by linarith, by linarith, ?_⟩
    nlinarith [ht.1]

theorem guardSLOW (x : State (Var 3)) (h0 : 0 ≤ x (Lv 1)) (h1 : x (Lv 1) < 20)
    (h2 : 3/10 ≤ x (Lv 0)) (h3 : x (Lv 0) ≤ 3/5) :
    Formula.sat (hostGuard vs 3 Side.L (mL 0)) x := by
  simp [hostGuard, mL, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp03,
    hp06, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Lv]
  exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩

theorem σ0_uL : σ0 uL = 0 := by simp [σ0, Lv, Rv]

/-- One iteration of the left automaton: `SLOW → SLOW`, the guard-gated window for `dt`. -/
theorem left_step (dt : ℝ) (hdt : 0 ≤ dt) :
    Program.sem (leftAutomatonBody (A dt) uL) σ0 (traj dt) := by
  have hg : Formula.sat (hostGuard vs 3 Side.L (mL 0)) σ0 :=
    guardSLOW σ0 (by simp [σ0, Lv]) (by simp [σ0, Lv]; norm_num) (by simp [σ0, Lv]; norm_num)
      (by simp [σ0, Lv]; norm_num)
  have hassign : Function.update σ0 uL ((0 : ℕ) : ℝ) = σ0 := by
    funext y; by_cases hy : y = uL
    · subst hy; simp [σ0_uL]
    · simp [Function.update_of_ne hy]
  refine bigChoiceP_sem_of_mem (p := leftModeStep (A dt) uL 0)
    (List.mem_map.mpr ⟨0, List.mem_range.mpr (by rw [A_numModes]; norm_num), rfl⟩) ?_
  refine ⟨σ0, ⟨rfl, ?_⟩, ?_⟩
  · simp only [modeIs, Formula.sat, CompOp.interp, Term.eval, σ0_uL]; norm_num
  refine bigChoiceP_sem_of_mem (p := leftEdge (A dt) uL 0)
    (by rw [show (A dt).succ 0 = [1, 2, 0] from by rw [A_succ, nextL_eq]; rfl]; simp) ?_
  refine ⟨σ0, ⟨rfl, ?_⟩, σ0, ?_, ?_⟩
  · rw [A_guard dt 0 (by norm_num)]; exact hg
  · refine ⟨by simp [Term.eval, σ0_uL], fun y _ => rfl⟩
  · rw [A_window dt 0 (by norm_num)]
    refine ⟨σ0, ⟨rfl, hg⟩, ?_⟩
    rw [sem_windowSeg_one]
    refine ⟨Function.update σ0 tg 0, ⟨by simp [Term.eval], fun y hy => Function.update_of_ne hy _ _⟩,
      traj dt, left_ode dt hdt, ?_⟩
    exact ⟨rfl, by rw [sat_clkGuard, traj_tg]⟩

/-! ## The mode-keyed invariant at a bi-state -/

theorem sat_modeKeyedR {ϕ : ℕ → RFormula (Var 3)} {k : ℕ} {a b : State (Var 3)} :
    RFormula.sat (modeKeyedR uL ϕ k) (a, b) ↔
      ∀ m < k, a uL = (m : ℝ) → RFormula.sat (ϕ m) (a, b) := by
  unfold modeKeyedR
  have key : ∀ ms : List ℕ,
      RFormula.sat (rbigAnd (ms.map (fun m =>
        RFormula.imp (RFormula.proj DLRel.Side.L (modeIs uL m)) (ϕ m)))) (a, b) ↔
      ∀ m ∈ ms, a uL = (m : ℝ) → RFormula.sat (ϕ m) (a, b) := by
    intro ms
    induction ms with
    | nil => simp [rbigAnd, RFormula.tt, RFormula.sat, CompOp.interp, RTerm.eval, Term.eval,
        Formula.sat]
    | cons m ms ih =>
        simp only [List.map_cons, rbigAnd, RFormula.sat_and, ih, List.mem_cons,
          forall_eq_or_imp]
        rw [RFormula_sat_imp]
        simp [RFormula.sat, modeIs, Formula.sat, CompOp.interp, Term.eval]
  rw [key]
  simp [List.mem_range]

theorem sat_row0 (a b : State (Var 3)) :
    RFormula.sat (ϕRow 0) (a, b) ↔ a (Lv 0) ≤ b (Rv 0) ∧ a (Lv 1) ≤ b (Rv 1) + 1/2 := by
  show RFormula.sat (canonInvM (g 0) (gs 0)) (a, b) ↔ _
  simp only [canonInvM, gs, List.foldr, RFormula.sat_and, sat_canonInv_bi]
  rw [show (comps 0).getD 1 (Term.const 0) = (gs 0).getD 0 (Term.const 0) from rfl,
    eval_gs0 0 (by norm_num), eval_g 0 (by norm_num)]
  simp [Lv, Rv, mL', mQ]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- **The guarded Theorem 3 of `rover_patrol_zones` is false as stated**: the statement of
`rover_patrol_zones_modeKeyed`, with the right automaton guarded, fails for every `dt > 0`. -/
theorem rover_patrol_zones_guarded_false (dt : ℝ) (hdt : 0 < dt) :
    ¬ RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody GrG mv)
      (psiK uL ϕRow (A dt).numModes domL domR
        (mvRegionR mv region GrG.modes.length))) := by
  intro hvalid
  have h := (RFormula_sat_imp _ _ (σ0, σ0)).mp (hvalid (σ0, σ0))
  have hpre : RFormula.sat (psiK uL ϕRow (A dt).numModes domL domR
      (mvRegionR mv region GrG.modes.length)) (σ0, σ0) := by
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [sat_modeKeyedR]
      intro m _ hm
      have : m = 0 := by rw [σ0_uL] at hm; exact_mod_cast hm.symm
      subst this
      rw [sat_row0]; simp [σ0, Lv, Rv]; norm_num
    · show Formula.sat domL σ0
      rw [sat_domL]; simp [σ0, Lv, Rv]; norm_num
    · show Formula.sat domR σ0
      rw [sat_domR]; simp [σ0, Lv, Rv]; norm_num
    · show Formula.sat (mvRegion mv region GrG.modes.length) σ0
      rw [sat_mvRegion]
      refine ⟨0, by simp [GrG, Gr], by simp [σ0, Lv, Rv], ?_⟩
      rw [sat_region_lt 0 (by norm_num), cutSatR_val 0 (by norm_num)]
      simp [σ0, Lv, Rv, loL, loQ, capL, capQ]; norm_num
    · show Formula.sat (mvValid uL (A dt).numModes) σ0
      rw [sat_mvValid]
      exact ⟨0, by rw [A_numModes]; norm_num, by rw [σ0_uL]; norm_num⟩
  have hfa := h hpre
  have hleft : RProgram.sem (RProgram.biprog (Program.star (leftAutomatonBody (A dt) uL))
      (Program.test Formula.tt)) (σ0, σ0) (traj dt, σ0) :=
    ⟨Relation.ReflTransGen.single (left_step dt hdt.le), rfl, trivial⟩
  have hdia := hfa (traj dt, σ0) hleft
  apply hdia
  rintro ⟨ωL, ωR⟩ ⟨hL, hR⟩ hΦ
  obtain ⟨rfl, -⟩ := hL
  have hωR : ωR = σ0 := star_frozen (by simp [σ0, Lv, Rv]) (by simp [σ0, Lv, Rv]; norm_num)
    (by simp [σ0, Lv, Rv]; norm_num) (by simp [σ0, Lv, Rv]; norm_num) hR
  subst hωR
  have hrow := (sat_modeKeyedR.mp hΦ.1.1.1) 0 (by rw [A_numModes]; norm_num)
    (by rw [traj_other dt (by simp [Lv, Prod.ext_iff]) (by simp [Lv, Prod.ext_iff])
      (by simp [Prod.ext_iff]), σ0_uL]; norm_num)
  rw [sat_row0, traj_L0] at hrow
  have he : Real.exp (-(5/4 * dt)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have := hrow.1
  simp [σ0, Lv, Rv] at this
  linarith

end V2RoverPatrolZonesCounterexample
end RelCertifier
