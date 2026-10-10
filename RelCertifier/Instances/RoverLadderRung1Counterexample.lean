/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung1_2to3` — the guarded Theorem 3 is FALSE as stated

`RoverLadderRung1Modal.rover_ladder_rung1_modal` proves Theorem 3 over the `⊤`-guarded right
graph `GrE`. This file shows that the same statement over the GUARDED right automaton (every
edge testing the lowered guard of the mode it enters, `GrEG`) is false, for every window
length `dt > 0`, so no legal witness can exist: it is a property of the stated invariant, not
of the proof.

The witness bi-state: the right in `STEEP` at `s_R = 5`, `v_R = 0.1` (the bookkeeping
`mvValid` puts no bound on `s_R`); the left at `v_L = 0.1`, `s_L = 0.3`, `ψ_L = 0`. The loop
invariant holds there (`v_L ≤ v_R`, `s_L ≤ s_R + 0.2`, both envelopes). Along `STEEP`'s flow
`s_R` never decreases (`s' = v ≥ 0` on the domain), so the guards of `STEEP`'s successors
(`STEEP`: `s < 0.6`; `MODER`: `s < 1.4`) never hold: the guarded right has no step at all,
its only run is the empty one. The left `STEEP` window, run for `dt`, raises `v_L` to
`0.3 − 0.2 e^{−3 dt} > 0.1 = v_R`, which breaks the row `v_L ≤ v_R`.
-/
import RelCertifier.Instances.RoverLadderRung1Modal
import RelCertifier.Proofs.Encoding.GuardedSwitch

namespace RelCertifier
namespace RoverLadderRung1Counterexample

open DL DLCalTiming DLRel Parse Set RoverLadderRung1Modal

set_option linter.unusedSimpArgs false

/-! ## Pins and evaluations -/

theorem hp1 : Run.parseRat "1" = some 1 := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm1 : Run.parseRat "-1" = some (-1) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp14 : Run.parseRat "1.4" = some ((7:ℚ)/5) := by
  have h : parseQ "1.4" = some (⟨14, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem fLE00_eval (x : State (Var 3)) : Term.eval (fLE 0 0) x = 3 * (3/10 - x (Lv 0)) := by
  simp [fLE, hostDyn, mLE, refinement_ladder_rover_rung1_2to3_IR, vsE, Run.dynOf,
    Run.lowerE, he3, he030, hp1, hp05, hpm1, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Lv]

theorem fLE01_eval (x : State (Var 3)) :
    Term.eval (fLE 0 1) x = x (Lv 0) * (1 - 1/2 * (x (Lv 2) * x (Lv 2))) := by
  simp [fLE, hostDyn, mLE, refinement_ladder_rover_rung1_2to3_IR, vsE, Run.dynOf,
    Run.lowerE, he3, he030, hp1, hp05, hpm1, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Lv]

theorem fLE02_eval (x : State (Var 3)) : Term.eval (fLE 0 2) x = -1 * x (Lv 2) := by
  simp [fLE, hostDyn, mLE, refinement_ladder_rover_rung1_2to3_IR, vsE, Run.dynOf,
    Run.lowerE, he3, he030, hp1, hp05, hpm1, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Lv]

theorem sat_domLE (x : State (Var 3)) : Formula.sat domLE x ↔
    (-1/2 ≤ x (Lv 2) ∧ x (Lv 2) ≤ 3/20 ∧ 0 ≤ x (Lv 1) ∧ 0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 4/5) := by
  simp only [domLE, hostEvolve, mLE, refinement_ladder_rover_rung1_2to3_IR, vsE]
  simp [Run.lowerF, Run.lowerE, hpm05, hp015, he00, he08, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]
  tauto

/-- The successors of `STEEP` need `s_R < 1.4` (`STEEP`: `s < 0.6`, `MODER`: `s < 1.4`). -/
theorem guard_s_lt (t : ℕ) (ht : t < 2) (x : State (Var 3))
    (h : Formula.sat (hostGuard vsE 3 Side.R (mRE t)) x) : x (Rv 1) < 7/5 := by
  interval_cases t <;>
  · simp [hostGuard, mRE, refinement_ladder_rover_rung1_2to3_IR, Run.lowerF, Run.lowerE,
      he00, hp06, hp14, hp03, hp05, vsE, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
      ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv] at h
    linarith [h.1.2]


/-! ## The guarded right graph -/

/-- The declared edge `st → tgt`, testing the lowered guard of the mode it enters. -/
noncomputable def edgeG (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := hostGuard vsE 3 Side.R (mRE tgt), pruned := false }

/-- `rover_ladder_rung1_modal`'s right automaton (the file's modes and `next` lists), guarded. -/
noncomputable def GrEG : SearchGraph (Var 3) :=
  { modes := [modeE 0, modeE 1, modeE 2],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 2, edgeG 1 1, edgeG 2 2] }

theorem GrEG_guards : ∀ q, ∀ e ∈ GrEG.edgesFrom q,
    e.guard = hostGuard vsE 3 Side.R (mRE e.tgt) := by
  intro q e he
  have hmem : e ∈ GrEG.edges := List.mem_of_mem_filter he
  simp only [GrEG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem GrEG_edges : GrEG.edges.map (fun e => (e.src, e.tgt)) =
    GrE.edges.map (fun e => (e.src, e.tgt)) := rfl

/-! ## The right cannot move from `STEEP` at `s_R ≥ 1.4` -/

/-- A coordinate whose field is nonnegative on the domain does not decrease along a run. -/
theorem coord_mono {sys : ODESystem (Var 3)} {dom : Formula (Var 3)} {ν μ : State (Var 3)}
    (h : Program.sem (Program.ode sys dom) ν μ) {x : Var 3} {f : Term (Var 3)}
    (hx : (x, f) ∈ sys) (hnn : ∀ s, Formula.sat dom s → 0 ≤ Term.eval f s) : ν x ≤ μ x := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, -, hdom⟩ := h
  have hderiv : ∀ t ∈ Icc (0:ℝ) r,
      HasDerivWithinAt (fun s => Φ s x) (Term.eval f (Φ t)) (Icc 0 r) t :=
    fun t ht => hder t ht (x, f) hx
  have hcont : ContinuousOn (fun s => Φ s x) (Icc 0 r) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  have hmono : MonotoneOn (fun s => Φ s x) (Icc 0 r) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hcont (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact ((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      exact hnn _ (hdom t (Ioo_subset_Icc_self ht))
  have := hmono ⟨le_refl 0, hr⟩ ⟨hr, le_refl r⟩ hr
  simpa [hΦ0, hΦr] using this

/-- **No step.** From `mv = STEEP` with `s_R ≥ 1.4`, the guarded right automaton has no
step: `STEEP`'s flow keeps `s_R ≥ 1.4`, where neither successor's guard holds. -/
theorem no_step {σ μ : State (Var 3)} (hmv : σ mvE = 0) (hs : 7/5 ≤ σ (Rv 1))
    (h : Program.sem (rightAutomatonBody GrEG mvE) σ μ) : False := by
  obtain ⟨p, hp, hsem⟩ := bigChoiceP_sem_forward h
  simp only [List.mem_filterMap, List.mem_range] at hp
  obtain ⟨q, -, hqm⟩ := hp
  rcases hm : GrEG.modeAt q with _ | m
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
  have hm0 : m = modeE 0 := by simpa [SearchGraph.modeAt, GrEG] using hm.symm
  subst hm0
  have hsκ : σ (Rv 1) ≤ κ (Rv 1) :=
    coord_mono hflow (f := Term.binop .mul (Term.const 1) (fRE 0 1))
      (List.mem_map.mpr ⟨1, List.mem_finRange 1, rfl⟩)
      (fun s hs' => by
        simp only [Term.eval, AOp.interp]
        rw [fRE1_eval 0 (by norm_num)]
        have := ((sat_domRE s).mp hs').2.1
        linarith)
  obtain ⟨p2, hp2, hsem2⟩ := bigChoiceP_sem_forward hedge
  simp only [List.mem_map] at hp2
  obtain ⟨e, he, rfl⟩ := hp2
  obtain ⟨κ1, ⟨hκ1, hg⟩, -⟩ := hsem2
  subst hκ1
  have hmem : e ∈ GrEG.edges := List.mem_of_mem_filter he
  have hsrc : e.src = 0 := by simpa using (List.mem_filter.mp he).2
  simp only [GrEG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact absurd (guard_s_lt 1 (by norm_num) κ hg) (by linarith)
  · exact absurd (guard_s_lt 0 (by norm_num) κ hg) (by linarith)
  · exact absurd hsrc (by simp [edgeG])
  · exact absurd hsrc (by simp [edgeG])
  · exact absurd hsrc (by simp [edgeG])

theorem star_frozen {σ μ : State (Var 3)} (hmv : σ mvE = 0) (hs : 7/5 ≤ σ (Rv 1))
    (h : Relation.ReflTransGen (Program.sem (rightAutomatonBody GrEG mvE)) σ μ) : μ = σ := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hstep, -⟩
  · exact h.symm
  · exact (no_step hmv hs hstep).elim


/-! ## The left `STEEP` window, explicitly -/

/-- The witness state: left `v = 0.1`, `s = 0.3`, `ψ = 0`; right `v = 0.1`, `s = 5`, mode
`STEEP` (`mv = 0`); every other coordinate 0. -/
noncomputable def σ0 : State (Var 3) :=
  fun y => if y = Lv 0 then 1/10 else if y = Lv 1 then 3/10 else if y = Rv 0 then 1/10
    else if y = Rv 1 then 5 else 0

/-- The left `STEEP` flow from `σ0` with the clock: `v = 0.3 − 0.2 e^{−3t}`,
`s = 0.3 + 0.3 t − (1 − e^{−3t})/15`, `ψ = 0`, `tg = t`. -/
noncomputable def traj (t : ℝ) : State (Var 3) :=
  fun y => if y = Lv 0 then 3/10 - 1/5 * Real.exp (-3 * t)
    else if y = Lv 1 then 3/10 + 3/10 * t - 1/15 * (1 - Real.exp (-3 * t))
    else if y = tgE then t else σ0 y

theorem tgE_ne_L (i : Fin 3) : tgE ≠ Lv i := by simp [Lv, Prod.ext_iff]
theorem tgE_ne_R (i : Fin 3) : tgE ≠ Rv i := by simp [Rv, Prod.ext_iff]

theorem traj_L0 (t : ℝ) : traj t (Lv 0) = 3/10 - 1/5 * Real.exp (-3 * t) := by simp [traj]
theorem traj_L1 (t : ℝ) :
    traj t (Lv 1) = 3/10 + 3/10 * t - 1/15 * (1 - Real.exp (-3 * t)) := by
  simp [traj, show (Lv 1 : Var 3) ≠ Lv 0 from by simp [Lv, Prod.ext_iff]]
theorem traj_L2 (t : ℝ) : traj t (Lv 2) = 0 := by
  simp [traj, σ0, show (Lv 2 : Var 3) ≠ Lv 0 from by simp [Lv, Prod.ext_iff],
    show (Lv 2 : Var 3) ≠ Lv 1 from by simp [Lv, Prod.ext_iff],
    show (Lv 2 : Var 3) ≠ tgE from (tgE_ne_L 2).symm,
    show (Lv 2 : Var 3) ≠ Rv 0 from by simp [Lv, Rv, Prod.ext_iff],
    show (Lv 2 : Var 3) ≠ Rv 1 from by simp [Lv, Rv, Prod.ext_iff]]
theorem traj_tg (t : ℝ) : traj t tgE = t := by
  simp [traj, tgE_ne_L]
theorem traj_other (t : ℝ) {y : Var 3} (h0 : y ≠ Lv 0) (h1 : y ≠ Lv 1) (h2 : y ≠ tgE) :
    traj t y = σ0 y := by simp [traj, h0, h1, h2]

theorem exp_bounds (t : ℝ) (ht : 0 ≤ t) : 0 < Real.exp (-3 * t) ∧ Real.exp (-3 * t) ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩

/-- The explicit left run: the clocked `STEEP` flow for `dt`. -/
theorem left_ode (dt : ℝ) (hdt : 0 ≤ dt) :
    Program.sem (Program.ode (DLCalTiming.clk tgE (leftBlock (fLE 0))) domLE)
      (Function.update σ0 tgE 0) (traj dt) := by
  refine ⟨dt, traj, hdt, ?_, rfl, ?_, ?_, ?_⟩
  · funext y
    by_cases h0 : y = Lv 0
    · subst h0; simp [traj, σ0, tgE_ne_L]; norm_num
    by_cases h1 : y = Lv 1
    · subst h1; simp [traj_L1, σ0, Function.update_of_ne (tgE_ne_L 1).symm,
        show (Lv 1 : Var 3) ≠ Lv 0 from by simp [Lv, Prod.ext_iff]]
    by_cases h2 : y = tgE
    · subst h2; simp [traj_tg]
    rw [traj_other 0 h0 h1 h2, Function.update_of_ne h2]
  · intro t ht p hp
    simp only [DLCalTiming.clk, leftBlock, List.mem_append, List.mem_map, List.mem_finRange,
      true_and, List.mem_singleton] at hp
    have hE := (exp_bounds t ht.1)
    have hexp : HasDerivWithinAt (fun u : ℝ => Real.exp (-3 * u)) (Real.exp (-3 * t) * (-3))
        (Icc 0 dt) t := by
      have := ((hasDerivAt_id t).const_mul (-3)).exp
      simpa using this.hasDerivWithinAt
    rcases hp with ⟨i, rfl⟩ | rfl
    · fin_cases i
      · show HasDerivWithinAt (fun u => traj u (Lv 0)) (Term.eval (fLE 0 0) (traj t)) _ t
        rw [fLE00_eval, traj_L0]
        have h := (hexp.const_mul (1/5)).const_sub (3/10)
        refine (h.congr (fun y _ => traj_L0 y) (traj_L0 t)).congr_deriv ?_
        ring
      · show HasDerivWithinAt (fun u => traj u (Lv 1)) (Term.eval (fLE 0 1) (traj t)) _ t
        rw [fLE01_eval, traj_L0, traj_L2]
        have hid := hasDerivWithinAt_id t (Icc (0:ℝ) dt)
        have h := ((hid.const_mul (3/10)).const_add (3/10)).sub
          ((hexp.const_sub 1).const_mul (1/15))
        refine (h.congr (fun y _ => by rw [traj_L1]; simp) (by rw [traj_L1]; simp)).congr_deriv
          ?_
        simp; ring
      · show HasDerivWithinAt (fun u => traj u (Lv 2)) (Term.eval (fLE 0 2) (traj t)) _ t
        rw [fLE02_eval, traj_L2]
        refine ((hasDerivWithinAt_const t (Icc (0:ℝ) dt) (0:ℝ)).congr
          (fun y _ => traj_L2 y) (traj_L2 t)).congr_deriv ?_
        ring
    · show HasDerivWithinAt (fun u => traj u tgE) (Term.eval (Term.const 1) (traj t)) _ t
      simp only [Term.eval]
      exact (hasDerivWithinAt_id t (Icc (0:ℝ) dt)).congr (fun y _ => traj_tg y) (traj_tg t)
  · intro t ht x hx
    have h0 : x ≠ Lv 0 := by
      rintro rfl; exact hx (by simp [DLCalTiming.clk, ODESystem.bound, leftBlock])
    have h1 : x ≠ Lv 1 := by
      rintro rfl; exact hx (by simp [DLCalTiming.clk, ODESystem.bound, leftBlock])
    have h2 : x ≠ tgE := by
      rintro rfl; exact hx (by simp [DLCalTiming.clk, ODESystem.bound, leftBlock])
    rw [traj_other t h0 h1 h2, Function.update_of_ne h2]
  · intro t ht
    have hE := exp_bounds t ht.1
    rw [sat_domLE, traj_L0, traj_L1, traj_L2]
    refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
    · nlinarith [ht.1]
    · linarith
    · linarith

/-- The left `STEEP` window, run for `dt`. -/
theorem left_window (dt : ℝ) (hdt : 0 ≤ dt) :
    Program.sem (windowSeg (leftBlock (fLE 0)) domLE tgE dt 1) σ0 (traj dt) := by
  rw [sem_windowSeg_one]
  refine ⟨Function.update σ0 tgE 0, ?_, traj dt, left_ode dt hdt, ?_⟩
  · refine ⟨by simp [Term.eval], fun y hy => Function.update_of_ne hy _ _⟩
  · exact ⟨rfl, by rw [sat_clkGuard, traj_tg]⟩

/-! ## The relational semantics -/

/-- The side-split term at a bi-state reads each variable on its own side. -/
theorem rsplit_eval (t : Term (Var 3)) (a b : State (Var 3)) :
    RTerm.eval (rsplit t) (a, b) = Term.eval t (fun x => if x.1 = Side.R then b x else a x) := by
  induction t with
  | var v =>
      unfold rsplit
      match hv : v.1 with
      | Side.R => simp [RTerm.eval, Term.eval, hv]
      | Side.L => simp [RTerm.eval, Term.eval, hv]
      | Side.Aux => simp [RTerm.eval, Term.eval, hv]
  | const c => simp [rsplit, RTerm.eval, Term.eval]
  | binop op a' b' iha ihb => simp [rsplit, RTerm.eval, Term.eval, iha, ihb]

theorem sat_canonInv (g : Term (Var 3)) (a b : State (Var 3)) :
    RFormula.sat (canonInv g) (a, b) ↔
      Term.eval g (fun x => if x.1 = Side.R then b x else a x) ≤ 0 := by
  simp [canonInv, RFormula.sat, rsplit_eval, RTerm.eval, Term.eval, CompOp.interp]

/-- **The guarded Theorem 3 of `refinement_ladder_rover_rung1_2to3` is false as stated**: the
statement of `rover_ladder_rung1_modal`, with the right automaton guarded, fails for every
window length `dt > 0`. -/
theorem rover_ladder_rung1_guarded_false (dt : ℝ) (hdt : 0 < dt) :
    ¬ RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsE dt))
      (rightAutomatonBody GrEG mvE)
      (RFormula.and (RFormula.and (canonInvM gE gsE) (envLR domLE domRE))
        (mvValidR mvE GrEG.modes.length))) := by
  intro hvalid
  have h := (RFormula_sat_imp _ _ (σ0, σ0)).mp (hvalid (σ0, σ0))
  -- the loop invariant at the witness
  have hpre : RFormula.sat (RFormula.and (RFormula.and (canonInvM gE gsE) (envLR domLE domRE))
      (mvValidR mvE GrEG.modes.length)) (σ0, σ0) := by
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [show gsE = [gAt 1] from rfl] at *
      simp only [sat_canonInv]
      simp only [ite_self]
      rw [gAt1_eval]; simp [σ0, Lv, Rv]; norm_num
    · show RFormula.sat (canonInv gE) (σ0, σ0)
      rw [sat_canonInv]; simp only [ite_self]
      rw [show gE = gAt 0 from rfl, gAt0_eval]; simp [σ0, Lv, Rv]
    · show Formula.sat domLE σ0
      rw [sat_domLE]; simp [σ0, Lv, Rv]; norm_num
    · show Formula.sat domRE σ0
      rw [sat_domRE]; simp [σ0, Lv, Rv]; norm_num
    · show Formula.sat (mvValid mvE GrEG.modes.length) σ0
      rw [sat_mvValid]
      exact ⟨0, by simp [GrEG], by simp [σ0, Lv, Rv]⟩
  have hfa := h hpre
  -- one left iteration: the `STEEP` window for `dt`
  have hleft : RProgram.sem (RProgram.biprog (Program.star (bigChoice (leftProgsE dt)))
      (Program.test Formula.tt)) (σ0, σ0) (traj dt, σ0) := by
    refine ⟨Relation.ReflTransGen.single (Or.inl (left_window dt hdt.le)), rfl, trivial⟩
  have hdia := hfa (traj dt, σ0) hleft
  -- the right's only run is the empty one
  apply hdia
  rintro ⟨ωL, ωR⟩ ⟨hL, hR⟩ hΦ
  obtain ⟨rfl, -⟩ := hL
  have hωR : ωR = σ0 := star_frozen (by simp [σ0, Lv, Rv]) (by simp [σ0, Lv, Rv]; norm_num) hR
  subst hωR
  -- the row `v_L ≤ v_R` fails
  have hrow : RFormula.sat (canonInv gE) (traj dt, σ0) := hΦ.1.1.2
  rw [sat_canonInv, show gE = gAt 0 from rfl, gAt0_eval] at hrow
  simp only [show (Lv 0 : Var 3).1 = Side.L from rfl, show (Rv 0 : Var 3).1 = Side.R from rfl,
    if_true, reduceCtorEq, if_false] at hrow
  rw [traj_L0] at hrow
  have he : Real.exp (-(3 * dt)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  simp [σ0, Lv, Rv] at hrow
  linarith


end RoverLadderRung1Counterexample
end RelCertifier
