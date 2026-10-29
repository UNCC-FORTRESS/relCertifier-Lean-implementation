import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.engine_start_highidle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `engine_start_highidle`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr` (the file's five modes and their declared
`next` lists), the lowered right guards, and `ε_r = 1` read from the file. The right model is
the ground-idle start schedule (idle `62 %`) with the sequencer's light-off timer: the core
speed `n` (coordinate 0) and the timer `t` (coordinate 1); coordinate 2 is the padding of the
bridge's keyed records (field 0, frozen). Evolve domain `5 ≤ n ≤ 110`, `0 ≤ t ≤ 40`. Every
phase contracts the speed, `n' = k (c − n)`: `STARTER` (`5 ≤ n < 25`, `t < 30`; `k = 0.1`,
`c = 30`, and the timer runs, `t' = 1`), `LIGHTOFF` (`[25, 50)`, `0.08`, `55`), `SELF`
(`[50, 60)`, `0.15`, `62`), `IDLE` (`n ≥ 60`, `0.5`, `62`); `ABORT` (`n < 25`, `t ≥ 30`) holds
both coordinates. The timer is frozen outside `STARTER`.
* Existence (i): `STARTER`: the explicit run `(30 + (n₀ − 30) e^{−0.1 s}, t₀ + s)`
  (`trajRs_sol`), `n` between `n₀` and `30`, `t ≤ t₀ + 1 < 31`; `LIGHTOFF`, `SELF`, `IDLE`: the
  explicit exponential of `n` with the timer held (`exists_contract_run`); `ABORT`: the frozen
  run (`const_sol`).
* (ii): the speed stays between its start and its set point (`linear_between`). `STARTER` ends
  in `[5, 30]`: in `LIGHTOFF` from 25, otherwise in `STARTER` while the timer is below 30 and
  in `ABORT` once it has reached 30 (style (b), an exit on the speed or on the time-out);
  `LIGHTOFF` ends in `[25, 55] ⊆ LIGHTOFF ∪ SELF`, `SELF` in `[50, 62] ⊆ SELF ∪ IDLE` (style (b));
  `IDLE` keeps `n ≥ 60` and `ABORT` holds both coordinates (`ODESol.const`; style (a),
  invariant); each entered mode is a declared successor.
Z3-free; modelled on `VentilatorVcCuffleak.lean` (the clock) and `TankDos3to1.lean`.
-/

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2EngineStartHighidle

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["n", "t"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := engine_start_highidle_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp008 : Run.parseRat "0.08" = some ((2:ℚ)/25) := by
  have h : parseQ "0.08" = some (⟨8, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp30 : Run.parseRat "30" = some (30 : ℚ) := by
  have h : parseQ "30" = some (⟨30, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp55 : Run.parseRat "55" = some (55 : ℚ) := by
  have h : parseQ "55" = some (⟨55, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp62 : Run.parseRat "62" = some (62 : ℚ) := by
  have h : parseQ "62" = some (⟨62, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp500 : Run.parseRat "50.0" = some (50 : ℚ) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp600 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1100 : Run.parseRat "110.0" = some (110 : ℚ) := by
  have h : parseQ "110.0" = some (⟨1100, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The contracting phases' speed fields `n' = k_q (c_q − n)` (`STARTER` 0.1/30, `LIGHTOFF`
0.08/55, `SELF` 0.15/62, `IDLE` 0.5/62). -/
noncomputable def kR (q : ℕ) : ℝ :=
  if q = 0 then 1/10 else if q = 1 then 2/25 else if q = 2 then 3/20 else 1/2
noncomputable def cR (q : ℕ) : ℝ :=
  if q = 0 then 30 else if q = 1 then 55 else 62

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR q * (cR q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, engine_start_highidle_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp008,
      hp015, hp05, hp30, hp55, hp62, hp00, hp10, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR, cR]

/-- `ABORT` holds the speed. -/
theorem fA0_eval (x : State (Var 3)) : Term.eval (fR 4 0) x = 0 := by
  simp [fR, hostDyn, mR, engine_start_highidle_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp008,
    hp015, hp05, hp30, hp55, hp62, hp00, hp10, Run.resolveVar, List.findIdx?_cons,
    List.finRange, ITerm.toHost, Term.eval, AOp.interp]

/-- The timer runs in `STARTER`. -/
theorem fS1_eval (x : State (Var 3)) : Term.eval (fR 0 1) x = 1 := by
  simp [fR, hostDyn, mR, engine_start_highidle_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp008,
    hp015, hp05, hp30, hp55, hp62, hp00, hp10, Run.resolveVar, List.findIdx?_cons,
    List.finRange, ITerm.toHost, Term.eval, AOp.interp]

/-- The timer is frozen in every other phase. -/
theorem fRt_eval (q : ℕ) (hq1 : 1 ≤ q) (hq5 : q < 5) (x : State (Var 3)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, engine_start_highidle_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp008,
      hp015, hp05, hp30, hp55, hp62, hp00, hp10, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp]

/-- The padding coordinate 2 (not in `vs`): its right field lowers to 0. -/
theorem fR2_eval (q : ℕ) (hq5 : q < 5) (x : State (Var 3)) : Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, engine_start_highidle_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp008,
      hp015, hp05, hp30, hp55, hp62, hp00, hp10, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval]

/-- Outside `STARTER`, every right field but the speed's vanishes. -/
theorem fRo_eval (q : ℕ) (hq1 : 1 ≤ q) (hq5 : q < 5) (i : Fin 3) (hi : i ≠ 0)
    (x : State (Var 3)) : Term.eval (fR q i) x = 0 := by
  match i, hi with
  | 1, _ => exact fRt_eval q hq1 hq5 x
  | 2, _ => exact fR2_eval q hq5 x

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (5 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 110 ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 40) := by
  simp only [domR, hostEvolve, mR, engine_start_highidle_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp50, hp1100, hp00, hp400, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (STARTER 0, LIGHTOFF 1, SELF 2, IDLE 3, ABORT 4). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 4), (1, 1), (1, 2), (2, 2), (2, 3), (3, 3), (4, 4)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 5) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 5 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## The right guards, evaluated -/

theorem sat_g0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (5 ≤ ν (Rv 0) ∧ ν (Rv 0) < 25 ∧ ν (Rv 1) < 30) := by
  simp [hostGuard, mR, engine_start_highidle_IRv2, Run.lowerF, Run.lowerE, hp50, hp250, hp300,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_g1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔ 25 ≤ ν (Rv 0) ∧ ν (Rv 0) < 50 := by
  simp [hostGuard, mR, engine_start_highidle_IRv2, Run.lowerF, Run.lowerE, hp250, hp500, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔ 50 ≤ ν (Rv 0) ∧ ν (Rv 0) < 60 := by
  simp [hostGuard, mR, engine_start_highidle_IRv2, Run.lowerF, Run.lowerE, hp500, hp600, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔ 60 ≤ ν (Rv 0) := by
  simp [hostGuard, mR, engine_start_highidle_IRv2, Run.lowerF, Run.lowerE, hp600, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g4 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 4)) ν ↔ ν (Rv 0) < 25 ∧ 30 ≤ ν (Rv 1) := by
  simp [hostGuard, mR, engine_start_highidle_IRv2, Run.lowerF, Run.lowerE, hp250, hp300, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR engine_start_highidle_IRv2 = 1 := by
  simp [epsR, engine_start_highidle_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem memR (q : ℕ) (i : Fin 3) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ i

/-- The speed field of a contracting phase, along the run. -/
theorem hfR (q : ℕ) (hq : q < 4) : ∀ s, Formula.sat (modeW q).dom s →
    Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cR q - s (Rv 0)) :=
  fun s _ => by rw [eval_unit_mul, fR0_eval q hq]

/-- A coordinate between `a` and `c` lies in any interval containing both. -/
theorem between_bounds {a c y lo hi : ℝ} (hb : min a c ≤ y ∧ y ≤ max a c) (h1 : lo ≤ a)
    (h2 : lo ≤ c) (h3 : a ≤ hi) (h4 : c ≤ hi) : lo ≤ y ∧ y ≤ hi :=
  ⟨le_trans (le_min h1 h2) hb.1, le_trans hb.2 (max_le h3 h4)⟩

/-! ## Existence: the explicit runs -/

theorem lin_der (a b t : ℝ) : HasDerivAt (fun u => a + b * u) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

/-- The run of `STARTER` from `x`: the spool's approach to 30 % and the running timer. -/
noncomputable def phiS (x : State (Var 3)) (i : Fin 3) (s : ℝ) : ℝ :=
  if i.val = 0 then 30 + (x (Rv 0) - 30) * Real.exp (-(1/10 * s))
  else if i.val = 1 then x (Rv 1) + 1 * s
  else x (Rv 2)

theorem phiS_der (x : State (Var 3)) (i : Fin 3) (s : ℝ) :
    HasDerivAt (phiS x i) (Term.eval (fR 0 i) (trajRs x (phiS x) s)) s := by
  match i with
  | 0 =>
      rw [fR0_eval 0 (by norm_num), trajRs_R, show kR 0 = 1/10 by norm_num [kR],
        show cR 0 = 30 by norm_num [cR]]
      have hf : phiS x 0 = fun u => 30 + (x (Rv 0) - 30) * Real.exp (-(1/10 * u)) := by
        funext u; simp [phiS]
      rw [hf]
      exact hasDerivAt_expApproach (1/10) 30 (x (Rv 0)) s
  | 1 =>
      rw [fS1_eval]
      have hf : phiS x 1 = fun u => x (Rv 1) + 1 * u := by funext u; simp [phiS]
      rw [hf]; exact lin_der _ _ s
  | 2 =>
      rw [fR2_eval 0 (by norm_num)]
      have hf : phiS x 2 = fun _ => x (Rv 2) := by funext u; simp [phiS]
      rw [hf]; exact hasDerivAt_const _ _

/-- **`STARTER`'s run** from a guard state: the speed between `n₀` and 30, the timer below
`t₀ + 1 < 31`. -/
theorem exists_runS (x : State (Var 3)) (hd : Formula.sat domR x) (ht : x (Rv 1) < 30) :
    ∃ Φ, ODESol (rightBlock (fR 0) (Term.const 1)) domR x 1 Φ := by
  obtain ⟨n5, n110, t0, t40⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiS x) 1 (by norm_num) (fun i => ?_)
    (fun i s _ _ => phiS_der x i s) (fun s hs hs1 => ?_)⟩
  · match i with
    | 0 => simp [phiS]
    | 1 => simp [phiS]
    | 2 => simp [phiS]
  · obtain ⟨l, u⟩ := exp_approach_between (1/10) 30 (x (Rv 0)) s (by norm_num) hs
    rw [sat_domR, trajRs_R, trajRs_R]
    simp only [phiS, Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false]
    exact ⟨le_trans (le_min n5 (by norm_num)) l, le_trans u (max_le n110 (by norm_num)),
      by linarith, by linarith⟩

/-- **The contracting phases' runs** with the timer held: the explicit exponential of the
speed, between `n₀` and the set point, both in `[5, 110]`. -/
theorem exists_runC (q : ℕ) (hq1 : 1 ≤ q) (hq4 : q < 4) (x : State (Var 3))
    (hd : Formula.sat domR x) (hk : 0 ≤ kR q) (hc : 5 ≤ cR q ∧ cR q ≤ 110) :
    ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x 1 Φ := by
  obtain ⟨n5, n110, t0, t40⟩ := (sat_domR x).mp hd
  refine exists_contract_run x 0 (kR q) (cR q) hk (fR0_eval q hq4)
    (fun i hi s => fRo_eval q hq1 (by omega) i hi s) ?_ 1 (by norm_num)
  intro v h1 h2
  show Formula.sat domR _
  rw [sat_domR, trajJ_j, trajJ_Rv_ne x 0 (fun _ => v) 0 (by decide : (1 : Fin 3) ≠ 0)]
  exact ⟨le_trans (le_min n5 hc.1) h1, le_trans h2 (max_le n110 hc.2), t0, t40⟩

/-- **`ABORT`'s run**: every field vanishes, the state is held. -/
theorem exists_runA (x : State (Var 3)) (hd : Formula.sat domR x) :
    ∃ Φ, ODESol (rightBlock (fR 4) (Term.const 1)) domR x 1 Φ :=
  ⟨_, const_sol (fun i s => by
      match i with
      | 0 => exact fA0_eval s
      | 1 => exact fRt_eval 4 (by norm_num) (by norm_num) s
      | 2 => exact fR2_eval 4 (by norm_num) s) hd (by norm_num)⟩

/-- **Assumption 1 for `engine_start_highidle`**, every mode, Z3-free. -/
theorem engine_start_highidle_wellFormedR :
    WellFormedR Gr guardR (epsR engine_start_highidle_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- STARTER: rises toward 30, ends in [5, 30]; LIGHTOFF from 25, else STARTER while the
    -- timer is below 30 and ABORT once it has reached 30
    have hgx := (sat_g0 x).mp hg
    refine ⟨exists_runS x hd hgx.2.2, ?_⟩
    intro t Φ _ H
    have hb := H.linear_between (memR 0 0) (kR 0) (cR 0) (by norm_num [kR]) (hfR 0 (by norm_num))
    rw [show cR 0 = 30 by norm_num [cR]] at hb
    have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2.1]) (le_refl (30:ℝ))
    by_cases h25 : Φ t (Rv 0) < 25
    · by_cases h30 : Φ t (Rv 1) < 30
      · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_g0 _).mpr ⟨hy.1, h25, h30⟩⟩
      · exact ⟨edgeW 0 4, edge_mem 0 4 (by decide), (sat_g4 _).mpr ⟨h25, by linarith⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
        (sat_g1 _).mpr ⟨by linarith, by linarith [hy.2]⟩⟩
  · -- LIGHTOFF: rises toward 55, ends in [25, 55]: LIGHTOFF below 50, SELF from 50
    have hgx := (sat_g1 x).mp hg
    refine ⟨exists_runC 1 (by norm_num) (by norm_num) x hd (by norm_num [kR])
      (by norm_num [cR]), ?_⟩
    intro t Φ _ H
    have hb := H.linear_between (memR 1 0) (kR 1) (cR 1) (by norm_num [kR]) (hfR 1 (by norm_num))
    rw [show cR 1 = 55 by norm_num [cR]] at hb
    have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2]) (le_refl (55:ℝ))
    by_cases h50 : Φ t (Rv 0) < 50
    · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_g1 _).mpr ⟨hy.1, h50⟩⟩
    · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide),
        (sat_g2 _).mpr ⟨by linarith, by linarith [hy.2]⟩⟩
  · -- SELF: rises toward 62, ends in [50, 62]: SELF below 60, IDLE from 60
    have hgx := (sat_g2 x).mp hg
    refine ⟨exists_runC 2 (by norm_num) (by norm_num) x hd (by norm_num [kR])
      (by norm_num [cR]), ?_⟩
    intro t Φ _ H
    have hb := H.linear_between (memR 2 0) (kR 2) (cR 2) (by norm_num [kR]) (hfR 2 (by norm_num))
    rw [show cR 2 = 62 by norm_num [cR]] at hb
    have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2]) (le_refl (62:ℝ))
    by_cases h60 : Φ t (Rv 0) < 60
    · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_g2 _).mpr ⟨hy.1, h60⟩⟩
    · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide), (sat_g3 _).mpr (by linarith)⟩
  · -- IDLE: contracts toward 62 from n ≥ 60, so the run stays at or above 60 (invariant)
    have hgx := (sat_g3 x).mp hg
    refine ⟨exists_runC 3 (by norm_num) (by norm_num) x hd (by norm_num [kR])
      (by norm_num [cR]), ?_⟩
    intro t Φ _ H
    have hb := H.linear_between (memR 3 0) (kR 3) (cR 3) (by norm_num [kR]) (hfR 3 (by norm_num))
    rw [show cR 3 = 62 by norm_num [cR]] at hb
    exact ⟨edgeW 3 3, edge_mem 3 3 (by decide),
      (sat_g3 _).mpr (le_trans (le_min hgx (by norm_num)) hb.1)⟩
  · -- ABORT: both coordinates are held, so `n < 25` and `t ≥ 30` are kept (invariant)
    have hgx := (sat_g4 x).mp hg
    refine ⟨exists_runA x hd, ?_⟩
    intro t Φ _ H
    have hn := H.const (memR 4 0) (fun s _ => by rw [eval_unit_mul, fA0_eval])
    have ht := H.const (memR 4 1)
      (fun s _ => by rw [eval_unit_mul, fRt_eval 4 (by norm_num) (by norm_num)])
    exact ⟨edgeW 4 4, edge_mem 4 4 (by decide),
      (sat_g4 _).mpr ⟨by rw [hn]; exact hgx.1, by rw [ht]; exact hgx.2⟩⟩

end V2EngineStartHighidle
end RelCertifier
