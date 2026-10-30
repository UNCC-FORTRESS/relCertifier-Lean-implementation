/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `turbine_startup_gearratio`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr` (the file's five modes and their declared
`next` lists), the lowered right guards, and `ε_r = 1` read from the file (at dimension 3:
coordinate 0 is the rotor speed `w`, coordinate 1 the frozen gust amplitude `G`, coordinate 2
the gust clock `t`). The right model is the reference turbine's start-up and regulation in a
gust, inside the evolve domain `0 ≤ w ≤ 13.31` (rest to the overspeed trip), `0 ≤ G ≤ 5.03`
(the design gust), `t ≥ 0`. Every mode freezes `G`; `SPINUP`, `RAMP`, `GEN` and `REG` also
freeze `t` and contract the speed, `w' = k (c − w)`:
`SPINUP` (`[2, 5)`, `k = 0.03`, `c = 9`), `RAMP` (`[5, 6.9)`, `0.04`, `7.5`),
`GEN` (`[6.9, 11.979)`, `0.05`, `12.1`), `REG` (`w ≥ 11.979`, `1.3125`, `12.1`);
`GUST` (`w ≥ 11.979`) has `w' = 1.3125 (12.1 − w) + 0.24 G` and `t' = 1`.
* Existence (i): for the four contractions the explicit exponential (`exists_contract_run`),
  every set point lying in `[0, 13.31]`; for `GUST` the explicit run `exists_runGust`: `G`
  frozen, the clock `t₀ + u`, and the exponential approach of `w` to the gust plateau
  `c(G) = 12.1 + (32/175) G ∈ [12.1, 13.0198] ⊆ [0, 13.31]` (`G` is frozen, so the field is
  the contraction `1.3125 (c(G) − w)` along the run).
* (ii): a contracting run stays between its start and its set point (`linear_between`), so
  `RAMP` ends in `[5, 7.5] ⊆ RAMP ∪ GEN` and `GEN` in `[6.9, 12.1] ⊆ GEN ∪ REG` (style (b),
  exit), `REG` in `[11.979, ∞)` (style (a), invariant). `SPINUP`'s set point `9` lies in
  `GEN`, not a successor of `SPINUP`, so its run is also bounded by its rate: the field is at
  most `0.03 · 9 = 0.27` on the domain (`rate_le`), so a run of duration `t ≤ 1` from `w < 5`
  ends in `[2, 5.27] ⊆ SPINUP ∪ RAMP` (style (b), exit). `GUST` keeps `w ≥ 11.979` (style (a),
  invariant) by the lower barrier `coord_ge_barrier`: at `w ≤ 11.979` the field is at least
  `1.3125 · 0.121 > 0` since `G ≥ 0` on the domain. Each entered mode is a declared successor.
Z3-free; modelled on `MoldingPackCheckring.lean` (clock + exponential, `trajRs_sol`) and
`EngineStartHighidle.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.turbine_startup_gearratio

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2TurbineStartupGearratio

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["w", "G", "t"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := turbine_startup_gearratio_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp003 : Run.parseRat "0.03" = some ((3:ℚ)/100) := by
  have h : parseQ "0.03" = some (⟨3, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp004 : Run.parseRat "0.04" = some ((1:ℚ)/25) := by
  have h : parseQ "0.04" = some (⟨4, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp005 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp13125 : Run.parseRat "1.3125" = some ((21:ℚ)/16) := by
  have h : parseQ "1.3125" = some (⟨13125, 10000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp024 : Run.parseRat "0.24" = some ((6:ℚ)/25) := by
  have h : parseQ "0.24" = some (⟨24, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp9 : Run.parseRat "9" = some (9 : ℚ) := by
  have h : parseQ "9" = some (⟨9, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp75 : Run.parseRat "7.5" = some ((15:ℚ)/2) := by
  have h : parseQ "7.5" = some (⟨75, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp121 : Run.parseRat "12.1" = some ((121:ℚ)/10) := by
  have h : parseQ "12.1" = some (⟨121, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1331 : Run.parseRat "13.31" = some ((1331:ℚ)/100) := by
  have h : parseQ "13.31" = some (⟨1331, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp503 : Run.parseRat "5.03" = some ((503:ℚ)/100) := by
  have h : parseQ "5.03" = some (⟨503, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp2 : Run.parseRat "2" = some (2 : ℚ) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp5 : Run.parseRat "5" = some (5 : ℚ) := by
  have h : parseQ "5" = some (⟨5, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp69 : Run.parseRat "6.9" = some ((69:ℚ)/10) := by
  have h : parseQ "6.9" = some (⟨69, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp11979 : Run.parseRat "11.979" = some ((11979:ℚ)/1000) := by
  have h : parseQ "11.979" = some (⟨11979, 1000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-- Right speed fields of the four contracting modes: `w' = k_q (c_q − w)` (`SPINUP` 0.03/9,
`RAMP` 0.04/7.5, `GEN` 0.05/12.1, `REG` 1.3125/12.1). -/
noncomputable def kR (q : ℕ) : ℝ :=
  if q = 0 then 3/100 else if q = 1 then 1/25 else if q = 2 then 1/20 else 21/16
noncomputable def cR (q : ℕ) : ℝ :=
  if q = 0 then 9 else if q = 1 then 15/2 else 121/10

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR q * (cR q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, turbine_startup_gearratio_IRv2, vs, Run.dynOf, Run.lowerE, hp003,
      hp004, hp005, hp13125, hp024, hp9, hp75, hp121, hp00, hp10, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR, cR]

/-- The gust amplitude `G` and, outside `GUST`, the gust clock `t` are frozen. -/
theorem fRo_eval (q : ℕ) (hq : q < 4) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | 1, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, turbine_startup_gearratio_IRv2, vs, Run.dynOf, Run.lowerE, hp003,
        hp004, hp005, hp13125, hp024, hp9, hp75, hp121, hp00, hp10, Run.resolveVar,
        List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]
  | 2, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, turbine_startup_gearratio_IRv2, vs, Run.dynOf, Run.lowerE, hp003,
        hp004, hp005, hp13125, hp024, hp9, hp75, hp121, hp00, hp10, Run.resolveVar,
        List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

/-- `GUST`'s speed field `1.3125 (12.1 − w) + 0.24 G`. -/
theorem fG0_eval (x : State (Var 3)) :
    Term.eval (fR 4 0) x = 21/16 * (121/10 - x (Rv 0)) + 6/25 * x (Rv 1) := by
  simp [fR, hostDyn, mR, turbine_startup_gearratio_IRv2, vs, Run.dynOf, Run.lowerE, hp13125,
    hp024, hp121, hp00, hp10, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem fG1_eval (x : State (Var 3)) : Term.eval (fR 4 1) x = 0 := by
  simp [fR, hostDyn, mR, turbine_startup_gearratio_IRv2, vs, Run.dynOf, Run.lowerE, hp13125,
    hp024, hp121, hp00, hp10, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval]

theorem fG2_eval (x : State (Var 3)) : Term.eval (fR 4 2) x = 1 := by
  simp [fR, hostDyn, mR, turbine_startup_gearratio_IRv2, vs, Run.dynOf, Run.lowerE, hp13125,
    hp024, hp121, hp00, hp10, Run.resolveVar, List.findIdx?_cons, List.finRange,
    ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 1331/100 ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 503/100 ∧
        0 ≤ x (Rv 2)) := by
  simp only [domR, hostEvolve, mR, turbine_startup_gearratio_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp1331, hp503, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (SPINUP 0, RAMP 1, GEN 2, REG 3, GUST 4). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (1, 1), (1, 2), (2, 2), (2, 3), (3, 3), (3, 4), (4, 4), (4, 3)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 5) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  have hlen : q < 5 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 5 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## The right guards, evaluated -/

theorem sat_g0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔ 2 ≤ ν (Rv 0) ∧ ν (Rv 0) < 5 := by
  simp [hostGuard, mR, turbine_startup_gearratio_IRv2, Run.lowerF, Run.lowerE, hp2, hp5, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔ 5 ≤ ν (Rv 0) ∧ ν (Rv 0) < 69/10 := by
  simp [hostGuard, mR, turbine_startup_gearratio_IRv2, Run.lowerF, Run.lowerE, hp5, hp69, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔
      69/10 ≤ ν (Rv 0) ∧ ν (Rv 0) < 11979/1000 := by
  simp [hostGuard, mR, turbine_startup_gearratio_IRv2, Run.lowerF, Run.lowerE, hp69, hp11979,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔ 11979/1000 ≤ ν (Rv 0) := by
  simp [hostGuard, mR, turbine_startup_gearratio_IRv2, Run.lowerF, Run.lowerE, hp11979, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g4 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 4)) ν ↔ 11979/1000 ≤ ν (Rv 0) := by
  simp [hostGuard, mR, turbine_startup_gearratio_IRv2, Run.lowerF, Run.lowerE, hp11979, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR turbine_startup_gearratio_IRv2 = 1 := by
  simp [epsR, turbine_startup_gearratio_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- A coordinate between `a` and `c` lies in any interval containing both. -/
theorem between_bounds {a c y lo hi : ℝ} (hb : min a c ≤ y ∧ y ≤ max a c) (h1 : lo ≤ a)
    (h2 : lo ≤ c) (h3 : a ≤ hi) (h4 : c ≤ hi) : lo ≤ y ∧ y ≤ hi :=
  ⟨le_trans (le_min h1 h2) hb.1, le_trans hb.2 (max_le h3 h4)⟩

/-! ## Existence in `GUST`: the explicit run -/

/-- `GUST`'s plateau for the frozen amplitude `G`: `12.1 + 0.24 G / 1.3125`. -/
noncomputable def cG (G : ℝ) : ℝ := 121/10 + 32/175 * G

/-- The run of `GUST` from `x`: the speed approaches the plateau, `G` frozen, the clock runs. -/
noncomputable def phiG (x : State (Var 3)) (i : Fin 3) (u : ℝ) : ℝ :=
  if i.val = 0 then cG (x (Rv 1)) + (x (Rv 0) - cG (x (Rv 1))) * Real.exp (-(21/16 * u))
  else if i.val = 1 then x (Rv 1)
  else x (Rv 2) + u

theorem phiG_der (x : State (Var 3)) (i : Fin 3) (u : ℝ) :
    HasDerivAt (phiG x i) (Term.eval (fR 4 i) (trajRs x (phiG x) u)) u := by
  match i with
  | 0 =>
      rw [fG0_eval, trajRs_R, trajRs_R]
      have hf0 : phiG x 0 = fun v =>
          cG (x (Rv 1)) + (x (Rv 0) - cG (x (Rv 1))) * Real.exp (-(21/16 * v)) := by
        funext v; simp [phiG]
      have hf1 : phiG x 1 = fun _ => x (Rv 1) := by funext v; simp [phiG]
      rw [hf0, hf1]
      exact (hasDerivAt_expApproach (21/16) (cG (x (Rv 1))) (x (Rv 0)) u).congr_deriv
        (by simp only [cG]; ring)
  | 1 =>
      rw [fG1_eval]
      have hf : phiG x 1 = fun _ => x (Rv 1) := by funext v; simp [phiG]
      rw [hf]; exact hasDerivAt_const u _
  | 2 =>
      rw [fG2_eval]
      have hf : phiG x 2 = fun v => x (Rv 2) + v := by funext v; simp [phiG]
      rw [hf]
      simpa using (hasDerivAt_id u).const_add (x (Rv 2))

theorem exists_runGust (x : State (Var 3)) (hd : Formula.sat domR x) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 4) (Term.const 1)) domR x ε Φ := by
  obtain ⟨w0, w1, g0, g1, t0⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiG x) ε hε (fun i => ?_) (fun i u _ _ => phiG_der x i u)
    (fun u hu _ => ?_)⟩
  · match i with
    | 0 => simp [phiG]
    | 1 => simp [phiG]
    | 2 => simp [phiG]
  · obtain ⟨l, h⟩ := exp_approach_between (21/16) (cG (x (Rv 1))) (x (Rv 0)) u (by norm_num) hu
    have c0 : 0 ≤ cG (x (Rv 1)) := by unfold cG; linarith
    have c1 : cG (x (Rv 1)) ≤ 1331/100 := by unfold cG; linarith
    rw [sat_domR, trajRs_R, trajRs_R, trajRs_R]
    simp only [phiG, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, if_true,
      one_ne_zero, if_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    exact ⟨le_trans (le_min w0 c0) l, le_trans h (max_le w1 c1), g0, g1, by linarith⟩

/-- **Assumption 1 for `turbine_startup_gearratio`**, every mode, Z3-free. -/
theorem turbine_startup_gearratio_wellFormedR :
    WellFormedR Gr guardR (epsR turbine_startup_gearratio_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  by_cases hq4 : q < 4
  · have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
    have hcr : 0 ≤ cR q ∧ cR q ≤ 1331/100 := by unfold cR; split_ifs <;> norm_num
    refine ⟨?_, ?_⟩
    · refine exists_contract_run x 0 (kR q) (cR q) hk (fR0_eval q hq4)
        (fun i hi s => fRo_eval q hq4 i hi s) ?_ 1 (by norm_num)
      intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j, trajJ_Rv_ne _ _ _ _ (by decide : (1 : Fin 3) ≠ 0),
        trajJ_Rv_ne _ _ _ _ (by decide : (2 : Fin 3) ≠ 0)]
      exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2.1 hcr.2),
        hdx.2.2⟩
    · intro t Φ ht H
      have hf : ∀ s, Formula.sat (modeW q).dom s →
          Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cR q - s (Rv 0)) :=
        fun s _ => by rw [eval_unit_mul, fR0_eval q hq4]
      have hb := H.linear_between (memR q) _ _ hk hf
      interval_cases q
      · -- SPINUP: rises toward 9 (inside GEN), but at rate at most 0.27, so a run of duration
        -- at most 1 from w < 5 ends in [2, 5.27]: SPINUP below 5, RAMP from 5
        have hgx := (sat_g0 x).mp hg
        rw [show cR 0 = 9 by norm_num [cR]] at hb
        have hlo : 2 ≤ Φ t (Rv 0) := le_trans (le_min hgx.1 (by norm_num)) hb.1
        have hrate : Φ t (Rv 0) ≤ x (Rv 0) + 27/100 * t := by
          refine H.rate_le (memR 0) (27/100) (fun s hs => ?_)
          have hs0 := ((sat_domR s).mp hs).1
          rw [hf s hs, show kR 0 = 3/100 by norm_num [kR], show cR 0 = 9 by norm_num [cR]]
          linarith
        by_cases h5 : Φ t (Rv 0) < 5
        · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_g0 _).mpr ⟨hlo, h5⟩⟩
        · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
            (sat_g1 _).mpr ⟨by linarith, by linarith [hgx.2]⟩⟩
      · -- RAMP: rises toward 7.5, ends in [5, 7.5]: RAMP below 6.9, GEN from 6.9
        have hgx := (sat_g1 x).mp hg
        rw [show cR 1 = 15/2 by norm_num [cR]] at hb
        have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2])
          (le_refl ((15:ℝ)/2))
        by_cases h69 : Φ t (Rv 0) < 69/10
        · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_g1 _).mpr ⟨hy.1, h69⟩⟩
        · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide),
            (sat_g2 _).mpr ⟨by linarith, by linarith [hy.2]⟩⟩
      · -- GEN: rises toward 12.1, ends in [6.9, 12.1]: GEN below 11.979, REG from 11.979
        have hgx := (sat_g2 x).mp hg
        rw [show cR 2 = 121/10 by norm_num [cR]] at hb
        have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2])
          (le_refl ((121:ℝ)/10))
        by_cases h12 : Φ t (Rv 0) < 11979/1000
        · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_g2 _).mpr ⟨hy.1, h12⟩⟩
        · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide), (sat_g3 _).mpr (by linarith)⟩
      · -- REG: contracts toward 12.1 from w ≥ 11.979, so the run stays at or above 11.979
        have hgx := (sat_g3 x).mp hg
        rw [show cR 3 = 121/10 by norm_num [cR]] at hb
        exact ⟨edgeW 3 3, edge_mem 3 3 (by decide),
          (sat_g3 _).mpr (le_trans (le_min hgx (by norm_num)) hb.1)⟩
  · have hq : q = 4 := by omega
    subst hq
    refine ⟨exists_runGust x hd 1 (by norm_num), ?_⟩
    · -- GUST: at w ≤ 11.979 the field is at least 1.3125 · 0.121 > 0 (G ≥ 0), so the run
      -- stays at or above 11.979 (lower barrier)
      intro t Φ _ H
      have hgx := (sat_g4 x).mp hg
      have hbar := H.coord_ge_barrier 0 (11979/1000) (fun s hs hle => by
        have hs1 := ((sat_domR s).mp hs).2.2.1
        rw [fG0_eval]
        nlinarith) hgx
      exact ⟨edgeW 4 4, edge_mem 4 4 (by decide), (sat_g4 _).mpr hbar⟩

end V2TurbineStartupGearratio
end RelCertifier
