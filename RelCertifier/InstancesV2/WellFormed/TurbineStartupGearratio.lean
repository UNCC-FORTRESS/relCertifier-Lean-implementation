/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `turbine_startup_gearratio`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr` (the file's four modes and their declared
`next` lists), the lowered right guards, and `ε_r = 1` read from the file. The right model is
the rotor-speed start schedule: every mode is a 1-D contraction `w' = k (c − w)` inside the
evolve domain `[0, 12.1]` (the start-up's reachable speeds, round B of the benchmark, 2026-10-29;
the domain was `[0, 16]` before):
`SPINUP` (`[2, 5)`, `k = 0.03`, `c = 9`), `RAMP` (`[5, 6.9)`, `0.04`, `7.5`),
`GEN` (`w ≥ 6.9`, `0.05`, `12.1`), `STOP` (`w < 2`, `0.1`, `0`).
* Existence (i): the explicit exponential (`exists_contract_run`); every set point lies in
  `[0, 12.1]` (the rated speed `12.1` is the top of the domain).
* (ii): a run stays between its start and its set point (`linear_between`), so
  `RAMP` ends in `[5, 7.5] ⊆ RAMP ∪ GEN` (style (b), exit), `GEN` in `[6.9, 12.1]` and `STOP` in
  `[0, 2)` (style (a), invariant). `SPINUP`'s set point `9` lies in `GEN`, which is not a
  successor of `SPINUP`, so the run is also bounded by its rate: the field is at most
  `0.03 · 9 = 0.27` on the domain (`rate_le`), so a run of duration `t ≤ 1` from `w < 5` ends
  below `5.27 < 6.9`, i.e. in `[2, 5.27] ⊆ SPINUP ∪ RAMP` (style (b), exit). Each entered mode
  is a declared successor.
Z3-free; modelled on `EngineStartHighidle.lean` and `TankDos3to1.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.turbine_startup_gearratio

namespace RelCertifier
namespace V2TurbineStartupGearratio

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["w"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := turbine_startup_gearratio_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
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
theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
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
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp69 : Run.parseRat "6.9" = some ((69:ℚ)/10) := by
  have h : parseQ "6.9" = some (⟨69, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
/-- Right fields: `w' = k_q (c_q − w)` (`SPINUP` 0.03/9, `RAMP` 0.04/7.5, `GEN` 0.05/12.1,
`STOP` 0.1/0, the last written `−0.1 w` in the file). -/
noncomputable def kR (q : ℕ) : ℝ :=
  if q = 0 then 3/100 else if q = 1 then 1/25 else if q = 2 then 1/20 else 1/10
noncomputable def cR (q : ℕ) : ℝ :=
  if q = 0 then 9 else if q = 1 then 15/2 else if q = 2 then 121/10 else 0

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (cR q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, turbine_startup_gearratio_IRv2, vs, Run.dynOf, Run.lowerE, hp003,
      hp004, hp005, hp01, hp9, hp75, hp121, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv, kR, cR]

theorem fRo_eval (q : ℕ) (hq : q < 4) (i : Fin 2) (hi : i ≠ 0) (x : State (Var 2)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | 1, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, turbine_startup_gearratio_IRv2, vs, Run.dynOf, Run.lowerE, hp003,
        hp004, hp005, hp01, hp9, hp75, hp121, Run.resolveVar, List.findIdx?_cons, List.finRange,
        ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 121/10) := by
  simp only [domR, hostEvolve, mR, turbine_startup_gearratio_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp121, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (SPINUP 0, RAMP 1, GEN 2, STOP 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (3, 3)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## The right guards, evaluated -/

theorem sat_g0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔ 2 ≤ ν (Rv 0) ∧ ν (Rv 0) < 5 := by
  simp [hostGuard, mR, turbine_startup_gearratio_IRv2, Run.lowerF, Run.lowerE, hp20, hp50, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔ 5 ≤ ν (Rv 0) ∧ ν (Rv 0) < 69/10 := by
  simp [hostGuard, mR, turbine_startup_gearratio_IRv2, Run.lowerF, Run.lowerE, hp50, hp69, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g2 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 2)) ν ↔ 69/10 ≤ ν (Rv 0) := by
  simp [hostGuard, mR, turbine_startup_gearratio_IRv2, Run.lowerF, Run.lowerE, hp69, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g3 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 3)) ν ↔ ν (Rv 0) < 2 := by
  simp [hostGuard, mR, turbine_startup_gearratio_IRv2, Run.lowerF, Run.lowerE, hp20, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR turbine_startup_gearratio_IRv2 = 1 := by
  simp [epsR, turbine_startup_gearratio_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- A coordinate between `a` and `c` lies in any interval containing both. -/
theorem between_bounds {a c y lo hi : ℝ} (hb : min a c ≤ y ∧ y ≤ max a c) (h1 : lo ≤ a)
    (h2 : lo ≤ c) (h3 : a ≤ hi) (h4 : c ≤ hi) : lo ≤ y ∧ y ≤ hi :=
  ⟨le_trans (le_min h1 h2) hb.1, le_trans hb.2 (max_le h3 h4)⟩

/-- **Assumption 1 for `turbine_startup_gearratio`**, every mode, Z3-free. -/
theorem turbine_startup_gearratio_wellFormedR :
    WellFormedR Gr guardR (epsR turbine_startup_gearratio_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq4, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
  have hcr : 0 ≤ cR q ∧ cR q ≤ 121/10 := by unfold cR; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR q) (cR q) hk (fR0_eval q hq4)
      (fun i hi s => fRo_eval q hq4 i hi s) ?_ 1 (by norm_num)
    intro v h1 h2
    show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2 hcr.2)⟩
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
      have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2]) (le_refl ((15:ℝ)/2))
      by_cases h69 : Φ t (Rv 0) < 69/10
      · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_g1 _).mpr ⟨hy.1, h69⟩⟩
      · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide), (sat_g2 _).mpr (by linarith)⟩
    · -- GEN: contracts toward 12.1 from w ≥ 6.9, so the run stays at or above 6.9 (invariant)
      have hgx := (sat_g2 x).mp hg
      rw [show cR 2 = 121/10 by norm_num [cR]] at hb
      exact ⟨edgeW 2 2, edge_mem 2 2 (by decide),
        (sat_g2 _).mpr (le_trans (le_min hgx (by norm_num)) hb.1)⟩
    · -- STOP: decays toward 0 from w < 2, so the run stays below 2 (invariant)
      have hgx := (sat_g3 x).mp hg
      rw [show cR 3 = 0 by norm_num [cR]] at hb
      exact ⟨edgeW 3 3, edge_mem 3 3 (by decide),
        (sat_g3 _).mpr (lt_of_le_of_lt hb.2 (max_lt hgx (by norm_num)))⟩

end V2TurbineStartupGearratio
end RelCertifier

