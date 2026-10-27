/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_tapers`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 0.006`
(the control period 0.36 s in the file's time unit, the minute).
Dimension 3 (the keyed bridge's padding for a one-variable file: coordinate 0 is the state of
charge `x`, 1 and 2 are frozen). Every mode is a contraction `x' = k_q (c_q − x)` inside the
evolve domain `[0, 100]`.
* `PRECHARGE` (`10 ≤ x < 15`, `x' = 0.2 (20 − x)`), style (b): a run ends in `[x₀, 20)`,
  inside `PRECHARGE` or `BULK` (`[15, 80)`).
* `BULK` (`15 ≤ x < 80`, `x' = 0.1 (100 − x)`), style (b): within one interval a run ends
  in `[x₀, 100 − (100 − x₀) e^{−0.1 t}] ⊆ [15, 99)` (the closed form at the run's duration
  `t ≤ 0.006`), inside `BULK` or `ABSORB_SLOW` (`[80, 99)`).
* `ABSORB_SLOW` / `ABSORB_FAST` (`80 ≤ x < 99`, `x' = k (100 − x)`), style (b): a run ends in
  `[x₀, 100]`, inside the mode itself or `FULL` (`x ≥ 99`).
* `FULL` (`x ≥ 99`, frozen) and `FAULT` (`x < 10`, `x' = −0.01 x`), style (a).
Existence: the explicit exponential. Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.charger_fast_tapers
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ChargerFastTapers

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["x"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := charger_fast_tapers_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp005 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp007 : Run.parseRat "0.07" = some ((7:ℚ)/100) := by
  have h : parseQ "0.07" = some (⟨7, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm001 : Run.parseRat "-0.01" = some (-(1:ℚ)/100) := by
  have h : parseQ "-0.01" = some (⟨-1, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp0006 : Run.parseRat "0.006" = some ((3:ℚ)/500) := by
  have h : parseQ "0.006" = some (⟨6, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp150 : Run.parseRat "15.0" = some (15 : ℚ) := by
  have h : parseQ "15.0" = some (⟨150, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp800 : Run.parseRat "80.0" = some (80 : ℚ) := by
  have h : parseQ "80.0" = some (⟨800, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp990 : Run.parseRat "99.0" = some (99 : ℚ) := by
  have h : parseQ "99.0" = some (⟨990, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp1000 : Run.parseRat "100.0" = some (100 : ℚ) := by
  have h : parseQ "100.0" = some (⟨1000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## The right fields -/

/-- Right fields `x' = k_q (c_q − x)` (PRECHARGE 0, BULK 1, ABSORB_SLOW 2, ABSORB_FAST 3,
FULL 4, FAULT 5): `PRECHARGE` 1/5 toward 20, `BULK` 1/10 toward 100, `ABSORB_SLOW` 1/20 and
`ABSORB_FAST` 7/100 toward 100, `FULL` 0, `FAULT` 1/100 toward 0. -/
noncomputable def kR (q : ℕ) : ℝ :=
  if q = 0 then 1/5 else if q = 1 then 1/10 else if q = 2 then 1/20 else if q = 3 then 7/100
  else if q = 4 then 0 else 1/100
noncomputable def cRc (q : ℕ) : ℝ :=
  if q = 0 then 20 else if q = 5 then 0 else 100

theorem fR0_eval (q : ℕ) (hq : q < 6) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR q * (cRc q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, charger_fast_tapers_IRv2, vs, Run.dynOf, Run.lowerE, hp02, hp01,
      hp005, hp007, hpm001, hp200, hp1000, hp0, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, kR, cRc]
  all_goals ring

theorem fRo_eval (q : ℕ) (hq : q < 6) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | ⟨1, _⟩, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, charger_fast_tapers_IRv2, vs, Run.dynOf, Run.lowerE, hp02,
        hp01, hp005, hp007, hpm001, hp200, hp1000, hp0, Run.resolveVar, List.findIdx?_cons,
        List.finRange, ITerm.toHost, Term.eval]
  | ⟨2, _⟩, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, charger_fast_tapers_IRv2, vs, Run.dynOf, Run.lowerE, hp02,
        hp01, hp005, hp007, hpm001, hp200, hp1000, hp0, Run.resolveVar, List.findIdx?_cons,
        List.finRange, ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 100) := by
  simp only [domR, hostEvolve, mR, charger_fast_tapers_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp1000, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (PRECHARGE 0, BULK 1, ABSORB_SLOW 2, ABSORB_FAST 3,
FULL 4, FAULT 5). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 0), (0, 5), (1, 2), (1, 3), (1, 1), (1, 5), (2, 4), (2, 2), (3, 4), (3, 3),
    (4, 4), (5, 5)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4, modeW 5]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 6) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 6 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 5 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 6 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## The right guards, evaluated -/

theorem sat_guard0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔ (10 ≤ ν (Rv 0) ∧ ν (Rv 0) < 15) := by
  simp [hostGuard, mR, charger_fast_tapers_IRv2, Run.lowerF, Run.lowerE, hp100, hp150, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔ (15 ≤ ν (Rv 0) ∧ ν (Rv 0) < 80) := by
  simp [hostGuard, mR, charger_fast_tapers_IRv2, Run.lowerF, Run.lowerE, hp150, hp800, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_guard2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔ (80 ≤ ν (Rv 0) ∧ ν (Rv 0) < 99) := by
  simp [hostGuard, mR, charger_fast_tapers_IRv2, Run.lowerF, Run.lowerE, hp800, hp990, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_guard3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔ (80 ≤ ν (Rv 0) ∧ ν (Rv 0) < 99) := by
  simp [hostGuard, mR, charger_fast_tapers_IRv2, Run.lowerF, Run.lowerE, hp800, hp990, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_guard4 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 4)) ν ↔ 99 ≤ ν (Rv 0) := by
  simp [hostGuard, mR, charger_fast_tapers_IRv2, Run.lowerF, Run.lowerE, hp990, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_guard5 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 5)) ν ↔ ν (Rv 0) < 10 := by
  simp [hostGuard, mR, charger_fast_tapers_IRv2, Run.lowerF, Run.lowerE, hp100, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem epsR_eq : epsR charger_fast_tapers_IRv2 = 3/500 := by
  simp [epsR, charger_fast_tapers_IRv2, hp0006]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem kR_nonneg (q : ℕ) : 0 ≤ kR q := by
  unfold kR; split_ifs <;> norm_num

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `charger_fast_tapers`**, every mode, Z3-free. -/
theorem charger_fast_tapers_wellFormedR :
    WellFormedR Gr guardR (epsR charger_fast_tapers_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq6, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hcr : 0 ≤ cRc q ∧ cRc q ≤ 100 := by
    unfold cRc; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR q) (cRc q) (kR_nonneg q) (fR0_eval q hq6)
      (fun i hi s => fRo_eval q hq6 i hi s) ?_ (3/500) (by norm_num)
    intro v h1 h2
    show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2 hcr.2)⟩
  · intro t Φ ht H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_eval q hq6]
    interval_cases q
    · -- PRECHARGE: ends in [x₀, 20), inside PRECHARGE or BULK
      have hgx := (sat_guard0 x).mp hg
      have hup := H.linear_up (memR 0) _ _ (kR_nonneg 0) hf (by simp [cRc]; linarith)
      have hlt := H.linear_lt (memR 0) _ _ hf (by simp [cRc]; linarith)
      simp [cRc] at hup hlt
      by_cases h15 : Φ t (Rv 0) < 15
      · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guard0 _).mpr ⟨by linarith, h15⟩⟩
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
          (sat_guard1 _).mpr ⟨by linarith, by linarith⟩⟩
    · -- BULK: ends in [x₀, 99) within one interval, inside BULK or ABSORB_SLOW
      have hgx := (sat_guard1 x).mp hg
      have hup := H.linear_up (memR 1) _ _ (kR_nonneg 1) hf (by simp [cRc]; linarith)
      have hex := H.linear_exact (memR 1) _ _ hf
      simp [cRc, kR] at hup hex
      have he := Real.add_one_le_exp (-(1/10 * t))
      have h99 : Φ t (Rv 0) < 99 := by
        rw [hex]; nlinarith [H.hr]
      by_cases h80 : Φ t (Rv 0) < 80
      · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guard1 _).mpr ⟨by linarith, h80⟩⟩
      · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide),
          (sat_guard2 _).mpr ⟨by linarith, h99⟩⟩
    · -- ABSORB_SLOW: ends in [x₀, 100], inside itself or FULL
      have hgx := (sat_guard2 x).mp hg
      have hup := H.linear_up (memR 2) _ _ (kR_nonneg 2) hf (by simp [cRc]; linarith)
      simp [cRc] at hup
      by_cases h99 : Φ t (Rv 0) < 99
      · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_guard2 _).mpr ⟨by linarith, h99⟩⟩
      · exact ⟨edgeW 2 4, edge_mem 2 4 (by decide), (sat_guard4 _).mpr (by linarith)⟩
    · -- ABSORB_FAST: the same
      have hgx := (sat_guard3 x).mp hg
      have hup := H.linear_up (memR 3) _ _ (kR_nonneg 3) hf (by simp [cRc]; linarith)
      simp [cRc] at hup
      by_cases h99 : Φ t (Rv 0) < 99
      · exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guard3 _).mpr ⟨by linarith, h99⟩⟩
      · exact ⟨edgeW 3 4, edge_mem 3 4 (by decide), (sat_guard4 _).mpr (by linarith)⟩
    · -- FULL: frozen
      have hgx := (sat_guard4 x).mp hg
      have hup := H.linear_up (memR 4) _ _ (kR_nonneg 4) hf (by simp [cRc]; linarith)
      exact ⟨edgeW 4 4, edge_mem 4 4 (by decide), (sat_guard4 _).mpr (by linarith [hup.1])⟩
    · -- FAULT: [0, 10) invariant
      have hgx := (sat_guard5 x).mp hg
      have hdn := H.linear_down (memR 5) _ _ (kR_nonneg 5) hf (by simp [cRc]; linarith)
      exact ⟨edgeW 5 5, edge_mem 5 5 (by decide), (sat_guard5 _).mpr (by linarith [hdn.2])⟩

end V2ChargerFastTapers
end RelCertifier
