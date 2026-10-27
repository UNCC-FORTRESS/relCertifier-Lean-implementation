/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_twospeed`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant and of the stretches: over the right
automaton `Gr` (the file's six nominal modes and their declared `next` lists), the lowered
right guards, and `ε_r = 1` read from the file.

Every right mode is a proportional pump controller `x' = k (c − x)` inside the tank
`0 ≤ x ≤ 25`: `Fast` (`k = 2`, `c = 12.5`, guard `[2, 7)`), `Slow` (`1`, `12.5`, `[7, 10)`),
`MidEco` (`0.5`, `17`, `[10, 17)`), `MidBoost` (`1`, `17`, `[10, 17)`), `High` (`1`, `17`,
`x ≥ 17`) and the sink `PumpOff` (`x' = 0`, read as `k = 0`, guard `x < 2`).
* Existence (i), every mode: the explicit exponential (`hwfB'`, `WellFormedFlowB_contract`; the
  set point lies in `[0, 25]`, so the run stays in the tank).
* (ii), style (b) for `Fast`: a run rises from `x₀ ≥ 2` and stays strictly below `12.5`, so it
  ends in `Fast` (`< 7`), `Slow` (`[7, 10)`) or `MidEco` (`[10, 17)`), all declared successors.
  Style (b) for `Slow`: it ends in `[7, 12.5)`, inside `Slow` or `MidEco`.
* (ii), style (a) for `MidEco` and `MidBoost` (the run rises from `x₀ ≥ 10` and stays strictly
  below `17`, as `x₀ < 17`), `High` (it falls toward `17` and stays `≥ 17`) and `PumpOff`
  (frozen: `x < 2` is kept); the self-loop is declared in every mode.
Z3-free; modelled on the old three-mode `WatertankTwospeed.lean` (same lowering, run lemmas).
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.watertank_twospeed

namespace RelCertifier
namespace V2WatertankTwospeed

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["x"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := watertank_twospeed_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp125 : Run.parseRat "12.5" = some ((25:ℚ)/2) := by
  have h : parseQ "12.5" = some (⟨125, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp170 : Run.parseRat "17.0" = some (17 : ℚ) := by
  have h : parseQ "17.0" = some (⟨170, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp70 : Run.parseRat "7.0" = some (7 : ℚ) := by
  have h : parseQ "7.0" = some (⟨70, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## The right fields, domain and guards, evaluated -/

/-- Right gains: `Fast` 2, `Slow` 1, `MidEco` 0.5, `MidBoost` 1, `High` 1, `PumpOff` 0. -/
noncomputable def kR : ℕ → ℝ
  | 0 => 2
  | 1 => 1
  | 2 => 1/2
  | 3 => 1
  | 4 => 1
  | _ => 0

/-- Right set points: `12.5` (`Fast`, `Slow`), `17` (`MidEco`, `MidBoost`, `High`); `PumpOff`
has gain 0, its set point `2` (the guard's bound) is a free choice. -/
noncomputable def cRc : ℕ → ℝ
  | 0 => 25/2
  | 1 => 25/2
  | 2 => 17
  | 3 => 17
  | 4 => 17
  | _ => 2

theorem kR_nonneg (q : ℕ) : 0 ≤ kR q := by
  unfold kR; split <;> norm_num

theorem cRc_mem (q : ℕ) : 0 ≤ cRc q ∧ cRc q ≤ 25 := by
  unfold cRc; split <;> norm_num

theorem fR0_eval (q : ℕ) (hq : q < 6) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (cRc q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, watertank_twospeed_IRv2, vs, Run.dynOf, Run.lowerE, hp20, hp10,
      hp05, hp125, hp170, hp00, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv, kR, cRc]

theorem fR1_eval (q : ℕ) (hq : q < 6) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, watertank_twospeed_IRv2, vs, Run.dynOf, Run.lowerE, hp20, hp10,
      hp05, hp125, hp170, hp00, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 25) := by
  simp only [domR, hostEvolve, mR, watertank_twospeed_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp250, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (Fast 0, Slow 1, MidEco 2, MidBoost 3, High 4,
PumpOff 5), in the file's order. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 5),
   (1, 1), (1, 2), (1, 3),
   (2, 2), (2, 3), (2, 4),
   (3, 3), (3, 2), (3, 4),
   (4, 4), (4, 2), (4, 3),
   (5, 5)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4, modeW 5]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 6) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 6 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 5 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 6 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-- `Fast`: `2 ≤ x < 7`. -/
theorem sat_g0 (ν : State (Var 2)) :
    Formula.sat (guardR 0) ν ↔ (2 ≤ ν (Rv 0) ∧ ν (Rv 0) < 7) := by
  simp [guardR, hostGuard, mR, watertank_twospeed_IRv2, Run.lowerF, Run.lowerE, hp20, hp70, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `Slow`: `7 ≤ x < 10`. -/
theorem sat_g1 (ν : State (Var 2)) :
    Formula.sat (guardR 1) ν ↔ (7 ≤ ν (Rv 0) ∧ ν (Rv 0) < 10) := by
  simp [guardR, hostGuard, mR, watertank_twospeed_IRv2, Run.lowerF, Run.lowerE, hp70, hp100, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `MidEco`: `10 ≤ x < 17`. -/
theorem sat_g2 (ν : State (Var 2)) :
    Formula.sat (guardR 2) ν ↔ (10 ≤ ν (Rv 0) ∧ ν (Rv 0) < 17) := by
  simp [guardR, hostGuard, mR, watertank_twospeed_IRv2, Run.lowerF, Run.lowerE, hp100, hp170,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `MidBoost`: `10 ≤ x < 17`. -/
theorem sat_g3 (ν : State (Var 2)) :
    Formula.sat (guardR 3) ν ↔ (10 ≤ ν (Rv 0) ∧ ν (Rv 0) < 17) := by
  simp [guardR, hostGuard, mR, watertank_twospeed_IRv2, Run.lowerF, Run.lowerE, hp100, hp170,
    vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `High`: `x ≥ 17`. -/
theorem sat_g4 (ν : State (Var 2)) :
    Formula.sat (guardR 4) ν ↔ 17 ≤ ν (Rv 0) := by
  simp [guardR, hostGuard, mR, watertank_twospeed_IRv2, Run.lowerF, Run.lowerE, hp170, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `PumpOff`: `x < 2`. -/
theorem sat_g5 (ν : State (Var 2)) :
    Formula.sat (guardR 5) ν ↔ ν (Rv 0) < 2 := by
  simp [guardR, hostGuard, mR, watertank_twospeed_IRv2, Run.lowerF, Run.lowerE, hp20, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## Existence: every right mode is a contraction toward a set point inside `[0, 25]` -/

/-- Existence at any nonnegative stretch (Assumption 1 needs the unit one). -/
theorem hwfB' (q : ℕ) (hq : q < 6) (lamv : ℝ) (hlv : 0 ≤ lamv) (dt : ℝ) :
    WellFormedFlowB (fR q) (Term.const lamv) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (lamv * kR q) (cRc q))
    (lam := Term.const 1) (domR := bandDom 0 0 25) ?_ ?_ ?_
  · intro i x
    match i with
    | 0 =>
        simp only [Term.eval, AOp.interp, contractF, if_true]
        rw [fR0_eval q hq]
        ring
    | 1 =>
        simp only [Term.eval, AOp.interp, contractF]
        rw [fR1_eval q hq]
        simp [Term.eval]
  · intro x
    rw [sat_domR]
    simp [bandDom, Formula.sat, CompOp.interp, Term.eval]
  · exact WellFormedFlowB_contract 0 (lamv * kR q) (cRc q) 0 25 dt
      (mul_nonneg hlv (kR_nonneg q)) (cRc_mem q).1 (cRc_mem q).2

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR watertank_twospeed_IRv2 = 1 := by
  simp [epsR, watertank_twospeed_IRv2, hp10]

theorem fieldR (q : ℕ) (hq : q < 6) (s : State (Var 2)) :
    Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) := by
  rw [eval_unit_mul, fR0_eval q hq]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `watertank_twospeed`**, every mode, Z3-free. -/
theorem watertank_twospeed_wellFormedR :
    WellFormedR Gr guardR (epsR watertank_twospeed_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq6, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_of_wellFormedFlowB (by norm_num) (hwfB' q hq6 1 zero_le_one 1) hd, ?_⟩
  intro t Φ _ H
  have hf : ∀ s, Formula.sat (modeW q).dom s →
      Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) :=
    fun s _ => fieldR q hq6 s
  have pick : ∀ t', (q, t') ∈ edgeList → Formula.sat (guardR t') (Φ t) →
      ∃ e ∈ Gr.edgesFrom q, Formula.sat (guardR e.tgt) (Φ t) :=
    fun t' he hs => ⟨edgeW q t', edge_mem q t' he, hs⟩
  have hup : x (Rv 0) ≤ cRc q → x (Rv 0) ≤ Φ t (Rv 0) ∧ Φ t (Rv 0) ≤ cRc q :=
    fun h => H.linear_up (memR q) _ _ (kR_nonneg q) hf h
  have hlt : x (Rv 0) < cRc q → Φ t (Rv 0) < cRc q :=
    fun h => H.linear_lt (memR q) _ _ hf h
  have hdn : cRc q ≤ x (Rv 0) → cRc q ≤ Φ t (Rv 0) ∧ Φ t (Rv 0) ≤ x (Rv 0) :=
    fun h => H.linear_down (memR q) _ _ (kR_nonneg q) hf h
  interval_cases q
  · -- Fast: the run rises from `x₀ ≥ 2` and stays below 12.5: Fast, Slow or MidEco
    have hgx := (sat_g0 x).mp hg
    simp only [cRc] at hup hlt
    have h1 := (hup (by linarith)).1
    have h2 := hlt (by linarith)
    by_cases h7 : Φ t (Rv 0) < 7
    · exact pick 0 (by decide) ((sat_g0 _).mpr ⟨by linarith, h7⟩)
    · by_cases h10 : Φ t (Rv 0) < 10
      · exact pick 1 (by decide) ((sat_g1 _).mpr ⟨by linarith, h10⟩)
      · exact pick 2 (by decide) ((sat_g2 _).mpr ⟨by linarith, by linarith⟩)
  · -- Slow: the run rises from `x₀ ≥ 7` and stays below 12.5: Slow or MidEco
    have hgx := (sat_g1 x).mp hg
    simp only [cRc] at hup hlt
    have h1 := (hup (by linarith)).1
    have h2 := hlt (by linarith)
    by_cases h10 : Φ t (Rv 0) < 10
    · exact pick 1 (by decide) ((sat_g1 _).mpr ⟨by linarith, h10⟩)
    · exact pick 2 (by decide) ((sat_g2 _).mpr ⟨by linarith, by linarith⟩)
  · -- MidEco: `[10, 17)` is kept (rises toward 17, strictly below it)
    have hgx := (sat_g2 x).mp hg
    simp only [cRc] at hup hlt
    exact pick 2 (by decide) ((sat_g2 _).mpr
      ⟨by linarith [(hup (by linarith)).1], hlt hgx.2⟩)
  · -- MidBoost: `[10, 17)` is kept
    have hgx := (sat_g3 x).mp hg
    simp only [cRc] at hup hlt
    exact pick 3 (by decide) ((sat_g3 _).mpr
      ⟨by linarith [(hup (by linarith)).1], hlt hgx.2⟩)
  · -- High: `x ≥ 17` is kept (falls toward 17)
    have hgx := (sat_g4 x).mp hg
    simp only [cRc] at hdn
    exact pick 4 (by decide) ((sat_g4 _).mpr (hdn hgx).1)
  · -- PumpOff: gain 0, `x < 2` is kept
    have hgx := (sat_g5 x).mp hg
    simp only [cRc] at hlt
    exact pick 5 (by decide) ((sat_g5 _).mpr (hlt hgx))

end V2WatertankTwospeed
end RelCertifier

