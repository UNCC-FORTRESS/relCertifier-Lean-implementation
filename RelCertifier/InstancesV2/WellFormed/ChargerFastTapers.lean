/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_tapers`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.
* `BULK` (`15 ≤ x < 80`, `x' = 0.1 (100 − x)`), style (b): within one interval a run ends
  in `[x₀, 100 − (100 − x₀) e^{−0.1}] ⊆ [15, 99)` (the closed form at the run's duration
  `t ≤ 1`), inside `BULK` or `ABSORB_SLOW` (`[80, 99)`).
* `ABSORB_SLOW` / `ABSORB_FAST` (`80 ≤ x < 99`, `x' = k (100 − x)`), style (b): a run ends in
  `[x₀, 100)`, inside the mode itself or `FULL` (`x ≥ 99`).
* `FULL` (`x ≥ 99`, frozen) and `FAULT` (`x < 10`, `x' = −0.01 x`), style (a).
Existence: the explicit exponential. Z3-free.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.Proofs.Soundness.UniformEvol
import RelCertifier.InstancesV2.BenchIR.charger_fast_tapers
import RelCertifier.Proofs.Encoding.ReplayOne
import RelCertifier.Proofs.Encoding.ContractRun
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ChargerFastTapers

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["x"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := charger_fast_tapers_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp005 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp007 : Run.parseRat "0.07" = some ((7:ℚ)/100) := by
  have h : parseQ "0.07" = some (⟨7, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp150 : Run.parseRat "15.0" = some (15 : ℚ) := by
  have h : parseQ "15.0" = some (⟨150, 10⟩ : QF) := by decide
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
/-- Right fields of the non-sink modes: `x' = k_q (100 − x)` (`BULK` 1/10, `ABSORB_SLOW`
1/20, `ABSORB_FAST` 7/100, `FULL` 0). -/
noncomputable def kR (q : ℕ) : ℝ :=
  if q = 0 then 1/10 else if q = 1 then 1/20 else if q = 2 then 7/100 else 0

theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (100 - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, charger_fast_tapers_IRv2, vs, Run.dynOf, Run.lowerE, hp01,
      hp005, hp007, hp1000, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv, kR]

theorem fR1_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, charger_fast_tapers_IRv2, vs, Run.dynOf, Run.lowerE, hp01,
      hp005, hp007, hp1000, hp0, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 100) := by
  simp only [domR, hostEvolve, mR, charger_fast_tapers_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp1000, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (BULK 0, ABSORB_SLOW 1, ABSORB_FAST 2, FULL 3,
FAULT 4). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 0), (0, 4), (1, 3), (1, 1), (2, 3), (2, 2), (3, 3), (4, 4)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 5) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
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

/-- The non-sink right guards, evaluated (`BULK`: `[15, 80)`; `ABSORB_SLOW`, `ABSORB_FAST`:
`[80, 99)`; `FULL`: `x ≥ 99`). -/
theorem sat_guardR (q : ℕ) (hq : q < 4) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔
      (if q = 0 then 15 ≤ ν (Rv 0) ∧ ν (Rv 0) < 80
       else if q = 3 then 99 ≤ ν (Rv 0) else 80 ≤ ν (Rv 0) ∧ ν (Rv 0) < 99) := by
  interval_cases q <;>
    simp [hostGuard, mR, charger_fast_tapers_IRv2, Run.lowerF, Run.lowerE, hp150, hp800,
      hp990, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]


theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm001 : Run.parseRat "-0.01" = some (-(1:ℚ)/100) := by
  have h : parseQ "-0.01" = some (⟨-1, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR charger_fast_tapers_IRv2 = 1 := by
  simp [epsR, charger_fast_tapers_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

noncomputable def kR5 (q : ℕ) : ℝ := if q < 4 then kR q else 1/100
noncomputable def cR5 (q : ℕ) : ℝ := if q < 4 then 100 else 0

theorem fR0_all (q : ℕ) (hq : q < 5) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR5 q * (cR5 q - x (Rv 0)) := by
  by_cases h4 : q < 4
  · rw [fR0_eval q h4]; simp [kR5, cR5, h4]
  · have : q = 4 := by omega
    subst this
    simp [fR, hostDyn, mR, charger_fast_tapers_IRv2, vs, Run.dynOf, Run.lowerE, hpm001,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, kR5, cR5]
    ring

theorem fR1_all (q : ℕ) (hq : q < 5) (x : State (Var 2)) : Term.eval (fR q 1) x = 0 := by
  by_cases h4 : q < 4
  · exact fR1_eval q h4 x
  · have : q = 4 := by omega
    subst this
    simp [fR, hostDyn, mR, charger_fast_tapers_IRv2, vs, Run.dynOf, Run.lowerE, hpm001,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

theorem sat_guardR4 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 4)) ν ↔ ν (Rv 0) < 10 := by
  simp [hostGuard, mR, charger_fast_tapers_IRv2, Run.lowerF, Run.lowerE, hp100, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem kR5_nonneg (q : ℕ) : 0 ≤ kR5 q := by
  unfold kR5 kR; split_ifs <;> norm_num

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `charger_fast_tapers`**, every mode, Z3-free. -/
theorem charger_fast_tapers_wellFormedR :
    WellFormedR Gr guardR (epsR charger_fast_tapers_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hcr : 0 ≤ cR5 q ∧ cR5 q ≤ 100 := by
    unfold cR5; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR5 q) (cR5 q) (kR5_nonneg q) (fR0_all q hq5)
      ?_ ?_ 1 (by norm_num)
    · intro i hi s
      match i, hi with
      | 1, _ => exact fR1_all q hq5 s
    · intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2 hcr.2)⟩
  · intro t Φ ht H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR5 q * (cR5 q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_all q hq5]
    interval_cases q
    · -- BULK: ends in [x₀, 99) within one interval, inside BULK or ABSORB_SLOW
      have hgx := (sat_guardR 0 (by norm_num) x).mp hg
      simp only [if_true] at hgx
      have hup := H.linear_up (memR 0) _ _ (kR5_nonneg 0) hf (by simp [cR5]; linarith)
      have hex := H.linear_exact (memR 0) _ _ hf
      simp [cR5, kR5, kR] at hup hex
      have he := Real.add_one_le_exp (-(1/10 * t))
      have h99 : Φ t (Rv 0) < 99 := by
        rw [hex]; nlinarith [H.hr]
      by_cases h80 : Φ t (Rv 0) < 80
      · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR 0 (by norm_num) _).mpr
          (by simp only [if_true]; exact ⟨by linarith, h80⟩)⟩
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide), (sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, h99⟩)⟩
    · -- ABSORB_SLOW: ends in [x₀, 100), inside itself or FULL
      have hgx := (sat_guardR 1 (by norm_num) x).mp hg
      norm_num at hgx
      have hup := H.linear_up (memR 1) _ _ (kR5_nonneg 1) hf (by simp [cR5]; linarith)
      simp [cR5] at hup
      by_cases h99 : Φ t (Rv 0) < 99
      · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, h99⟩)⟩
      · exact ⟨edgeW 1 3, edge_mem 1 3 (by decide), (sat_guardR 3 (by norm_num) _).mpr
          (by norm_num; linarith)⟩
    · -- ABSORB_FAST: the same
      have hgx := (sat_guardR 2 (by norm_num) x).mp hg
      norm_num at hgx
      have hup := H.linear_up (memR 2) _ _ (kR5_nonneg 2) hf (by simp [cR5]; linarith)
      simp [cR5] at hup
      by_cases h99 : Φ t (Rv 0) < 99
      · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_guardR 2 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, h99⟩)⟩
      · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide), (sat_guardR 3 (by norm_num) _).mpr
          (by norm_num; linarith)⟩
    · -- FULL: frozen
      have hgx := (sat_guardR 3 (by norm_num) x).mp hg
      norm_num at hgx
      have hup := H.linear_up (memR 3) _ _ (kR5_nonneg 3) hf (by simp [cR5]; linarith)
      exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR 3 (by norm_num) _).mpr
        (by norm_num; linarith [hup.1])⟩
    · -- FAULT: [0, 10) invariant
      have hgx := (sat_guardR4 x).mp hg
      have hdn := H.linear_down (memR 4) _ _ (kR5_nonneg 4) hf (by simp [cR5]; linarith)
      exact ⟨edgeW 4 4, edge_mem 4 4 (by decide), (sat_guardR4 _).mpr (by linarith [hdn.2])⟩

end V2ChargerFastTapers
end RelCertifier
