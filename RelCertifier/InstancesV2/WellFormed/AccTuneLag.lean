/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_lag`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.
`CRUISE` (`20 ≤ v < 40`, `v' = (30 − v)/2`) and `DISENGAGE` (`v < 20`, `v' = −v/2`) are
contractions whose guard sets are forward invariant (style (a): the set point 30 lies in
`[20, 40)`, 0 in `[0, 20)`); `a` is frozen. Existence: the explicit exponential. Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.acc_tune_lag
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2AccTuneLag

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["v", "a"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := acc_tune_lag_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm100 : Run.parseRat "-10.0" = some (-10 : ℚ) := by
  have h : parseQ "-10.0" = some (⟨-100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem fR0_eval (x : State (Var 2)) : Term.eval (fR 0 0) x = 1/2 * (30 - x (Rv 0)) := by
  simp [fR, hostDyn, mR, acc_tune_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300, hp0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem fR1_eval (x : State (Var 2)) : Term.eval (fR 0 1) x = 0 := by
  simp [fR, hostDyn, mR, acc_tune_lag_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300, hp0,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 40) ∧ (-10 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 10) := by
  simp only [domR, hostEvolve, mR, acc_tune_lag_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp400, hpm100, hp100, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  tauto

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (CRUISE 0, DISENGAGE 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- `CRUISE`'s guard, evaluated (`20 ≤ v < 40`). -/
theorem sat_guardR0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔ 20 ≤ ν (Rv 0) ∧ ν (Rv 0) < 40 := by
  simp [hostGuard, mR, acc_tune_lag_IRv2, Run.lowerF, Run.lowerE, hp200, hp400, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]


theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem epsR_eq : epsR acc_tune_lag_IRv2 = 1 := by
  simp [epsR, acc_tune_lag_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

noncomputable def kR (_q : ℕ) : ℝ := 1/2
noncomputable def cRc (q : ℕ) : ℝ := if q = 0 then 30 else 0

theorem fR0_eval' (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (cRc q - x (Rv 0)) := by
  interval_cases q
  · rw [fR0_eval]; simp [kR, cRc]
  · simp [fR, hostDyn, mR, acc_tune_lag_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, kR, cRc]
    ring

theorem fR1_eval' (q : ℕ) (hq : q < 2) (x : State (Var 2)) : Term.eval (fR q 1) x = 0 := by
  interval_cases q
  · exact fR1_eval x
  · simp [fR, hostDyn, mR, acc_tune_lag_IRv2, vs, Run.dynOf, Run.lowerE, hpm05, hp0,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv]

theorem sat_guardR1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔ ν (Rv 0) < 20 := by
  simp [hostGuard, mR, acc_tune_lag_IRv2, Run.lowerF, Run.lowerE, hp200, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `acc_tune_lag`**, every mode, Z3-free. -/
theorem acc_tune_lag_wellFormedR : WellFormedR Gr guardR (epsR acc_tune_lag_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hk : 0 ≤ kR q := by simp [kR]
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR q) (cRc q) hk (fR0_eval' q hq2) ?_ ?_ 1 (by norm_num)
    · intro i hi s
      match i, hi with
      | 1, _ => exact fR1_eval' q hq2 s
    · intro v h1 h2
      have hcr : 0 ≤ cRc q ∧ cRc q ≤ 40 := by unfold cRc; split_ifs <;> norm_num
      show Formula.sat domR _
      rw [sat_domR, trajJ_j, trajJ_Rv_ne x 0 _ 0 (by decide)]
      refine ⟨⟨?_, ?_⟩, hdx.2⟩
      · exact le_trans (le_min hdx.1.1 hcr.1) h1
      · exact le_trans h2 (max_le hdx.1.2 hcr.2)
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_eval' q hq2]
    have hb := H.linear_between (memR q) _ _ hk hf
    interval_cases q
    · -- CRUISE: [20, 40) invariant
      have hgx := (sat_guardR0 x).mp hg
      simp only [cRc, if_true] at hb
      refine ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR0 _).mpr ⟨?_, ?_⟩⟩
      · exact le_trans (le_min hgx.1 (by norm_num)) hb.1
      · exact lt_of_le_of_lt hb.2 (max_lt hgx.2 (by norm_num))
    · -- DISENGAGE: [0, 20) invariant
      have hgx := (sat_guardR1 x).mp hg
      have hdn := H.linear_down (memR 1) _ _ hk hf (by simp [cRc]; linarith [hdx.1.1])
      refine ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR1 _).mpr ?_⟩
      linarith [hdn.2]

end V2AccTuneLag
end RelCertifier
