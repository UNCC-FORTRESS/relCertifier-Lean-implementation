/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_limp`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1/10` (the 0.1 s decision period; 1 until 2026-10-27).
The stock controller has two modes since 2026-10-30 (review round 6 removed `COMFORT` and `SPORT`;
`NORMAL.next = [NORMAL, DISENGAGE]`). `NORMAL` (`20 ≤ v ≤ 40`, `v' = (30 − v)/2`) and
`DISENGAGE` (`v < 20`, `v' = −v/10`; `−v/2` until 2026-10-28) are contractions whose guard sets are forward invariant
(style (a)). Existence: the explicit exponential. Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.acc_tune_limp
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2AccTuneLimp

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["v"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := acc_tune_limp_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10 : ℚ) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm01 : Run.parseRat "-0.1" = some (-(1:ℚ)/10) := by
  have h : parseQ "-0.1" = some (⟨-1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-- Right fields: `v' = k_q (c_q − v)` (`NORMAL`: `k = 1/2`, `c = 30`; `DISENGAGE`: `k = 1/10`,
`c = 0`). -/
noncomputable def kR2 (q : ℕ) : ℝ := if q = 0 then 1/2 else 1/10
noncomputable def cR2 (q : ℕ) : ℝ := if q = 0 then 30 else 0

theorem kR2_nonneg (q : ℕ) : 0 ≤ kR2 q := by unfold kR2; split_ifs <;> norm_num

theorem fR0_all (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR2 q * (cR2 q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300, hpm01,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, kR2, cR2] <;> ring

theorem fRo_all (q : ℕ) (hq : q < 2) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | 1, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300, hpm01,
        Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
        AOp.interp, Rv]
  | 2, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300, hpm01,
        Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
        AOp.interp, Rv]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 40) := by
  simp only [domR, hostEvolve, mR, acc_tune_limp_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp400, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (NORMAL 0, DISENGAGE 1). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (1, 1)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The right guards, evaluated (`NORMAL`: `20 ≤ v ≤ 40`; `DISENGAGE`: `v < 20`). -/
theorem sat_guardR (q : ℕ) (hq : q < 2) (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) ν ↔
      (if q = 0 then 20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 40 else ν (Rv 0) < 20) := by
  interval_cases q <;>
    simp [hostGuard, mR, acc_tune_limp_IRv2, Run.lowerF, Run.lowerE, hp200, hp400, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

theorem epsR_eq : epsR acc_tune_limp_IRv2 = 1/10 := by
  simp [epsR, acc_tune_limp_IRv2, hp01]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `acc_tune_limp`**, every mode, Z3-free. -/
theorem acc_tune_limp_wellFormedR : WellFormedR Gr guardR (epsR acc_tune_limp_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hcr : 0 ≤ cR2 q ∧ cR2 q ≤ 40 := by
    unfold cR2; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR2 q) (cR2 q) (kR2_nonneg q) (fR0_all q hq2)
      (fun i hi s => fRo_all q hq2 i hi s) ?_ (1/10) (by norm_num)
    intro v h1 h2
    show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2 hcr.2)⟩
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR2 q * (cR2 q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_all q hq2]
    have hb := H.linear_between (memR q) _ _ (kR2_nonneg q) hf
    have hgx := (sat_guardR q hq2 x).mp hg
    by_cases h0 : q = 0
    · -- NORMAL: [20, 40] invariant (set point 30 inside)
      subst h0
      simp only [if_true] at hgx
      simp only [cR2, if_true] at hb
      refine ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR 0 hq2 _).mpr ?_⟩
      simp only [if_true]
      exact ⟨le_trans (le_min hgx.1 (by norm_num)) hb.1,
        le_trans hb.2 (max_le hgx.2 (by norm_num))⟩
    · have : q = 1 := by omega
      subst this
      simp only [show ¬ (1:ℕ) = 0 from by norm_num, if_false] at hgx
      have hdn := H.linear_down (memR 1) _ _ (kR2_nonneg 1) hf
        (by simp [cR2]; linarith [hdx.1])
      refine ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR 1 hq2 _).mpr ?_⟩
      simp only [show ¬ (1:ℕ) = 0 from by norm_num, if_false]
      linarith [hdn.2]

end V2AccTuneLimp
end RelCertifier
