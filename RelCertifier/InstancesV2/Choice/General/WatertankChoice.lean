/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_choice`: the right model, the pruned automaton and Assumption 1

The running example with the economy profile: the right model (state variables, right modes,
fields, evolve domain, parse pins, field evaluations), the search graph with the edge
`Low → PumpOff` pruned (`GrP`), and Assumption 1 proved for the nominal model with the
economy set point (`wellFormedR`, at dimension 2; the bridge instance
`InstancesV2/Bridge/WatertankChoice.lean` transports it and lifts it by one for the right
clock; the bridge instance reads the emitted cut table `Choice/Cuts/watertank_choice` through this
file, so that leaf is imported here). Self-contained; the standalone Theorem 3 leaf `Choice/Modal/WatertankChoice` imports
this file for the right model. The kernel-decided covers, the window data and the hop
certificate of the retired standalone route were dropped on 2026-10-22 (history: git show
212cd42:RelCertifier/InstancesV2/Choice/General/WatertankChoice.lean).
-/
import RelCertifier.InstancesV2.Choice.BenchIR.watertank_choice
import RelCertifier.InstancesV2.Choice.Cuts.watertank_choice
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace ChoiceWatertank

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-! ## The right model -/

def vs : List String := ["x"]

def dm : PMode := ⟨"", [], .tt, .tt, []⟩

def mR (q : ℕ) : PMode := watertank_choice_IRc.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)

noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)

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

theorem hp130 : Run.parseRat "13.0" = some (13 : ℚ) := by
  have h : parseQ "13.0" = some (⟨130, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- Right fields: `x' = k_q (c_q − x)` (PumpOff: `0`). -/
noncomputable def kR (q : ℕ) : ℝ := if q = 1 then 1/2 else if q = 4 then 0 else 1

noncomputable def cRc (q : ℕ) : ℝ :=
  if q = 0 then 25/2 else if q = 1 then 13 else if q = 4 then 0 else 17

theorem fR0_eval (q : ℕ) (hq : q < 5) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (cRc q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, watertank_choice_IRc, vs, Run.dynOf, Run.lowerE, hp10, hp125, hp05,
      hp170, hp130, hp00, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR, cRc]

theorem fR1_eval (q : ℕ) (hq : q < 5) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, watertank_choice_IRc, vs, Run.dynOf, Run.lowerE, hp10, hp125, hp05,
      hp170, hp130, hp00, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 25) := by
  simp only [domR, hostEvolve, mR, watertank_choice_IRc, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp250, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, exactly as the left windows' guards are lowered): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (Low 0, MidEco 1, MidBoost 2, High 3, PumpOff 4). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 4), (1, 1), (1, 2), (1, 3), (2, 2), (2, 1), (2, 3),
   (3, 3), (3, 1), (3, 2), (4, 4)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

/-- The right guards, evaluated (Low `[2, 10)`, MidEco and MidBoost `[10, 17)`, High
`x ≥ 17`, PumpOff `x < 2`). -/
theorem sat_guardR (q : ℕ) (hq : q < 5) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔
      (if q = 0 then 2 ≤ ν (Rv 0) ∧ ν (Rv 0) < 10
       else if q = 3 then 17 ≤ ν (Rv 0)
       else if q = 4 then ν (Rv 0) < 2 else 10 ≤ ν (Rv 0) ∧ ν (Rv 0) < 17) := by
  interval_cases q <;>
    simp [hostGuard, mR, watertank_choice_IRc, Run.lowerF, Run.lowerE, hp20, hp100, hp170, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

theorem hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp [edgeW, Gr]

/-- `Low` pairs with `Low` at 2, `MidEco` at 7/2, `MidBoost` and `High` at 1 (the per-pairing
fallback); `Mid` and `High` at 1. -/
noncomputable def lam (l q : ℕ) : ℝ :=
  if l = 0 then (if q = 0 then 2 else if q = 1 then 7/2 else 1) else 1

theorem lam_pos (l q : ℕ) : 0 < lam l q := by unfold lam; split_ifs <;> norm_num

theorem hwfB (l q : ℕ) (hq : q < 5) (dt : ℝ) :
    WellFormedFlowB (fR q) (Term.const (lam l q)) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (lam l q * kR q) (cRc q))
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
  · refine WellFormedFlowB_contract 0 (lam l q * kR q) (cRc q) 0 25 dt ?_ ?_ ?_
    · exact mul_nonneg (le_of_lt (lam_pos l q)) (by unfold kR; split_ifs <;> norm_num)
    · unfold cRc; split_ifs <;> norm_num
    · unfold cRc; split_ifs <;> norm_num

/-! ## Assumption 1 for the nominal model -/

theorem epsR_eq : epsR watertank_choice_IRc = 1 := by
  simp [epsR, watertank_choice_IRc, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-- The declared edge, pruned iff it is `Low → PumpOff` (the tool's non-connection
certificate). -/
noncomputable def edgeWP (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t),
    pruned := decide (s = 0 ∧ t = 4) }

noncomputable def GrP : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeWP e.1 e.2) }

theorem GrP_modeAt (q : ℕ) (hq : q < 5) : GrP.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem GrP_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : GrP.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | q + 5 => exact absurd hm (by simp [SearchGraph.modeAt, GrP])

theorem edge_memP (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeWP s t ∈ GrP.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeWP]⟩

theorem fieldR (q : ℕ) (hq : q < 5) (s : State (Var 2)) :
    Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) := by
  rw [eval_unit_mul, fR0_eval q hq]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

theorem wellFormedR : WellFormedR GrP guardR 1 := by
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := GrP_modeAt_inv hm
  have hgx := (sat_guardR q hq5 x).mp hg
  refine ⟨?_, ?_⟩
  · have hw := hwfB 2 q hq5 1
    rw [show lam 2 q = 1 from by simp [lam]] at hw
    exact exists_of_wellFormedFlowB (by norm_num) hw hd
  · intro t Φ _ H
    have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) :=
      fun s _ => fieldR q hq5 s
    have hx0 := ((sat_domR x).mp hd).1
    have pick : ∀ t', (q, t') ∈ edgeList → t' < 5 →
        Formula.sat (hostGuard vs 2 Side.R (mR t')) (Φ t) →
        ∃ e ∈ GrP.edgesFrom q, Formula.sat (guardR e.tgt) (Φ t) :=
      fun t' he _ hs => ⟨edgeWP q t', edge_memP q t' he, hs⟩
    have hbet := H.linear_between (memR q) _ _ hk hf
    interval_cases q
    · -- Low: toward 12.5 from [2, 10): ends in [2, 12.5], inside Low or MidEco
      simp only [if_true] at hgx
      norm_num [cRc] at hbet
      obtain ⟨h1, h2⟩ := hbet
      by_cases h10 : Φ t (Rv 0) < 10
      · exact pick 0 (by decide) (by norm_num) ((sat_guardR 0 (by norm_num) _).mpr
          (by simp only [if_true]; exact ⟨by rcases h1 with h1 | h1 <;> linarith, h10⟩))
      · exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, by rcases h2 with h2 | h2 <;> linarith⟩))
    · -- MidEco: toward 13 from [10, 17): stays in [10, 17)
      norm_num at hgx
      norm_num [cRc] at hbet
      obtain ⟨h1, h2⟩ := hbet
      exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
        (by norm_num; exact ⟨by rcases h1 with h1 | h1 <;> linarith,
          by rcases h2 with h2 | h2 <;> linarith⟩))
    · -- MidBoost: toward 17 from [10, 17): stays in [10, 17)
      norm_num at hgx
      have hup := H.linear_up (memR 2) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      have hlt := H.linear_lt (memR 2) _ _ hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hup hlt; norm_num at hup hlt
      exact pick 2 (by decide) (by norm_num) ((sat_guardR 2 (by norm_num) _).mpr
        (by norm_num; exact ⟨by linarith, hlt⟩))
    · -- High: x ≥ 17 is invariant
      norm_num at hgx
      have hdn := H.linear_down (memR 3) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hdn; norm_num at hdn
      exact pick 3 (by decide) (by norm_num) ((sat_guardR 3 (by norm_num) _).mpr
        (by norm_num; exact hdn.1))
    · -- PumpOff: frozen (k = 0)
      norm_num at hgx
      have hdn := H.linear_down (memR 4) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hdn; norm_num at hdn
      exact pick 4 (by decide) (by norm_num) ((sat_guardR 4 (by norm_num) _).mpr
        (by norm_num; linarith))

/- Theorem-3 part retired 2026-10-21 with the clocked right automaton (the file was fixed at
`Var 2`, no slot for the right clock); the benchmark's Theorem 3 is the generated bridge
instance `InstancesV2/Bridge/WatertankChoice.lean`.
History: git show 61d7389:RelCertifier/InstancesV2/Choice/General/WatertankChoice.lean. -/

end ChoiceWatertank
end RelCertifier
