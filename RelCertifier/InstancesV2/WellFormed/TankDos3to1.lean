/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tank_dos_3to1`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
two modes and their declared `next` lists), the lowered right guards, and `ε_r = 1` read from
the file.

Both pump speeds are contractions `h' = 0.1 (c − h)` inside the tank `[0, 2]` (`HIGH` toward
`c = 1.3`, `LOW` toward `c = 0.7`); the guards `[0, 1)` and `[1, 2]` partition the tank.
* Existence (i): the explicit exponential (`hwfB`, unit stretch).
* (ii), style (b) for both modes: a `HIGH` run ends in `[h₀, 1.3]`, a `LOW` run in `[0.7, h₀]`,
  both inside `[0, 2]`, so the end state lies in `HIGH`'s or `LOW`'s guard and the edge into
  that mode is declared.
Z3-free; modelled on `WatertankTwospeed.lean`.
-/
import RelCertifier.InstancesV2.BenchIR.tank_dos_3to1
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace V2TankDos3to1

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["h"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := tank_dos_3to1_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp13 : Run.parseRat "1.3" = some ((13:ℚ)/10) := by
  have h : parseQ "1.3" = some (⟨13, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp07 : Run.parseRat "0.7" = some ((7:ℚ)/10) := by
  have h : parseQ "0.7" = some (⟨7, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- Right fields: `h' = 0.1 (c_q − h)` (`HIGH` 1.3, `LOW` 0.7). -/
noncomputable def kR (_q : ℕ) : ℝ := 1/10
noncomputable def cRc (q : ℕ) : ℝ := if q = 0 then 13/10 else 7/10

theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (cRc q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, tank_dos_3to1_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp13, hp07,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR, cRc]

theorem fR1_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, tank_dos_3to1_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp13, hp07,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 2) := by
  simp only [domR, hostEvolve, mR, tank_dos_3to1_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp20, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (HIGH 0, LOW 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 0), (1, 1)]

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

/-- The right guards, evaluated (HIGH `[0, 1)`, LOW `[1, 2]`). -/
theorem sat_guardR (q : ℕ) (hq : q < 2) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔
      (if q = 0 then 0 ≤ ν (Rv 0) ∧ ν (Rv 0) < 1 else 1 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 2) := by
  interval_cases q <;>
    simp [hostGuard, mR, tank_dos_3to1_IRv2, Run.lowerF, Run.lowerE, hp00, hp10, hp20, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## Existence: every right mode is a contraction inside `[0, 2]` -/

theorem hwfB (q : ℕ) (hq : q < 2) (dt : ℝ) :
    WellFormedFlowB (fR q) (Term.const 1) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (kR q) (cRc q))
    (lam := Term.const 1) (domR := bandDom 0 0 2) ?_ ?_ ?_
  · intro i x
    match i with
    | 0 =>
        simp only [Term.eval, AOp.interp, contractF, if_true]
        rw [fR0_eval q hq]
    | 1 =>
        simp only [Term.eval, AOp.interp, contractF]
        rw [fR1_eval q hq]
        simp [Term.eval]
  · intro x
    rw [sat_domR]
    simp [bandDom, Formula.sat, CompOp.interp, Term.eval]
  · refine WellFormedFlowB_contract 0 (kR q) (cRc q) 0 2 dt ?_ ?_ ?_
    · unfold kR; norm_num
    · unfold cRc; split_ifs <;> norm_num
    · unfold cRc; split_ifs <;> norm_num

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR tank_dos_3to1_IRv2 = 1 := by
  simp [epsR, tank_dos_3to1_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem fieldR (q : ℕ) (hq : q < 2) (s : State (Var 2)) :
    Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) := by
  rw [eval_unit_mul, fR0_eval q hq]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `tank_dos_3to1`**, every mode, Z3-free. -/
theorem tank_dos_3to1_wellFormedR : WellFormedR Gr guardR (epsR tank_dos_3to1_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR q hq2 x).mp hg
  refine ⟨?_, ?_⟩
  · exact exists_of_wellFormedFlowB (by norm_num) (hwfB q hq2 1) hd
  · intro t Φ _ H
    have hk : 0 ≤ kR q := by unfold kR; norm_num
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) :=
      fun s _ => fieldR q hq2 s
    -- the end state lies in [0, 2]: in HIGH's guard below 1, in LOW's guard from 1 on
    have pick : ∀ y, 0 ≤ y → y ≤ 2 → Φ t (Rv 0) = y →
        ∃ e ∈ Gr.edgesFrom q, Formula.sat (guardR e.tgt) (Φ t) := by
      intro y h0 h2 hy
      by_cases h1 : Φ t (Rv 0) < 1
      · refine ⟨edgeW q 0, edge_mem q 0 (by interval_cases q <;> decide), ?_⟩
        exact (sat_guardR 0 (by norm_num) _).mpr (by simp only [if_true]; constructor <;> linarith)
      · refine ⟨edgeW q 1, edge_mem q 1 (by interval_cases q <;> decide), ?_⟩
        exact (sat_guardR 1 (by norm_num) _).mpr (by norm_num; constructor <;> linarith)
    interval_cases q
    · -- HIGH: the level rises toward 1.3, so the run ends in [h₀, 1.3]
      simp only [if_true] at hgx
      have hup := H.linear_up (memR 0) _ _ hk hf (by simp only [cRc, if_true]; linarith)
      simp only [cRc, if_true] at hup
      exact pick _ (by linarith [hup.1]) (by linarith [hup.2]) rfl
    · -- LOW: the level falls toward 0.7, so the run ends in [0.7, h₀]
      norm_num at hgx
      have hdn := H.linear_down (memR 1) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hdn; norm_num at hdn
      exact pick _ (by linarith [hdn.1]) (by linarith [hdn.2]) rfl

end V2TankDos3to1
end RelCertifier
