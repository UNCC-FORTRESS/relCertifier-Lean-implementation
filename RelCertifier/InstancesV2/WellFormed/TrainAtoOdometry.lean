/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `train_ato_odometry`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three modes and their declared `next` lists), the lowered right guards, and `ε_r = 0.5` read
from the file.

The right model is the design train with calibrated odometry: in every performance level the
ATO speed loop is the contraction `v' = k (25 − v)` (`PL1` `k = 0.05`, `PL2` `k = 0.045`, `PL3`
`k = 0.04`), evolve domain = every guard = `[5, 27.08]`, which contains the set point 25.
* Existence (i), every mode: the explicit exponential `25 + (v₀ − 25) e^{−k t}`
  (`WellFormedFlowB_contract` at unit stretch), inside the band for every duration.
* (ii), every mode `invariant`: a run ends in the evolve domain, which is the mode's own guard,
  and the self-edge `q → q` is declared.
Z3-free; modelled on `TankDos3to1.lean`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.train_ato_odometry

namespace RelCertifier
namespace V2TrainAtoOdometry

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["v"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := train_ato_odometry_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp005 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp0045 : Run.parseRat "0.045" = some ((9:ℚ)/200) := by
  have h : parseQ "0.045" = some (⟨45, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp004 : Run.parseRat "0.04" = some ((1:ℚ)/25) := by
  have h : parseQ "0.04" = some (⟨4, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp2708 : Run.parseRat "27.08" = some ((677:ℚ)/25) := by
  have h : parseQ "27.08" = some (⟨2708, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- Right loop gains: `PL1` 0.05, `PL2` 0.045, `PL3` 0.04 (set point 25 in every level). -/
noncomputable def kR (q : ℕ) : ℝ := if q = 0 then 1/20 else if q = 1 then 9/200 else 1/25

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (25 - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, train_ato_odometry_IRv2, vs, Run.dynOf, Run.lowerE, hp005, hp0045,
      hp004, hp250, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR]

theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, train_ato_odometry_IRv2, vs, Run.dynOf, Run.lowerE, hp005, hp0045,
      hp004, hp250, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (5 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 677/25) := by
  simp only [domR, hostEvolve, mR, train_ato_odometry_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp50, hp2708, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (PL1 0, PL2 1, PL3 2): every level declares every
level. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- The right guards, evaluated: every level's guard is the band `[5, 27.08]`. -/
theorem sat_guardR (q : ℕ) (hq : q < 3) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔ (5 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 677/25) := by
  interval_cases q <;>
    simp [hostGuard, mR, train_ato_odometry_IRv2, Run.lowerF, Run.lowerE, hp50, hp2708, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## Existence: every right mode is a contraction toward 25 inside `[5, 27.08]` -/

theorem hwfB (q : ℕ) (hq : q < 3) (dt : ℝ) :
    WellFormedFlowB (fR q) (Term.const 1) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (kR q) 25)
    (lam := Term.const 1) (domR := bandDom 0 5 (677/25)) ?_ ?_ ?_
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
  · refine WellFormedFlowB_contract 0 (kR q) 25 5 (677/25) dt ?_ ?_ ?_
    · unfold kR; split_ifs <;> norm_num
    · norm_num
    · norm_num

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR train_ato_odometry_IRv2 = 1/2 := by
  simp [epsR, train_ato_odometry_IRv2, hp05]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-- **Assumption 1 for `train_ato_odometry`**, every mode, Z3-free. -/
theorem train_ato_odometry_wellFormedR :
    WellFormedR Gr guardR (epsR train_ato_odometry_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_of_wellFormedFlowB (by norm_num) (hwfB q hq3 (1/2)) hd, ?_⟩
  -- every level is invariant: the end state is in the band, the mode's own guard
  intro t Φ _ H
  refine ⟨edgeW q q, edge_mem q q (by interval_cases q <;> decide), ?_⟩
  exact (sat_guardR q hq3 _).mpr ((sat_domR _).mp H.end_dom)

end V2TrainAtoOdometry
end RelCertifier

