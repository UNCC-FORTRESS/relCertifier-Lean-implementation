/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Watertank — the verdict column

IR mirrors of the six `VerdW` route-query triples that `watertank_modal_certified`
hypothesizes, with kernel identity theorems `mirror.toHost = hypothesis-query`.
The runner (`--run-verdicts`) prints exactly these mirrors and runs Z3; an `unsat`
on any route of a pair discharges that pair's `VerdW` empirically.
-/
import RelCertifier.Verdicts.Mirrors
import RelCertifier.Instances.WatertankViability

namespace RelCertifier
namespace WatertankVerdicts

open DL Parse WatertankModal

/-! ## IR components (probe-verified literals + kernel identities) -/

def gWI : ITerm 2 :=
  ITerm.bin .sub (ITerm.var (Side.L, 0))
    (ITerm.bin .add (ITerm.var (Side.R, 0)) (ITerm.rat 3))

def fLWI (l : ℕ) : Fin 2 → ITerm 2 := fun i =>
  if i = 0 then
    ITerm.bin .mul (ITerm.rat 3) (ITerm.bin .sub (ITerm.rat (if l = 0 then (3:ℚ)/5 else if l = 1 then 1 else (1:ℚ)/10))
      (ITerm.bin .mul (ITerm.var (Side.L, 0)) (ITerm.rat ((1:ℚ)/25))))
  else ITerm.rat 0

def fRWI (q : ℕ) : Fin 2 → ITerm 2 := fun i =>
  if i = 0 then
    ITerm.bin .mul (ITerm.rat 3) (ITerm.bin .sub (ITerm.rat (if q = 0 then (1:ℚ)/2 else if q = 1 then 1 else (1:ℚ)/10))
      (ITerm.bin .mul (ITerm.var (Side.R, 0)) (ITerm.rat ((1:ℚ)/25))))
  else ITerm.rat 0

def domLWI : IForm 2 :=
  IForm.and (IForm.cmp .ge (ITerm.var (Side.L, 0)) (ITerm.rat 0))
    (IForm.cmp .le (ITerm.var (Side.L, 0)) (ITerm.rat 25))

def domRWI : IForm 2 :=
  IForm.and (IForm.cmp .ge (ITerm.var (Side.R, 0)) (ITerm.rat 0))
    (IForm.cmp .le (ITerm.var (Side.R, 0)) (ITerm.rat 25))

theorem hinv_W :
    Run.invToG vsM 2 ((watertank_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)
      = some gWI := by
  simp [mLW, mRW, vsM, watertank_IR, Run.dynOf, Run.lowerF, Run.lowerE,
    Run.resolveVar, Run.parseRat, Run.invToG,
    parseQ, parseQChars, parseQChars.parseQPos, parseQChars.splitDot,
    digitsToNat, digitsToNat.go, qOfInt, qAdd, qMul, qPow10, qNeg,
    gWI, fLWI, fRWI, domLWI, domRWI, Parse.dr,
    (show ("L_x".drop 2).copy = "x" from rfl), (show ("R_x".drop 2).copy = "x" from rfl),
    List.findIdx?, List.findIdx?.go, List.mapM, List.mapM.loop, List.finRange,
    (show "3".data = ['3'] from rfl), (show "0.6".data = ['0','.','6'] from rfl),
    (show "0.5".data = ['0','.','5'] from rfl),
    (show "1.0".data = ['1','.','0'] from rfl),
    (show "0.1".data = ['0','.','1'] from rfl),
    (show "0.04".data = ['0','.','0','4'] from rfl),
    (show "0.0".data = ['0','.','0'] from rfl),
    (show "25.0".data = ['2','5','.','0'] from rfl)]
  try norm_num

theorem hdynL0_W (l : ℕ) (hl : l < 3) :
    (Run.dynOf vsM 2 Side.L (mLW l)).map (fun f => f 0) = some (fLWI l 0) := by
  interval_cases l <;>
    · simp [mLW, mRW, vsM, watertank_IR, Run.dynOf, Run.lowerF, Run.lowerE,
        Run.resolveVar, Run.parseRat, Run.invToG,
        parseQ, parseQChars, parseQChars.parseQPos, parseQChars.splitDot,
        digitsToNat, digitsToNat.go, qOfInt, qAdd, qMul, qPow10, qNeg,
    gWI, fLWI, fRWI, domLWI, domRWI, Parse.dr,
    (show ("L_x".drop 2).copy = "x" from rfl), (show ("R_x".drop 2).copy = "x" from rfl),
        List.findIdx?, List.findIdx?.go, List.mapM, List.mapM.loop, List.finRange,
        (show "3".data = ['3'] from rfl), (show "0.6".data = ['0','.','6'] from rfl),
        (show "0.5".data = ['0','.','5'] from rfl),
        (show "1.0".data = ['1','.','0'] from rfl),
        (show "0.1".data = ['0','.','1'] from rfl),
        (show "0.04".data = ['0','.','0','4'] from rfl),
        (show "0.0".data = ['0','.','0'] from rfl),
        (show "25.0".data = ['2','5','.','0'] from rfl)]
      try norm_num

theorem hdynL1_W (l : ℕ) (hl : l < 3) :
    (Run.dynOf vsM 2 Side.L (mLW l)).map (fun f => f 1) = some (fLWI l 1) := by
  interval_cases l <;>
    · simp [mLW, mRW, vsM, watertank_IR, Run.dynOf, Run.lowerF, Run.lowerE,
        Run.resolveVar, Run.parseRat, Run.invToG,
        parseQ, parseQChars, parseQChars.parseQPos, parseQChars.splitDot,
        digitsToNat, digitsToNat.go, qOfInt, qAdd, qMul, qPow10, qNeg,
    gWI, fLWI, fRWI, domLWI, domRWI, Parse.dr,
    (show ("L_x".drop 2).copy = "x" from rfl), (show ("R_x".drop 2).copy = "x" from rfl),
        List.findIdx?, List.findIdx?.go, List.mapM, List.mapM.loop, List.finRange,
        (show "3".data = ['3'] from rfl), (show "0.6".data = ['0','.','6'] from rfl),
        (show "0.5".data = ['0','.','5'] from rfl),
        (show "1.0".data = ['1','.','0'] from rfl),
        (show "0.1".data = ['0','.','1'] from rfl),
        (show "0.04".data = ['0','.','0','4'] from rfl),
        (show "0.0".data = ['0','.','0'] from rfl),
        (show "25.0".data = ['2','5','.','0'] from rfl)]
      try norm_num

theorem hlowL_W :
    Run.lowerF vsM 2 Side.L (mLW 0).evolve = some domLWI := by
  simp [mLW, mRW, vsM, watertank_IR, Run.dynOf, Run.lowerF, Run.lowerE,
    Run.resolveVar, Run.parseRat, Run.invToG,
    parseQ, parseQChars, parseQChars.parseQPos, parseQChars.splitDot,
    digitsToNat, digitsToNat.go, qOfInt, qAdd, qMul, qPow10, qNeg,
    gWI, fLWI, fRWI, domLWI, domRWI, Parse.dr,
    (show ("L_x".drop 2).copy = "x" from rfl), (show ("R_x".drop 2).copy = "x" from rfl),
    List.findIdx?, List.findIdx?.go, List.mapM, List.mapM.loop, List.finRange,
    (show "3".data = ['3'] from rfl), (show "0.6".data = ['0','.','6'] from rfl),
    (show "0.5".data = ['0','.','5'] from rfl),
    (show "1.0".data = ['1','.','0'] from rfl),
    (show "0.1".data = ['0','.','1'] from rfl),
    (show "0.04".data = ['0','.','0','4'] from rfl),
    (show "0.0".data = ['0','.','0'] from rfl),
    (show "25.0".data = ['2','5','.','0'] from rfl)]
  try norm_num

/-! ## Component identities (host = mirror.toHost) -/

theorem hgW_id : gW = gWI.toHost := by
  show ((Run.invToG vsM 2 _).map ITerm.toHost).getD (Term.const 0) = _
  rw [hinv_W]
  rfl

theorem hfLW_id (l : ℕ) (hl : l < 3) : fLW l = fun i => (fLWI l i).toHost := by
  funext i
  match i with
  | 0 =>
      rw [fLW_pipe]
      rw [show (fun f : Fin 2 → ITerm 2 => ITerm.toHost (f 0))
        = ITerm.toHost ∘ (fun f => f 0) from rfl, ← Option.map_map]
      rw [show ((some (mLW l)).bind (Run.dynOf vsM 2 Side.L))
        = Run.dynOf vsM 2 Side.L (mLW l) from rfl]
      rw [hdynL0_W l hl]
      rfl
  | 1 =>
      rw [fLW_pipe]
      rw [show (fun f : Fin 2 → ITerm 2 => ITerm.toHost (f 1))
        = ITerm.toHost ∘ (fun f => f 1) from rfl, ← Option.map_map]
      rw [show ((some (mLW l)).bind (Run.dynOf vsM 2 Side.L))
        = Run.dynOf vsM 2 Side.L (mLW l) from rfl]
      rw [hdynL1_W l hl]
      rfl

theorem hfRW_id (q : ℕ) (hq : q < 3) : fRW q = fun i => (fRWI q i).toHost := by
  funext i
  match i with
  | 0 =>
      rw [fRW_coord0 q hq]
      interval_cases q <;> rfl
  | 1 =>
      rw [fRW_coord1 q hq]
      interval_cases q <;> rfl

theorem hdomLW_id : domLW = domLWI.toHost := by
  rw [domLW_pipe]
  rw [show ((some (mLW 0)).bind (fun m => Run.lowerF vsM 2 Side.L m.evolve))
    = Run.lowerF vsM 2 Side.L (mLW 0).evolve from rfl]
  rw [hlowL_W]
  rfl

theorem hdomRW_id : domRW = domRWI.toHost := by
  rw [domRW_pipe]
  rw [show ((some (mRW 0)).bind (fun m => Run.lowerF vsM 2 Side.R m.evolve))
    = Run.lowerF vsM 2 Side.R (mRW 0).evolve from rfl]
  rw [hlowR_W]
  rfl

theorem hlam_id : Term.const (1:ℝ) = (ITerm.rat 1 : ITerm 2).toHost := by
  show Term.const (1:ℝ) = Term.const ((1:ℚ):ℝ)
  norm_num

/-! ## The mirror queries and their identities -/

def wtDomI : IForm 2 := IForm.and domLWI domRWI

def wtA (l q : ℕ) : IForm 2 := iflowQuery gWI (fLWI l) (fRWI q) (ITerm.rat 1) wtDomI
def wtB (l q : ℕ) : IForm 2 := iflowQueryStrict gWI (fLWI l) (fRWI q) (ITerm.rat 1) wtDomI
def wtC (l q : ℕ) : IForm 2 :=
  iflowQuerySuperlevel gWI (fLWI l) (fRWI q) (ITerm.rat 1) wtDomI

/-- **The printed queries ARE the hypothesized queries** (per pair, all three routes). -/
theorem wt_id (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    (wtA l q).toHost = flowQuery ⟨gW, fLW l, fRW q, Term.const 1,
        Formula.and domLW domRW⟩
    ∧ (wtB l q).toHost = flowQueryStrict ⟨gW, fLW l, fRW q, Term.const 1,
        Formula.and domLW domRW⟩
    ∧ (wtC l q).toHost = flowQuerySuperlevel ⟨gW, fLW l, fRW q, Term.const 1,
        Formula.and domLW domRW⟩ := by
  have hdom : (wtDomI).toHost = Formula.and domLW domRW := by
    show Formula.and domLWI.toHost domRWI.toHost = _
    rw [hdomLW_id, hdomRW_id]
  refine ⟨?_, ?_, ?_⟩
  · rw [wtA, iflowQuery_toHost, hgW_id, hfLW_id l hl, hfRW_id q hq, ← hlam_id, hdom]
  · rw [wtB, iflowQueryStrict_toHost, hgW_id, hfLW_id l hl, hfRW_id q hq, ← hlam_id,
      hdom]
  · rw [wtC, iflowQuerySuperlevel_toHost, hgW_id, hfLW_id l hl, hfRW_id q hq,
      ← hlam_id, hdom]

/-- **The empirical interface.** If, for each of the six pairs, SOME printed route
query is UNSAT under `z3solve` (= the printer + Z3, per the trust wording), then
`watertank_modal_certified`'s hypotheses hold. -/
theorem verdW_of_mirror (l q : ℕ) (hl : l < 3) (hq : q < 3)
    (h : z3solve (wtA l q).toHost = Verdict.unsat
       ∨ z3solve (wtB l q).toHost = Verdict.unsat
       ∨ z3solve (wtC l q).toHost = Verdict.unsat) :
    VerdW l q := by
  obtain ⟨hA, hB, hC⟩ := wt_id l q hl hq
  rw [hA, hB, hC] at h
  exact h

end WatertankVerdicts
end RelCertifier
