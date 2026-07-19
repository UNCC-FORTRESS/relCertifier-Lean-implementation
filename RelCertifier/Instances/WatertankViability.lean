/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S3 — watertank's existence residuals, fully discharged

Every watertank right mode is an exact contract field (`x' = (3/25)·(c_q − x)` with
`c_q ∈ {12.5, 25, 2.5}` inside the band `[0, 25]`), so the settling arc's explicit
exponential witness (`WellFormedFlowB_contract`) discharges the bounded existence
residual COMPLETELY — no Z3, no growth budget, equilibrium anchors included. The
`watertank_modal_certified` wrapper feeds the discharge into the S1 gate: the theorem's
only remaining residuals are the six joint route verdicts (`VerdW`).

Kernel facts: the lowered field/evolve literals (probe-verified), by the established
`simp`+`decide` route; the contract transfer is semantic (`WellFormedFlowB_transfer`).
-/
import RelCertifier.Instances.WatertankModal
import RelCertifier.Proofs.Flow.FaceBridge

namespace RelCertifier
namespace WatertankModal

open DL DLRel Parse Set

/-! ## The lowered field and evolve literals (kernel facts) -/

theorem hdyn0_W (q : ℕ) (hq : q < 3) :
    (Run.dynOf vsM 2 Side.R (mRW q)).map (fun f => f 0)
      = some (ITerm.bin .mul (ITerm.rat 3) (ITerm.bin .sub
          (ITerm.rat (if q = 0 then (1:ℚ)/2 else if q = 1 then 1 else (1:ℚ)/10))
          (ITerm.bin .mul (ITerm.var (Side.R, 0)) (ITerm.rat ((1:ℚ)/25))))) := by
  interval_cases q <;>
    · simp [mRW, vsM, watertank_IR, Run.dynOf, Run.lowerE, Run.resolveVar, Run.parseRat,
        parseQ, parseQChars, parseQChars.parseQPos, parseQChars.splitDot,
        digitsToNat, digitsToNat.go, qOfInt, qAdd, qMul, qPow10,
        List.findIdx?, List.findIdx?.go, List.mapM, List.mapM.loop, List.finRange,
        (show "3".data = ['3'] from rfl), (show "0.5".data = ['0','.','5'] from rfl),
        (show "1.0".data = ['1','.','0'] from rfl),
        (show "0.1".data = ['0','.','1'] from rfl),
        (show "0.04".data = ['0','.','0','4'] from rfl),
        (show "0.0".data = ['0','.','0'] from rfl),
        (show "25.0".data = ['2','5','.','0'] from rfl), qNeg]
      try norm_num

theorem hdyn1_W (q : ℕ) (hq : q < 3) :
    (Run.dynOf vsM 2 Side.R (mRW q)).map (fun f => f 1) = some (ITerm.rat 0) := by
  interval_cases q <;>
    · simp [mRW, vsM, watertank_IR, Run.dynOf, Run.lowerE, Run.resolveVar, Run.parseRat,
        parseQ, parseQChars, parseQChars.parseQPos, parseQChars.splitDot,
        digitsToNat, digitsToNat.go, qOfInt, qAdd, qMul, qPow10,
        List.findIdx?, List.findIdx?.go, List.mapM, List.mapM.loop, List.finRange,
        (show "3".data = ['3'] from rfl), (show "0.5".data = ['0','.','5'] from rfl),
        (show "1.0".data = ['1','.','0'] from rfl),
        (show "0.1".data = ['0','.','1'] from rfl),
        (show "0.04".data = ['0','.','0','4'] from rfl),
        (show "0.0".data = ['0','.','0'] from rfl),
        (show "25.0".data = ['2','5','.','0'] from rfl), qNeg]
      try norm_num

theorem hlowR_W :
    Run.lowerF vsM 2 Side.R (mRW 0).evolve
      = some (IForm.and
          (IForm.cmp .ge (ITerm.var (Side.R, 0)) (ITerm.rat 0))
          (IForm.cmp .le (ITerm.var (Side.R, 0)) (ITerm.rat 25))) := by
  simp [mRW, vsM, watertank_IR, Run.lowerF, Run.lowerE, Run.resolveVar, Run.parseRat,
    parseQ, parseQChars, parseQChars.parseQPos, parseQChars.splitDot,
    digitsToNat, digitsToNat.go, qOfInt, qAdd, qMul, qPow10,
    List.findIdx?, List.findIdx?.go, List.mapM, List.mapM.loop, List.finRange,
    (show "3".data = ['3'] from rfl), (show "0.5".data = ['0','.','5'] from rfl),
    (show "1.0".data = ['1','.','0'] from rfl),
    (show "0.1".data = ['0','.','1'] from rfl),
    (show "0.04".data = ['0','.','0','4'] from rfl),
    (show "0.0".data = ['0','.','0'] from rfl),
    (show "25.0".data = ['2','5','.','0'] from rfl), qNeg]
  try norm_num

/-! ## The contract transfer per right mode -/

/-- The per-mode contract center. -/
noncomputable def cW (q : ℕ) : ℝ := if q = 0 then 25/2 else if q = 1 then 25 else 5/2

theorem fRW_coord0 (q : ℕ) (hq : q < 3) :
    fRW q 0 = (ITerm.bin .mul (ITerm.rat 3) (ITerm.bin .sub
        (ITerm.rat (if q = 0 then (1:ℚ)/2 else if q = 1 then 1 else (1:ℚ)/10))
        (ITerm.bin .mul (ITerm.var (Side.R, 0))
          (ITerm.rat ((1:ℚ)/25)))) : ITerm 2).toHost := by
  rw [fRW_pipe]
  rw [show (fun f : Fin 2 → ITerm 2 => ITerm.toHost (f 0))
    = ITerm.toHost ∘ (fun f => f 0) from rfl, ← Option.map_map]
  rw [show ((some (mRW q)).bind (Run.dynOf vsM 2 Side.R))
    = Run.dynOf vsM 2 Side.R (mRW q) from rfl]
  rw [hdyn0_W q hq]
  rfl

theorem fRW_coord1 (q : ℕ) (hq : q < 3) :
    fRW q 1 = (ITerm.rat 0 : ITerm 2).toHost := by
  rw [fRW_pipe]
  rw [show (fun f : Fin 2 → ITerm 2 => ITerm.toHost (f 1))
    = ITerm.toHost ∘ (fun f => f 1) from rfl, ← Option.map_map]
  rw [show ((some (mRW q)).bind (Run.dynOf vsM 2 Side.R))
    = Run.dynOf vsM 2 Side.R (mRW q) from rfl]
  rw [hdyn1_W q hq]
  rfl

theorem hev_W (q : ℕ) (hq : q < 3) :
    ∀ (i : Fin 2) (x : DL.State (Var 2)),
      Term.eval (Term.binop .mul (Term.const 1) (fRW q i)) x
        = Term.eval (Term.binop .mul (Term.const 1)
            (contractF 0 (3/25) (cW q) i)) x := by
  intro i x
  match i with
  | 0 =>
      interval_cases q <;>
        · rw [fRW_coord0 _ (by norm_num)]
          simp only [ITerm.toHost, contractF, cW, reduceIte, Term.eval, AOp.interp]
          push_cast
          ring
  | 1 =>
      rw [fRW_coord1 q hq]
      simp [ITerm.toHost, contractF, Term.eval, AOp.interp]

theorem hdom_W : ∀ x : DL.State (Var 2),
    Formula.sat domRW x ↔ Formula.sat (bandDom 0 0 25) x := by
  intro x
  rw [domRW_pipe]
  rw [show ((some (mRW 0)).bind (fun m => Run.lowerF vsM 2 Side.R m.evolve))
    = Run.lowerF vsM 2 Side.R (mRW 0).evolve from rfl]
  rw [hlowR_W]
  simp only [Option.map_some, Option.getD_some, IForm.toHost, ITerm.toHost, bandDom,
    Formula.sat, CompOp.interp, Term.eval]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · push_cast at h1 ⊢
      linarith
    · push_cast at h2 ⊢
      linarith
  · rintro ⟨h1, h2⟩
    constructor
    · push_cast at h1 ⊢
      linarith
    · push_cast at h2 ⊢
      linarith

/-- **The bounded flow well-formedness of every watertank right mode** — the explicit
exponential contract witness, transferred to the lowered data. -/
theorem hwfB_W (q : ℕ) (hq : q < 3) (dt : ℝ) :
    WellFormedFlowB (fRW q) (Term.const 1) domRW dt := by
  refine WellFormedFlowB_transfer (hev_W q hq) hdom_W ?_
  refine WellFormedFlowB_contract 0 (3/25) (cW q) 0 25 dt (by norm_num) ?_ ?_
  · interval_cases q <;> simp [cW] <;> norm_num
  · interval_cases q <;> simp [cW] <;> norm_num

/-! ## The full existence discharge -/

/-- **Every watertank existence residual holds** — no Z3, no budget, all anchors. -/
theorem watertank_ESW (l q : ℕ) (hq : q < 3) (dt : ℝ) : ESW l q dt := by
  intro σ hσ
  refine hExistSegB_of_wellFormedFlowB (fLW l) (fRW q) (Term.const 1) domLW domRW dt _
    (hwfB_W q hq dt) ?_ ?_
  · intro x hx hb
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLW l) _ hb
    obtain ⟨j, hj⟩ := hdomRW hx
    rw [← hj] at hi
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · have hσR : Formula.sat domRW σ := hσ.2.2
    have htgd : tgM ∉ domRW.fv := by
      intro h
      obtain ⟨i, hi⟩ := hdomRW h
      exact absurd hi (by simp [Rv, Prod.ext_iff])
    rwa [(Formula.coincidence domRW (fun v hv =>
      Function.update_of_ne (fun hc => htgd (by rw [← hc]; exact hv)) _ _) :
        Formula.sat domRW _ ↔ Formula.sat domRW σ)]

/-- **The S1 gate, existence-certified.** `watertank_modal` with every `ESW` residual
discharged by the contract witnesses: the only remaining residuals are the six joint
route verdicts. -/
theorem watertank_modal_certified (dt : ℝ)
    (h00 : VerdW 0 0) (h01 : VerdW 0 1) (h11 : VerdW 1 1)
    (h20 : VerdW 2 0) (h21 : VerdW 2 1) (h22 : VerdW 2 2) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsW dt))
      (rightAutomatonBody GrW mvM)
      (RFormula.and (RFormula.and (canonInv gW) (envLR domLW domRW))
        (mvValidR mvM GrW.modes.length))) :=
  watertank_modal dt h00 h01 h11 h20 h21 h22
    (watertank_ESW 0 0 (by norm_num) dt) (watertank_ESW 0 1 (by norm_num) dt)
    (watertank_ESW 1 1 (by norm_num) dt) (watertank_ESW 2 0 (by norm_num) dt)
    (watertank_ESW 2 1 (by norm_num) dt) (watertank_ESW 2 2 (by norm_num) dt)

end WatertankModal
end RelCertifier
