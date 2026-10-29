/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_gpt10_boost_converter`: Assumption 1 of the right model (affine flows, whole space)

Stated directly over the generic bridge's automaton `grOf IR 3 pruned` (no standalone
instance): the lowered right guards, `ε_r = 0.5`. The right model is the boost DC-DC converter
of Girard, Pola, Tabuada (TAC 2010, Sec. 5.1) in the rescaled state `[il, 5 vc]` (coordinates 0
and 1; the padding coordinate 2 has field 0): `P1` (`il' = a il + b`, `z' = c z`) and `P2`
(`il' = d il + e z + b`, `z' = f il + c z`), guards and evolve domain the constant atom
`0.0 ≤ 1.0` (every state), each mode a successor of each.
* Existence (i): both fields are affine with coefficients below `0.1` in absolute value, so
  globally `1`-Lipschitz; a run of every length exists from every state
  (`exists_odeSol_of_lipschitz`, `Proofs/Flow/LipschitzRun.lean`), trivially in the domain.
* Completeness (ii): every guard is the constant atom, so the end state of every run enables
  the declared self-loop. Z3-free.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Flow.LipschitzRun
import RelCertifier.InstancesV2.BenchIR.lit_gpt10_boost_converter

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2LitGpt10BoostConverter

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.lit_gpt10_boost_converter_IRv2

/-! ## Parse pins -/

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1 : ℚ) / 2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpa : Run.parseRat "-0.0166666666667" = some (-(166666666667 : ℚ) / 10000000000000) := by
  have h : parseQ "-0.0166666666667" = some (⟨-166666666667, 10000000000000⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpb : Run.parseRat "0.333333333333" = some ((333333333333 : ℚ) / 1000000000000) := by
  have h : parseQ "0.333333333333" = some (⟨333333333333, 1000000000000⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpc : Run.parseRat "-0.0142146410803" = some (-(142146410803 : ℚ) / 10000000000000) := by
  have h : parseQ "-0.0142146410803" = some (⟨-142146410803, 10000000000000⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpd : Run.parseRat "-0.0183250414594" = some (-(183250414594 : ℚ) / 10000000000000) := by
  have h : parseQ "-0.0183250414594" = some (⟨-183250414594, 10000000000000⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpe : Run.parseRat "-0.0663349917081" = some (-(663349917081 : ℚ) / 10000000000000) := by
  have h : parseQ "-0.0663349917081" = some (⟨-663349917081, 10000000000000⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpf : Run.parseRat "0.0710732054016" = some ((710732054016 : ℚ) / 10000000000000) := by
  have h : parseQ "0.0710732054016" = some (⟨710732054016, 10000000000000⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem epsR_eq : epsR IR = 1 / 2 := by
  simp [epsR, IR, Parse.lit_gpt10_boost_converter_IRv2, hp05]

theorem nR_eq : nR IR = 2 := rfl

/-! ## The right fields, evaluated -/

/-- The coefficient of `il` in coordinate `i` of mode `q`. -/
noncomputable def cA (q : ℕ) (i : Fin 3) : ℝ :=
  if i.val = 0 then (if q = 0 then -(166666666667 : ℝ) / 10000000000000
    else -(183250414594 : ℝ) / 10000000000000)
  else if i.val = 1 then (if q = 0 then 0 else (710732054016 : ℝ) / 10000000000000) else 0

/-- The coefficient of `z` in coordinate `i` of mode `q`. -/
noncomputable def cB (q : ℕ) (i : Fin 3) : ℝ :=
  if i.val = 0 then (if q = 0 then 0 else -(663349917081 : ℝ) / 10000000000000)
  else if i.val = 1 then -(142146410803 : ℝ) / 10000000000000 else 0

/-- The constant term of coordinate `i` (the source voltage, the same in both modes). -/
noncomputable def cC (i : Fin 3) : ℝ :=
  if i.val = 0 then (333333333333 : ℝ) / 1000000000000 else 0

theorem fR_eval (q : ℕ) (hq : q < 2) (s : State (Var 3)) (i : Fin 3) :
    Term.eval (fR IR 3 q i) s = cA q i * s (Rv 0) + cB q i * s (Rv 1) + cC i := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.lit_gpt10_boost_converter_IRv2, Run.dynOf,
      Run.lowerE, hp00, hpa, hpb, hpc, hpd, hpe, hpf, Run.resolveVar, List.findIdx?_cons,
      List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cA, cB, cC]

theorem coef_le (q : ℕ) (i : Fin 3) : |cA q i| + |cB q i| ≤ 1 := by
  unfold cA cB
  split_ifs <;> norm_num [abs_of_neg, abs_of_nonneg]

/-- Every right field moves by at most the sup distance: the block is `1`-Lipschitz. -/
theorem lipR (q : ℕ) (hq : q < 2) :
    LipschitzWith (Real.toNNReal 1) (odeField (rightBlock (fR IR 3 q) (Term.const 1))) := by
  apply lipschitz_rightBlock (fR IR 3 q) 1 zero_le_one
  intro j x y
  rw [fR_eval q hq x j, fR_eval q hq y j]
  have h := affine2_sub_le (cA q j) (cB q j) x y (Rv 0) (Rv 1)
  have hd : (0 : ℝ) ≤ dist x y := dist_nonneg
  calc |cA q j * x (Rv 0) + cB q j * x (Rv 1) + cC j - (cA q j * y (Rv 0) + cB q j * y (Rv 1) + cC j)|
      = |cA q j * (x (Rv 0) - y (Rv 0)) + cB q j * (x (Rv 1) - y (Rv 1))| := by ring_nf
    _ ≤ (|cA q j| + |cB q j|) * dist x y := h
    _ ≤ 1 * dist x y := mul_le_mul_of_nonneg_right (coef_le q j) hd

/-! ## Domain and guards -/

theorem sat_domR_iff (s : State (Var 3)) : Formula.sat (domR IR 3) s ↔ (0 : ℝ) ≤ 1 := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.lit_gpt10_boost_converter_IRv2, Run.lowerF,
    Run.lowerE, hp00, hp10, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
    Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

/-- The evolve domain is the whole state space (the constant atom `0 ≤ 1`). -/
theorem sat_domR (s : State (Var 3)) : Formula.sat (domR IR 3) s :=
  (sat_domR_iff s).mpr zero_le_one

theorem sat_guardR (q : ℕ) (hq : q < 2) (s : State (Var 3)) : Formula.sat (guardR IR 3 q) s := by
  interval_cases q <;>
    simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_gpt10_boost_converter_IRv2, Run.lowerF,
      Run.lowerE, hp00, hp10, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
      Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]

theorem p1_next : "P1" ∈ (mRof IR 0).next := by decide
theorem p2_next : "P2" ∈ (mRof IR 1).next := by decide

theorem tgt_p1 : tgtIdx IR "P1" = 0 := by decide
theorem tgt_p2 : tgtIdx IR "P2" = 1 := by decide

/-- **Assumption 1 for `lit_gpt10_boost_converter`**, every mode, over the bridge's automaton. -/
theorem lit_gpt10_boost_converter_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 3 pruned) (guardR IR 3) (epsR IR) := by
  rw [epsR_eq]
  intro q hq m hm x _ _ _
  obtain ⟨hq2, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq2
  refine ⟨exists_odeSol_of_lipschitz (rightBlock_wellFormed _ _) sat_domR (lipR q hq2) x
    (1 / 2) (by norm_num), ?_⟩
  intro t Φ _ _
  interval_cases q
  · refine ⟨edgeOf IR 3 pruned 0 "P1", edge_mem_grOf (by rw [nR_eq]; norm_num) p1_next, ?_⟩
    simp only [edgeOf, tgt_p1]
    exact sat_guardR 0 (by norm_num) _
  · refine ⟨edgeOf IR 3 pruned 1 "P2", edge_mem_grOf (by rw [nR_eq]; norm_num) p2_next, ?_⟩
    simp only [edgeOf, tgt_p2]
    exact sat_guardR 1 (by norm_num) _

end V2LitGpt10BoostConverter
end RelCertifier
