/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_ladder_rung_b` (suite_v2) — mode-keyed Theorem 3 at the declared rows

The suite_v2 file differs from the suite_uniform one ONLY on the left: every left guard
carries the settled-attitude entry condition `ψ, ω_ψ, θ_p, ω_θ ≥ −0.25`, and the left
attitude domains are the physical `[−1, 1]` (were `[−0.5, 0.5]`); the right system, all
odes, the invariant rows and the `next` lists are the legacy ones (`R_eq`, `inv_eq`, by
`rfl`). The floor `ψ_L ≥ −0.5` the energy rows need is no longer declared but DERIVED
through the left linear-form cut chain of the extended certificate
(`story3_rollover_ladder_rung_b_cutsV2X`): per left mode, the odometer guard conjunct
`s ≥ s_l`, the linear forms `ω_ψ + ψ ≥ −0.5`, `ω_θ + θ_p ≥ −0.5` (critically damped pairs,
`q' = −q`), and the derived floors `ψ ≥ −0.5`, `θ_p ≥ −0.5` (stratified inside their linear
form); per right mode, the odometer guard conjunct.

Reused from the legacy compiled instance `Story3RolloverRungBModal` (right-only facts): the
right fields `fRV`, domain `domRV` and its evaluation, the right graph `GrV` (one-way terrain
chain with self-loops) and its side lemmas, and the stratified right viability facts
(strict/non-strict faces, `e`-affine faces, Lipschitz and field bounds), re-plumbed in `es`
for the v2 left domain (`HExistSegB` reads the left domain only as a run hypothesis).

New here: the v2 left fields/domain/guards, the rows via `invComponents` (as the tool lowers
them, with the cover's strata orders), O1 from the kernel-checked certificate
(`cutSatL_of_guard`), O2 for every kept atom RATIONALLY (odometer floors from `s' ≥ 0` on the
domain, `super_linear_ge_L` for the linear forms, `stay_given` + `super_derived_ge_L` for the
derived floors, `boxle_thrGe_R` on the right — no Z3 probe), the cut-narrowed coupling
(`couple_cutX`), the guard-gated left automaton, the region bookkeeping (`mvRegionR`, the
right mode's kept atoms), and the in-kernel handoffs (STEEP → MODER drops `v_L ≤ v_R`;
MODER → FLAT identical rows).

Residuals: nine stratified verdict packs `Verd l q` (`modalVerdX`, the tool's own narrowed
queries: left window `l` at its own row, right mode `q`, λ = 1). Axioms: the standard three
plus `z3_unsat_sound` at those leaves.
-/
import RelCertifier.Instances.Story3RolloverRungBModal
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.InstancesV2.Cuts.story3_rollover_ladder_rung_b

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Story3RolloverRungB

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle Story3RolloverRungBModal


/-! ## The suite_v2 file against the legacy one -/

theorem stateVars_eq : story3_rollover_ladder_rung_b_IRv2.L.stateVars = vsV := rfl
theorem R_eq : story3_rollover_ladder_rung_b_IRv2.R = story3_rollover_ladder_rung_b_IR.R := rfl
theorem inv_eq : story3_rollover_ladder_rung_b_IRv2.invariants =
    story3_rollover_ladder_rung_b_IR.invariants := rfl

def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := story3_rollover_ladder_rung_b_IRv2.L.modes.getD l dm

theorem mR_eq (q : ℕ) : story3_rollover_ladder_rung_b_IRv2.R.modes.getD q dm = mRV q := by
  rw [R_eq]; rfl

abbrev mv : Var 12 := (Side.Aux, 0)
abbrev tg : Var 12 := (Side.Aux, 1)
abbrev uL : Var 12 := (Side.Aux, 2)

noncomputable def fL (l : ℕ) : Fin 12 → Term (Var 12) := hostDyn vsV 12 Side.L (mL l)
noncomputable def domL : Formula (Var 12) := hostEvolve vsV 12 Side.L (mL 0)
noncomputable def env : Formula (Var 12) := Formula.and domL domRV

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vsV 12 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) :
    hostEvolve vsV 12 Side.R (story3_rollover_ladder_rung_b_IRv2.R.modes.getD q dm) = domRV := by
  rw [mR_eq]; interval_cases q <;> rfl
theorem fR_eq (q : ℕ) :
    hostDyn vsV 12 Side.R (story3_rollover_ladder_rung_b_IRv2.R.modes.getD q dm) = fRV q := by
  rw [mR_eq]; rfl

/-! ## Parse pins (left constants) -/

theorem pq10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem pq15 : Run.parseRat "1.5" = some ((3:ℚ)/2) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem pqm15 : Run.parseRat "-1.5" = some (-(3:ℚ)/2) := by
  have h : parseQ "-1.5" = some (⟨-15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem pq14 : Run.parseRat "1.4" = some ((7:ℚ)/5) := by
  have h : parseQ "1.4" = some (⟨14, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem pqm025 : Run.parseRat "-0.25" = some (-(1:ℚ)/4) := by
  have h : parseQ "-0.25" = some (⟨-25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem pq89995 : Run.parseRat "899.95" = some ((17999:ℚ)/20) := by
  have h : parseQ "899.95" = some (⟨89995, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem pqm4 : Run.parseRat "-4" = some (-4) := by
  have h : parseQ "-4" = some (⟨-4, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem pq4 : Run.parseRat "4" = some (4) := by
  have h : parseQ "4" = some (⟨4, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## Left field evaluations (the attitude pairs and the odometer) -/

theorem fL1_eval (l : ℕ) (hl : l < 3) (x : State (Var 12)) :
    Term.eval (fL l 1) x = x (Lv 0) * ((1 - 1/2 * (x (Lv 2) * x (Lv 2))) - 3/10 * (x (Lv 4) * x (Lv 4))) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hv2, pqm4, pq4,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

theorem fL2_eval (l : ℕ) (hl : l < 3) (x : State (Var 12)) :
    Term.eval (fL l 2) x = x (Lv 3) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hv2, pqm4, pq4,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

theorem fL3_eval (l : ℕ) (hl : l < 3) (x : State (Var 12)) :
    Term.eval (fL l 3) x = -1 * (x (Lv 2) - 0) - 2 * x (Lv 3) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hv2, pqm4, pq4,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

theorem fL4_eval (l : ℕ) (hl : l < 3) (x : State (Var 12)) :
    Term.eval (fL l 4) x = x (Lv 5) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hv2, pqm4, pq4,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

theorem fL5_eval (l : ℕ) (hl : l < 3) (x : State (Var 12)) :
    Term.eval (fL l 5) x = -1 * (x (Lv 4) - 0) - 2 * x (Lv 5) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, story3_rollover_ladder_rung_b_IRv2, vsV, Run.dynOf,
      Run.lowerE, hv030, hv050, hv065, hv3, hvm1, hv0, hv1, hv05, hv03, hv2, pqm4, pq4,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

/-- The v2 left evolve, evaluated. -/
theorem sat_domL (x : State (Var 12)) : Formula.sat domL x ↔
    (-(3:ℝ)/2 ≤ x (Lv 6) ∧ x (Lv 6) ≤ (3:ℝ)/2 ∧ -(1:ℝ)/2 ≤ x (Lv 9) ∧ x (Lv 9) ≤ (1:ℝ)/2 ∧
     -(1:ℝ) ≤ x (Lv 3) ∧ x (Lv 3) ≤ 1 ∧ -(1:ℝ) ≤ x (Lv 5) ∧ x (Lv 5) ≤ 1 ∧
     -(1:ℝ)/2 ≤ x (Lv 8) ∧ x (Lv 8) ≤ (1:ℝ)/2 ∧ -(1:ℝ) ≤ x (Lv 2) ∧ x (Lv 2) ≤ 1 ∧
     -(38:ℝ)/25 ≤ x (Lv 7) ∧ x (Lv 7) ≤ (38:ℝ)/25 ∧ 0 ≤ x (Lv 1) ∧
     -(1:ℝ) ≤ x (Lv 4) ∧ x (Lv 4) ≤ 1 ∧ 0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ (4:ℝ)/5 ∧
     -(1:ℝ) ≤ x (Lv 11) ∧ x (Lv 11) ≤ (3:ℝ)/20 ∧ -(1:ℝ) ≤ x (Lv 10) ∧ x (Lv 10) ≤ (3:ℝ)/20) := by
  simp only [domL, hostEvolve, mL, story3_rollover_ladder_rung_b_IRv2, vsV]
  simp [Run.lowerF, Run.lowerE, hvm152, hv152, hvm05, hv05, pq10, hvm10, pq15, pqm15, hv015,
    hv00, hv08, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Lv]
  tauto


/-! ## The cut families (read off the extended certificate) -/

def aS (k : String) : PForm := .cmp ">=" (.var "s") (.num k)
def aLinPsi : PForm :=
  .cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0"))))
    (.num "-0.5")
def aLinTh : PForm :=
  .cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0"))))
    (.num "-0.5")
def aPsi : PForm := .cmp ">=" (.var "psi") (.num "-0.5")
def aTh : PForm := .cmp ">=" (.var "theta_p") (.num "-0.5")

/-- The odometer threshold of mode `l` (the guard's lower bound). -/
def sStr (l : ℕ) : String := if l = 0 then "0.0" else if l = 1 then "0.6" else "1.4"
noncomputable def sK (l : ℕ) : ℝ := if l = 0 then 0 else if l = 1 then 3/5 else 7/5

noncomputable def cL (l : ℕ) : List (CutAtomP 12) :=
  cutPairsX vsV 12 Side.L (cutAtomsOfX story3_rollover_ladder_rung_b_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 12) :=
  cutPairsX vsV 12 Side.R (cutAtomsOfX story3_rollover_ladder_rung_b_cutsV2X.R
    (story3_rollover_ladder_rung_b_IRv2.R.modes.getD q dm).name)

theorem gL_s (l : ℕ) (hl : l < 3) : hostAtomG vsV 12 Side.L (aS (sStr l)) = thrGe (Lv 1) (sK l) := by
  interval_cases l <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, hv00, hv06, pq14, vsV, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gR_s (q : ℕ) (hq : q < 3) : hostAtomG vsV 12 Side.R (aS (sStr q)) = thrGe (Rv 1) (sK q) := by
  interval_cases q <;>
  simp [aS, sStr, sK, hostAtomG, cutAtomG, Run.lowerE, hv00, hv06, pq14, vsV, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, thrGe, Rv]
theorem gL_linPsi : hostAtomG vsV 12 Side.L aLinPsi = linGe (Lv 2) (Lv 3) 1 0 (-1/2) := by
  simp [aLinPsi, hostAtomG, cutAtomG, Run.lowerE, hv1, hv0, hvm05, vsV, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linGe, linQ, Lv]
theorem gL_linTh : hostAtomG vsV 12 Side.L aLinTh = linGe (Lv 4) (Lv 5) 1 0 (-1/2) := by
  simp [aLinTh, hostAtomG, cutAtomG, Run.lowerE, hv1, hv0, hvm05, vsV, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, linGe, linQ, Lv]
theorem gL_psi : hostAtomG vsV 12 Side.L aPsi = thrGe (Lv 2) (-1/2) := by
  simp [aPsi, hostAtomG, cutAtomG, Run.lowerE, hvm05, vsV, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, thrGe, Lv]
theorem gL_th : hostAtomG vsV 12 Side.L aTh = thrGe (Lv 4) (-1/2) := by
  simp [aTh, hostAtomG, cutAtomG, Run.lowerE, hvm05, vsV, Run.resolveVar,
    List.findIdx?_cons, ITerm.toHost, thrGe, Lv]

/-- Every left mode keeps five atoms: its odometer guard conjunct, the two linear forms
`ω_ψ + ψ ≥ −0.5`, `ω_θ + θ ≥ −0.5`, and the two derived floors `ψ ≥ −0.5`, `θ ≥ −0.5`. -/
noncomputable def cLlist (l : ℕ) : List (CutAtomP 12) :=
  [(hostAtomF vsV 12 Side.L (aS (sStr l)), thrGe (Lv 1) (sK l)),
   (hostAtomF vsV 12 Side.L aLinPsi, linGe (Lv 2) (Lv 3) 1 0 (-1/2)),
   (hostAtomF vsV 12 Side.L aLinTh, linGe (Lv 4) (Lv 5) 1 0 (-1/2)),
   (hostAtomF vsV 12 Side.L aPsi, thrGe (Lv 2) (-1/2)),
   (hostAtomF vsV 12 Side.L aTh, thrGe (Lv 4) (-1/2))]

theorem cL_eq (l : ℕ) (hl : l < 3) : cL l = cLlist l := by
  unfold cLlist
  rw [← gL_s l hl, ← gL_linPsi, ← gL_linTh, ← gL_psi, ← gL_th]
  interval_cases l <;> rfl

theorem cR_eq (q : ℕ) (hq : q < 3) :
    cR q = [(hostAtomF vsV 12 Side.R (aS (sStr q)), thrGe (Rv 1) (sK q))] := by
  rw [← gR_s q hq]
  interval_cases q <;> rfl

theorem cR_nil (q : ℕ) (hq : 3 ≤ q) : cR q = [] := by
  have : story3_rollover_ladder_rung_b_IRv2.R.modes.getD q dm = dm :=
    List.getD_eq_default _ _ (by simp [story3_rollover_ladder_rung_b_IRv2]; omega)
  simp only [cR, this]
  rfl

theorem hiffL (l : ℕ) (hl : l < 3) : AtomsIff (cL l) := by
  rw [cL_eq l hl]
  intro a ha ν
  simp only [cLlist, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · rw [← gL_s l hl]; exact hostAtom_iff (Or.inr rfl) ν
  · rw [← gL_linPsi]; exact hostAtom_iff (Or.inr rfl) ν
  · rw [← gL_linTh]; exact hostAtom_iff (Or.inr rfl) ν
  · rw [← gL_psi]; exact hostAtom_iff (Or.inr rfl) ν
  · rw [← gL_th]; exact hostAtom_iff (Or.inr rfl) ν

theorem hiffR (q : ℕ) : AtomsIff (cR q) := by
  by_cases hq : q < 3
  · rw [cR_eq q hq]
    intro a ha ν
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    rw [← gR_s q hq]; exact hostAtom_iff (Or.inr rfl) ν
  · rw [cR_nil q (by omega)]
    intro a ha; simp at ha

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 3) :
    ∀ ν, Formula.sat (hostGuard vsV 12 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard story3_rollover_ladder_rung_b_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, story3_rollover_ladder_rung_b_cutsV2X, mL,
        story3_rollover_ladder_rung_b_IRv2] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, story3_rollover_ladder_rung_b_cutsV2X, mL,
        story3_rollover_ladder_rung_b_IRv2] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, hv00, hv06, pq14, hv1, hv0, hvm05, vsV, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases l <;>
      simp [mL, story3_rollover_ladder_rung_b_IRv2, Run.lowerF, Run.lowerE, hv00, hv06, pq14,
        pq89995, pqm025, vsV, Run.resolveVar, List.findIdx?_cons]


/-! ## O2: every kept atom stays along the joint flows (rational, no Z3) -/

/-- The odometer is non-decreasing on the joint domain (`v ≥ 0`, `|ψ|, |θ| ≤ 1`). -/
theorem sdotL_nonneg (l : ℕ) (hl : l < 3) (z : State (Var 12))
    (hz : Formula.sat (Formula.and domL domRV) z) : 0 ≤ Term.eval (fL l 1) z := by
  rw [fL1_eval l hl]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h2l, h2h, -, -, -, h4l, h4h, h0l, -, -, -, -, -⟩ :=
    (sat_domL z).mp hz.1
  have hB : (0:ℝ) ≤ (1 - 1/2 * (z (Lv 2) * z (Lv 2))) - 3/10 * (z (Lv 4) * z (Lv 4)) := by
    nlinarith
  exact mul_nonneg h0l hB

theorem sdotR_nonneg (q : ℕ) (hq : q < 3) (z : State (Var 12))
    (hz : Formula.sat (Formula.and domL domRV) z) : 0 ≤ Term.eval (fRV q 1) z := by
  rw [fRV1_eval q hq]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h2l, h2h, -, -, -, h4l, h4h, h0l, -, -, -, -, -⟩ :=
    (sat_domRV z).mp hz.2
  have hB : (0:ℝ) ≤ (1 - 1/2 * (z (Rv 2) * z (Rv 2))) - 3/10 * (z (Rv 4) * z (Rv 4)) := by
    nlinarith
  exact mul_nonneg h0l hB

/-- The critically damped attitude loop: `q = ω_ψ + ψ` has `q' = −q`, so `q ≥ −0.5` stays. -/
theorem stay_linPsi (l q : ℕ) (hl : l < 3) : ∀ ν,
    Term.eval (linGe (Lv 2) (Lv 3) 1 0 (-1/2)) ν ≤ 0 →
    BoxLe (Program.ode (jointSys (fL l) (fRV q) (Term.const 1)) (Formula.and domL domRV))
      (fun ω => Term.eval (linGe (Lv 2) (Lv 3) (1:ℝ) 0 (-1/2)) ω) ν := by
  intro ν hν
  refine boxle_L_of_super _ (fL l) (fRV q) (Term.const 1) _ (Formula.and domL domRV)
    (fun i h => by simp [linGe, linQ, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h) ?_ hν
  exact super_linear_ge_L (a := 1) (b := 2) (c := 0) (r := 1) (K := -1/2)
    (by norm_num) (by norm_num) (by norm_num) (fL l) _
    (fun z _ => fL2_eval l hl z) (fun z _ => (fL3_eval l hl z).trans (by ring))

theorem stay_linTh (l q : ℕ) (hl : l < 3) : ∀ ν,
    Term.eval (linGe (Lv 4) (Lv 5) 1 0 (-1/2)) ν ≤ 0 →
    BoxLe (Program.ode (jointSys (fL l) (fRV q) (Term.const 1)) (Formula.and domL domRV))
      (fun ω => Term.eval (linGe (Lv 4) (Lv 5) (1:ℝ) 0 (-1/2)) ω) ν := by
  intro ν hν
  refine boxle_L_of_super _ (fL l) (fRV q) (Term.const 1) _ (Formula.and domL domRV)
    (fun i h => by simp [linGe, linQ, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h) ?_ hν
  exact super_linear_ge_L (a := 1) (b := 2) (c := 0) (r := 1) (K := -1/2)
    (by norm_num) (by norm_num) (by norm_num) (fL l) _
    (fun z _ => fL4_eval l hl z) (fun z _ => (fL5_eval l hl z).trans (by ring))

/-- The derived floor `ψ ≥ −0.5`, inside its given linear form (`ψ' = ω_ψ ≥ −0.5 − ψ ≥ 0` on
the face `ψ ≤ −0.5`), stratified by `stay_given`. -/
theorem stay_psi (l q : ℕ) (hl : l < 3) : ∀ ν,
    Term.eval (linGe (Lv 2) (Lv 3) 1 0 (-1/2)) ν ≤ 0 →
    Term.eval (thrGe (Lv 2) (-1/2)) ν ≤ 0 →
    BoxLe (Program.ode (jointSys (fL l) (fRV q) (Term.const 1)) (Formula.and domL domRV))
      (fun ω => Term.eval (thrGe (Lv 2) (-1/2 : ℝ)) ω) ν := by
  have hFq : ∀ z, Formula.sat (hostAtomF vsV 12 Side.L aLinPsi) z ↔
      Term.eval (linGe (Lv 2) (Lv 3) 1 0 (-1/2)) z ≤ 0 := fun z => by
    rw [← gL_linPsi]; exact hostAtom_iff (Or.inr rfl) z
  refine stay_given hFq (stay_linPsi l q hl) ?_
  intro ν hν
  refine boxle_L_of_super _ (fL l) (fRV q) (Term.const 1) _ _
    (fun i h => by simp [thrGe, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h) ?_ hν
  exact super_derived_ge_L (r := 1) (c := 0) (K := -1/2) (K' := -1/2) (by norm_num)
    (by norm_num) (fL l) _ (fun z _ => fL2_eval l hl z) (fun z hz => (hFq z).mp hz.2)

theorem stay_th (l q : ℕ) (hl : l < 3) : ∀ ν,
    Term.eval (linGe (Lv 4) (Lv 5) 1 0 (-1/2)) ν ≤ 0 →
    Term.eval (thrGe (Lv 4) (-1/2)) ν ≤ 0 →
    BoxLe (Program.ode (jointSys (fL l) (fRV q) (Term.const 1)) (Formula.and domL domRV))
      (fun ω => Term.eval (thrGe (Lv 4) (-1/2 : ℝ)) ω) ν := by
  have hFq : ∀ z, Formula.sat (hostAtomF vsV 12 Side.L aLinTh) z ↔
      Term.eval (linGe (Lv 4) (Lv 5) 1 0 (-1/2)) z ≤ 0 := fun z => by
    rw [← gL_linTh]; exact hostAtom_iff (Or.inr rfl) z
  refine stay_given hFq (stay_linTh l q hl) ?_
  intro ν hν
  refine boxle_L_of_super _ (fL l) (fRV q) (Term.const 1) _ _
    (fun i h => by simp [thrGe, Term.fv, Lv, Rv, Prod.ext_iff] at h) (fun x h => h) ?_ hν
  exact super_derived_ge_L (r := 1) (c := 0) (K := -1/2) (K' := -1/2) (by norm_num)
    (by norm_num) (fL l) _ (fun z _ => fL4_eval l hl z) (fun z hz => (hFq z).mp hz.2)

theorem stayL (l q : ℕ) (hl : l < 3) :
    AtomsStayC (cL l) (jointSys (fL l) (fRV q) (Term.const 1)) (Formula.and domL domRV) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  have hall : ∀ b ∈ cLlist l, Term.eval b.2 ν ≤ 0 := by
    intro b hb
    rw [← cL_eq l hl] at hb
    exact (hiffL l hl b hb ν).mp (hν b hb)
  have hlp := hall (hostAtomF vsV 12 Side.L aLinPsi, linGe (Lv 2) (Lv 3) 1 0 (-1/2))
    (by simp [cLlist])
  have hlt := hall (hostAtomF vsV 12 Side.L aLinTh, linGe (Lv 4) (Lv 5) 1 0 (-1/2))
    (by simp [cLlist])
  rw [cL_eq l hl] at ha
  simp only [cLlist, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact boxle_thrGe_L 1 (sK l) _ _ _ _ (Formula.and domL domRV) (fun x h => h)
      (fun z hz _ => sdotL_nonneg l hl z hz) hinit
  · exact stay_linPsi l q hl ν hinit
  · exact stay_linTh l q hl ν hinit
  · exact stay_psi l q hl ν hlp hinit
  · exact stay_th l q hl ν hlt hinit

theorem stayR (l q : ℕ) :
    AtomsStayC (cR q) (jointSys (fL l) (fRV q) (Term.const 1)) (Formula.and domL domRV) := by
  intro a ha ν hν
  have hinit := (hiffR q a ha ν).mp (hν a ha)
  by_cases hq : q < 3
  · rw [cR_eq q hq] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_R 1 (sK q) _ _ 1 zero_le_one _ (Formula.and domL domRV) (fun x h => h)
      (fun z hz _ => sdotR_nonneg q hq z hz) hinit
  · rw [cR_nil q (by omega)] at ha
    simp at ha


/-! ## Side splits (the v2 left fields, evolve and guards) -/

theorem fL_pipe (l : ℕ) (i : Fin 12) : fL l i =
    (((some (mL l)).bind (Run.dynOf vsV 12 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domL_pipe : domL =
    (((some (mL 0)).bind (fun m => Run.lowerF vsV 12 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfL (l : ℕ) (hl : l < 3) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsV) (some (mL l))
    (by interval_cases l <;>
      simp [mL, story3_rollover_ladder_rung_b_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))

theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsV) (some (mL 0))
    (by simp [mL, story3_rollover_ladder_rung_b_IRv2, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domL_pipe ▸ hx))

theorem hguardL (l : ℕ) (hl : l < 3) : (hostGuard vsV 12 Side.L (mL l)).fv ⊆ range Lv := by
  refine hostGuard_fv_L vsV (mL l) ?_
  interval_cases l <;>
    simp [mL, story3_rollover_ladder_rung_b_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]

/-! ## The declared rows (`invComponents`, as the tool lowers them) -/

/-- `invComponents` output mentions no Aux coordinate. -/
theorem invComponents_no_aux {vars : List String} :
    ∀ {f : PForm} {L : List (ITerm 12)}, Oracle.invComponents vars 12 f = some L →
      ∀ t ∈ L, ∀ v ∈ (ITerm.toHost t).fv, v.1 ≠ Side.Aux := by
  intro f
  induction f with
  | tt =>
      intro L h t ht
      simp only [Oracle.invComponents, Option.some.injEq] at h
      subst h; simp at ht
  | cmp op a b =>
      intro L h t ht v hv
      simp only [Oracle.invComponents] at h
      rcases hea : Run.lowerE vars 12 Side.L a with _ | ea <;>
        rcases heb : Run.lowerE vars 12 Side.L b with _ | eb <;>
        simp only [hea, heb] at h <;>
        split_ifs at h <;> simp at h <;> subst h <;> simp at ht <;> subst ht <;>
        simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv <;>
        rcases hv with hv | hv <;>
        first
        | exact Run.lowerE_no_aux (by simp) hea v hv
        | exact Run.lowerE_no_aux (by simp) heb v hv
  | and x y ihx ihy =>
      intro L h t ht v hv
      simp only [Oracle.invComponents] at h
      rcases hx : Oracle.invComponents vars 12 x with _ | lx <;>
        rcases hy : Oracle.invComponents vars 12 y with _ | ly <;>
        simp only [hx, hy] at h <;> simp at h
      subst h
      rcases List.mem_append.mp ht with ht | ht
      · exact ihx hx t ht v hv
      · exact ihy hy t ht v hv
  | or x y _ _ => intro L h; simp [Oracle.invComponents] at h
  | not x _ => intro L h; simp [Oracle.invComponents] at h

theorem hostComps_fv (f : PForm) :
    ∀ t ∈ hostComps vsV 12 f, t.fv ⊆ range Lv ∪ range Rv := by
  intro t ht x hx
  unfold hostComps at ht
  rcases h : Oracle.invComponents vsV 12 f with _ | L
  · rw [h] at ht; simp at ht
  · rw [h] at ht
    simp only [Option.map_some, Option.getD_some, List.mem_map] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact notAux_mem_LR (invComponents_no_aux h u hu x hx)

/-- The cover's strata orders: `[0, 1, 2]` for the STEEP window, `[0, 1]` for MODER / FLAT. -/
def ordOf : ℕ → List ℕ
  | 0 => [0, 1, 2]
  | _ => [0, 1]

noncomputable def comps0 (l : ℕ) : List (Term (Var 12)) :=
  hostComps vsV 12 (story3_rollover_ladder_rung_b_IRv2.invariants.getD l ("", PForm.tt)).2
noncomputable def comps (l : ℕ) : List (Term (Var 12)) :=
  (ordOf l).map (fun i => (comps0 l).getD i (Term.const 0))
noncomputable def g (l : ℕ) : Term (Var 12) := (comps0 l).getD 0 (Term.const 0)
noncomputable def gs (l : ℕ) : List (Term (Var 12)) :=
  (ordOf l).tail.map (fun i => (comps0 l).getD i (Term.const 0))

theorem comps_eq (l : ℕ) : comps l = g l :: gs l := by
  cases l <;> rfl

theorem getD_fv (L : List (Term (Var 12))) (hL : ∀ t ∈ L, t.fv ⊆ range Lv ∪ range Rv) (i : ℕ) :
    (L.getD i (Term.const 0)).fv ⊆ range Lv ∪ range Rv := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : L[i]? with _ | t
  · simp [Term.fv]
  · exact hL t (List.mem_of_getElem? h)

theorem comps_fv_all (l : ℕ) : ∀ c ∈ g l :: gs l, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact getD_fv _ (hostComps_fv _) 0
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
    exact getD_fv _ (hostComps_fv _) i

/-- The window's row is the left mode's own declared row (by name, as the tool reads it). -/
theorem invRow_faithful (l : ℕ) (hl : l < 3) :
    Handoff.invRowOf story3_rollover_ladder_rung_b_IRv2 (mL l)
      = some (story3_rollover_ladder_rung_b_IRv2.invariants.getD l ("", PForm.tt)).2 := by
  interval_cases l <;> decide

/-! ### Row nesting: STEEP's row is `v_L ≤ v_R` conjoined with MODER's; FLAT's is MODER's -/

def rowV : PForm := .cmp "<=" (.var "L_v") (.var "R_v")
def rowP : PForm := match (story3_rollover_ladder_rung_b_IRv2.invariants.getD 1 ("", PForm.tt)).2 with
  | .and a _ => a
  | _ => .tt
def rowT : PForm := match (story3_rollover_ladder_rung_b_IRv2.invariants.getD 1 ("", PForm.tt)).2 with
  | .and _ b => b
  | _ => .tt

theorem row0_eq : (story3_rollover_ladder_rung_b_IRv2.invariants.getD 0 ("", PForm.tt)).2
    = .and (.and rowV rowP) rowT := rfl
theorem row1_eq : (story3_rollover_ladder_rung_b_IRv2.invariants.getD 1 ("", PForm.tt)).2
    = .and rowP rowT := rfl
theorem row2_eq : (story3_rollover_ladder_rung_b_IRv2.invariants.getD 2 ("", PForm.tt)).2
    = (story3_rollover_ladder_rung_b_IRv2.invariants.getD 1 ("", PForm.tt)).2 := rfl

theorem rowV_comp : ∃ t, Oracle.invComponents vsV 12 rowV = some [t] := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [rowV, Oracle.invComponents, Run.lowerE, vsV, Run.resolveVar, Parse.dr, hdL, hdR,
    List.findIdx?_cons]

theorem invComp_and (vars : List String) (x y : PForm) :
    Oracle.invComponents vars 12 (.and x y) =
      (Oracle.invComponents vars 12 x).bind (fun lx =>
        (Oracle.invComponents vars 12 y).bind (fun ly => some (lx ++ ly))) := rfl

theorem comps0_shift (i : ℕ) : (comps0 0).getD (i + 1) (Term.const 0) = (comps0 1).getD i (Term.const 0) := by
  obtain ⟨t, ht⟩ := rowV_comp
  unfold comps0 hostComps
  rw [row0_eq, row1_eq, invComp_and, invComp_and, invComp_and, ht]
  rcases Oracle.invComponents vsV 12 rowP with _ | lp <;>
    rcases Oracle.invComponents vsV 12 rowT with _ | lt <;> simp

theorem comps0_two : comps0 2 = comps0 1 := by
  unfold comps0; rw [row2_eq]

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- One pack: left window `l` at its OWN declared row (`invRow = l`), right mode `q`, at the
cover's λ = 1 and strata order (`[0, 1, 2]` for STEEP, `[0, 1]` for MODER / FLAT). -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX story3_rollover_ladder_rung_b_IRv2 story3_rollover_ladder_rung_b_cutsV2X 12 l
    (ordOf l) 1 l q

theorem verd_core (l q : ℕ) (hl : l < 3) (hq : q < 3) (h : Verd l q) :
    VerdXCore (comps l) (fL l) (fRV q) 1 (domCutX (Formula.and domL domRV) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq, ← fR_eq q]
  exact h'

/-! ## Right existence (Z3-free): the legacy right-only face lemmas, any left field/domain

`HExistSegB` reads the left domain only as a hypothesis on the left run, and the stratified
viability consumer never uses it, so the legacy right viability facts (strict inflow
`hbndS_V`, non-strict faces `hbndN_V`, the `e`-affine faces, Lipschitz/field bounds) give the
existence for the v2 (wider) left domain verbatim. -/
set_option maxHeartbeats 1600000 in
theorem es (fL' : Fin 12 → Term (Var 12)) (D A : Formula (Var 12)) (m : ℕ) (hm : m < 3)
    (dt : ℝ) :
    ∀ σ, Formula.sat (Formula.and A (Formula.and D domRV)) σ →
      HExistSegB fL' (fRV m) (Term.const 1) D domRV dt (Function.update σ tg 0) := by
  intro σ hσ
  by_cases hdt : 0 ≤ dt
  swap
  · intro s _ hs0 hsdt
    exact absurd (le_trans hs0 hsdt) hdt
  have hR : Formula.sat domRV σ := hσ.2.2
  rw [sat_domRV] at hR
  obtain ⟨hd6l, hd6h, hd9l, hd9h, hd3l, hd3h, hd5l, hd5h, hd8l, hd8h, hd2l, hd2h, hd7l, hd7h, hd1l, hd4l, hd4h, hd0l, hd0h, hd11l, hd11h, hd10l, hd10h⟩ := hR
  have hupd : ∀ j : Fin 12, σ (Side.R, j) = Function.update σ tg 0 (Side.R, j) := by
    intro j
    rw [Function.update_of_ne (by simp [tg, Prod.ext_iff])]
  have hfS : ∀ gT' ∈ gsSV, Term.eval gT' (Function.update σ tg 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsSV, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceVLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceVHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsiHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceRLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceRHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceEAuxLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceEAuxHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  have hfN : ∀ gT' ∈ gsNV, Term.eval gT' (Function.update σ tg 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsNV, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceSLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPsLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPsHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOThLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOThHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPhLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPhHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceYLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceYHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  refine HExistSegB_of_viability_stratA fL' (fRV m) (Term.const (1))
    D domRV gsSV [] gsNV 0 le_rfl
    [((Rv 6 : Var 12), 2, (76:ℝ)/25, (38:ℝ)/25)]
    [((Rv 6 : Var 12), 2, -(76:ℝ)/25, -(38:ℝ)/25)]
    (jointSys_wellFormed _ _ _)
    (by
      intro gT' hgT x hxf hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub fL' _ hb
      obtain ⟨j, hj⟩ := faces_fv_RV gT' (by
        rcases List.mem_append.mp hgT with h | h
        · exact List.mem_append_left _ h
        · exact absurd h (List.not_mem_nil)) x hxf
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT' hgT x hxf hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub fL' _ hb
      obtain ⟨j, hj⟩ := faces_fv_RV gT' (List.mem_append_right _ hgT) x hxf
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro p hp hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      obtain ⟨i, hi⟩ := leftBlock_bound_sub fL' _ hb
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro p hp hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      obtain ⟨i, hi⟩ := leftBlock_bound_sub fL' _ hb
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      norm_num)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      norm_num)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      norm_num)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      norm_num)
    (by
      intro gT' hgT x hsub hface
      exact hbndS_V m hm gT' hgT x
        (fun g hg => hsub g (List.mem_append_left _ hg)) hface)
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro i hi x hxs _
      exact hbndN_V m hm i hi x hxs)
    (by
      intro p hp x hxs _
      have hne : ∀ (a b : Fin 12), a ≠ b → (Rv a : Var 12) ≠ Rv b := by
        intro a b hab
        simp [Rv, Prod.ext_iff]
        exact fun h => hab (by exact_mod_cast h)
      have hr2 : x (Rv 7) ≤ (76:ℝ)/25 := by
        have := hxs faceRHi (List.mem_append_left _ (by simp [gsSV]))
        simp only [faceRHi, Term.eval, AOp.interp] at this; linarith
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      rw [odeField_RV m hm]
      simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)),
        if_neg (hne 6 2 (by decide)), if_neg (hne 6 4 (by decide)),
        eq_self_iff_true, if_true, if_pos rfl]
      show x (Rv 7) - 2 * x (Rv 6) ≤ (76:ℝ)/25 - 2 * x (Rv 6)
      linarith)
    (by
      intro p hp x hxs _
      have hne : ∀ (a b : Fin 12), a ≠ b → (Rv a : Var 12) ≠ Rv b := by
        intro a b hab
        simp [Rv, Prod.ext_iff]
        exact fun h => hab (by exact_mod_cast h)
      have hr1 : -(76:ℝ)/25 ≤ x (Rv 7) := by
        have := hxs faceRLo (List.mem_append_left _ (by simp [gsSV]))
        simp only [faceRLo, Term.eval, AOp.interp] at this; linarith
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      rw [odeField_RV m hm]
      simp only [if_neg (hne 6 0 (by decide)), if_neg (hne 6 1 (by decide)),
        if_neg (hne 6 2 (by decide)), if_neg (hne 6 4 (by decide)),
        eq_self_iff_true, if_true, if_pos rfl]
      show -(76:ℝ)/25 - 2 * x (Rv 6) ≤ x (Rv 7) - 2 * x (Rv 6)
      linarith)
    (by
      intro x hS hN hAU hAL
      have hS' : ∀ gT' ∈ gsSV, Term.eval gT' x ≤ 0 :=
        fun gT' hgT => hS gT' (List.mem_append_left _ hgT)
      have hb0l : 0 ≤ x (Rv 0) := by
        have := hS' faceVLo (by simp [gsSV])
        simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
      have hb0h : x (Rv 0) ≤ (4:ℝ)/5 := by
        have := hS' faceVHi (by simp [gsSV])
        simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
      have hb2l : -(1:ℝ)/2 ≤ x (Rv 2) := by
        have := hS' facePsiLo (by simp [gsSV])
        simp only [facePsiLo, Term.eval, AOp.interp] at this; linarith
      have hb2h : x (Rv 2) ≤ (3:ℝ)/20 := by
        have := hS' facePsiHi (by simp [gsSV])
        simp only [facePsiHi, Term.eval, AOp.interp] at this; linarith
      have hb4l : -(1:ℝ)/2 ≤ x (Rv 4) := by
        have := hS' faceThLo (by simp [gsSV])
        simp only [faceThLo, Term.eval, AOp.interp] at this; linarith
      have hb4h : x (Rv 4) ≤ (3:ℝ)/20 := by
        have := hS' faceThHi (by simp [gsSV])
        simp only [faceThHi, Term.eval, AOp.interp] at this; linarith
      have hb7l : -(76:ℝ)/25 ≤ x (Rv 7) := by
        have := hS' faceRLo (by simp [gsSV])
        simp only [faceRLo, Term.eval, AOp.interp] at this; linarith
      have hb7h : x (Rv 7) ≤ (76:ℝ)/25 := by
        have := hS' faceRHi (by simp [gsSV])
        simp only [faceRHi, Term.eval, AOp.interp] at this; linarith
      have hb8l : -(1:ℝ)/2 ≤ x (Rv 8) := by
        have := hS' facePhLo (by simp [gsSV])
        simp only [facePhLo, Term.eval, AOp.interp] at this; linarith
      have hb8h : x (Rv 8) ≤ (3:ℝ)/20 := by
        have := hS' facePhHi (by simp [gsSV])
        simp only [facePhHi, Term.eval, AOp.interp] at this; linarith
      have hb1l : 0 ≤ x (Rv 1) := by
        have := hN faceSLo (by simp [gsNV])
        simp only [faceSLo, Term.eval, AOp.interp] at this; linarith
      have hb3l : -(1:ℝ)/2 ≤ x (Rv 3) := by
        have := hN faceOPsLo (by simp [gsNV])
        simp only [faceOPsLo, Term.eval, AOp.interp] at this; linarith
      have hb3h : x (Rv 3) ≤ (3:ℝ)/5 := by
        have := hN faceOPsHi (by simp [gsNV])
        simp only [faceOPsHi, Term.eval, AOp.interp] at this; linarith
      have hb5l : -(1:ℝ)/2 ≤ x (Rv 5) := by
        have := hN faceOThLo (by simp [gsNV])
        simp only [faceOThLo, Term.eval, AOp.interp] at this; linarith
      have hb5h : x (Rv 5) ≤ (3:ℝ)/5 := by
        have := hN faceOThHi (by simp [gsNV])
        simp only [faceOThHi, Term.eval, AOp.interp] at this; linarith
      have hb9l : -(1:ℝ)/2 ≤ x (Rv 9) := by
        have := hN faceOPhLo (by simp [gsNV])
        simp only [faceOPhLo, Term.eval, AOp.interp] at this; linarith
      have hb9h : x (Rv 9) ≤ (3:ℝ)/5 := by
        have := hN faceOPhHi (by simp [gsNV])
        simp only [faceOPhHi, Term.eval, AOp.interp] at this; linarith
      have hb10l : -(1:ℝ) ≤ x (Rv 10) := by
        have := hN faceZLo (by simp [gsNV])
        simp only [faceZLo, Term.eval, AOp.interp] at this; linarith
      have hb10h : x (Rv 10) ≤ (11:ℝ)/10 := by
        have := hN faceZHi (by simp [gsNV])
        simp only [faceZHi, Term.eval, AOp.interp] at this; linarith
      have hb11l : -(1:ℝ) ≤ x (Rv 11) := by
        have := hN faceYLo (by simp [gsNV])
        simp only [faceYLo, Term.eval, AOp.interp] at this; linarith
      have hb11h : x (Rv 11) ≤ (11:ℝ)/10 := by
        have := hN faceYHi (by simp [gsNV])
        simp only [faceYHi, Term.eval, AOp.interp] at this; linarith
      have hb6h : x (Rv 6) ≤ (38:ℝ)/25 := by
        have := hAU ((Rv 6 : Var 12), 2, (76:ℝ)/25, (38:ℝ)/25) (by simp)
        simpa using this
      have hb6l : -(38:ℝ)/25 ≤ x (Rv 6) := by
        have := hAL ((Rv 6 : Var 12), 2, -(76:ℝ)/25, -(38:ℝ)/25) (by simp)
        simpa using this
      exact (sat_domRV x).mpr ⟨hb6l, hb6h, hb9l, hb9h, hb3l, hb3h, hb5l, hb5h, hb8l, hb8h, hb2l, hb2h, hb7l, hb7h, hb1l, hb4l, hb4h, hb0l, hb0h, hb11l, hb11h, hb10l, hb10h⟩)
    60 60 1 one_pos
    (fun ν0 h0 => hLip_V m hm ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    (fun ν0 h0 => hfbnd_V m hm ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    dt hdt
    (Function.update σ tg 0)
    hfS
    hfN
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      show Function.update σ tg 0 (Rv 6) ≤ (38:ℝ)/25
      rw [← hupd 6]
      linarith)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      show -(38:ℝ)/25 ≤ Function.update σ tg 0 (Rv 6)
      rw [← hupd 6]
      linarith)
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))



/-! ## The coupling, the window response -/

theorem atoms_fv (l q : ℕ) (hl : l < 3) :
    ∀ c ∈ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [cL_eq l hl] at ha
    simp only [cLlist, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    · intro x hx
      simp only [thrGe, linGe, linQ, Term.fv, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, or_false, false_or] at hx
      rcases hx with rfl | rfl <;> simp
  · by_cases hq : q < 3
    · rw [cR_eq q hq] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      intro x hx
      simp only [thrGe, Term.fv, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, false_or] at hx
      subst hx; simp
    · rw [cR_nil q (by omega)] at ha; simp at ha

theorem anchor_fv (l q : ℕ) (hl : l < 3) :
    ∀ c ∈ g l :: gs l ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv_all l _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv_all l _ (List.mem_cons_of_mem _ hc)
  · exact atoms_fv l q hl c hc

theorem couple (l q : ℕ) (hl : l < 3) (hq : q < 3) (dt : ℝ) (hv : Verd l q) :
    ∀ σ, Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domRV)) σ →
      faModalB (Equiv.refl (Var 12))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fRV q) (Term.const 1)) domRV)
        (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q))) (Formula.and domL domRV))
        tg dt (Function.update σ tg 0) :=
  couple_cutX (g l) (gs l) (comps l) (cL l) (cR q) (fL l) (fRV q) 1 one_pos domL domRV 1 dt
    (hfL l hl) (hfRV q hq) hdomL hdomRV (anchor_fv l q hl)
    (fun c hc => by rw [comps_eq] at hc; exact hc)
    (fun c hc => by rw [comps_eq]; exact hc)
    (hiffL l hl) (hiffR q) (stayL l q hl) (stayR l q)
    (verd_core l q hl hq hv) (es (fL l) domL _ q hq dt)

theorem sat_faModal_monoPost {P Q : Program (Var 12)} {A B : Formula (Var 12)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 12)}
    (h : Formula.sat (faModal (Equiv.refl (Var 12)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 12)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

/-- The right mode's region: its kept cut atoms (the odometer floor of its terrain zone). -/
noncomputable def region (q : ℕ) : Formula (Var 12) := cutF (cR q)

theorem sat_region (q : ℕ) (ν : State (Var 12)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := sat_cutF _ _

theorem region_fv (q : ℕ) : (region q).fv ⊆ range Rv := by
  intro x hx
  unfold region cutF at hx
  have key : ∀ (L : List (CutAtomP 12)) (acc : Formula (Var 12)),
      acc.fv ⊆ range Rv → (∀ a ∈ L, a.1.fv ⊆ range Rv) →
      (L.foldl (fun d a => Formula.and d a.1) acc).fv ⊆ range Rv := by
    intro L
    induction L with
    | nil => intro acc hacc _; simpa using hacc
    | cons a L ih =>
        intro acc hacc hL
        simp only [List.foldl_cons]
        refine ih _ ?_ (fun b hb => hL b (List.mem_cons_of_mem _ hb))
        intro y hy
        rcases hy with hy | hy
        · exact hacc hy
        · exact hL a List.mem_cons_self hy
  refine key (cR q) Formula.tt (by simp [Formula.fv]) ?_ hx
  intro a ha y hy
  by_cases hq : q < 3
  · rw [cR_eq q hq] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact side_eq_R_mem (by
      simp only at hy
      unfold hostAtomF at hy
      exact hostForm_side (resolvesTo_R vsV) _
        (by interval_cases q <;>
          simp [aS, sStr, Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · rw [cR_nil q (by omega)] at ha; simp at ha

theorem respond (l qs : ℕ) (hl : l < 3) (hqs : qs < 3) (dt : ℝ) (hv : Verd l qs)
    {σ : State (Var 12)}
    (hσ : Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR qs)))
        (Formula.and domL domRV)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 12))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq ([] ++ [Program.ode (rightBlock (fRV qs) (Term.const 1)) domRV]))
      (Formula.and (Formula.and (FM (g l) (gs l)) env) (region qs))) σ := by
  have htgF : tg ∉ (FM (g l) (gs l ++ atomTerms (cL l) (cR qs))).fv :=
    notMem_FM_fv (fun g' hg' hx => by
      rcases anchor_fv l qs hl g' (by simpa using hg') hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact absurd hi (by simp [Lv, Prod.ext_iff])
      · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have htgenv : tg ∉ (Formula.and domL domRV).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 1 (hdomL h)
    · exact aux_notin_range_Rv 1 (hdomRV h)
  have hfa := Hmulti_windowRF_prefixed (fL l) domL (FM (g l) (gs l ++ atomTerms (cL l) (cR qs)))
    (Formula.and domL domRV) 1 dt 1 htgF htgenv [] (by simp)
    (fun σ' hσ' => hσ'.2.1) (by simp)
    (hfL l hl) hdomL
    [Program.ode (rightBlock (fRV qs) (Term.const 1)) domRV] rfl (by norm_num)
    (by
      intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      rw [Program.rename_refl]
      exact hdisH_progR (⟨fRV qs, Term.const 1, domRV⟩ : RepoHop 12)
        (hfRV qs hqs) (by simp [Term.fv]) hdomRV (hfL l hl) hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple l qs hl hqs dt hv σ' hσ')
    hσ
  refine sat_faModal_monoPost ?_ (by simpa using hfa)
  intro ν hν
  obtain ⟨hFν, hatν⟩ := (sat_FM_append (g l) (gs l) _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff (hiffL l hl) (hiffR qs) ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region qs ν).mpr hRν⟩

/-! ## The per-left-mode step provider: STAY in the start mode -/

theorem gate (l : ℕ) (dt : ℝ) (R : Program (Var 12)) (ψ : Formula (Var 12))
    {σ : State (Var 12)}
    (hbody : Formula.sat (hostGuard vsV 12 Side.L (mL l)) σ →
      Formula.sat (faModal (Equiv.refl (Var 12))
        (windowSeg (leftBlock (fL l)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 12))
      (gwindowSeg (hostGuard vsV 12 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

theorem stayCase (l q : ℕ) (hl : l < 3) (hq : q < 3) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 12)} (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ)
    (hreg : Formula.sat (region q) σ) :
    ∃ segs : List (ℕ × RMode (Var 12) × REdge (Var 12)),
      (∀ s ∈ segs, GrV.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrV.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      Formula.sat (faModal (Equiv.refl (Var 12))
        (gwindowSeg (hostGuard vsV 12 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FM (g l) (gs l)) env) (region (qfOf segs q)))) σ := by
  refine ⟨[(q, modeV q, edgeV q q)], ?_, by simp, by simp, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    refine ⟨GrV_modeAt q hq, edgeV_mem q q ?_⟩
    interval_cases q <;> simp [GrV]
  · refine gate l dt _ _ (fun hguard => ?_)
    have hanchor : Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domRV)) σ := by
      refine ⟨(sat_FM_append (g l) (gs l) _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
      exact (atomTerms_iff (hiffL l hl) (hiffR q) σ).mpr
        ⟨hO1L l hl σ hguard, (sat_region q σ).mp hreg⟩
    have := respond l q hl hq dt hv hanchor
    simpa [modeV, qfOf, edgeV] using this

/-- Left mode `l`'s window, every right start mode: the response stays in place. -/
theorem HmultiL (l : ℕ) (hl : l < 3) (dt : ℝ) (h0 : Verd l 0) (h1 : Verd l 1) (h2 : Verd l 2) :
    ∀ (q : ℕ), q < GrV.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and (FM (g l) (gs l)) env) (region q)) σ →
      ∃ segs : List (ℕ × RMode (Var 12) × REdge (Var 12)),
        (∀ s ∈ segs, GrV.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrV.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 12))
          (gwindowSeg (hostGuard vsV 12 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FM (g l) (gs l)) env) (region (qfOf segs q)))) σ := by
  intro q hq σ _ hσ
  have hq3 : q < 3 := by simpa [GrV] using hq
  match q, hq3, hσ with
  | 0, _, hσ => exact stayCase l 0 hl (by norm_num) dt h0 hσ.1 hσ.2
  | 1, _, hσ => exact stayCase l 1 hl (by norm_num) dt h1 hσ.1 hσ.2
  | 2, _, hσ => exact stayCase l 2 hl (by norm_num) dt h2 hσ.1 hσ.2

/-! ## The declared rows, per left mode -/

noncomputable def FRow (l : ℕ) : Formula (Var 12) := FM (g l) (gs l)
noncomputable def ϕRow (l : ℕ) : RFormula (Var 12) := canonInvM (g l) (gs l)

theorem encode_ϕRow (l : ℕ) : encode (Equiv.refl (Var 12)) (ϕRow l) = FRow l :=
  encode_canonInvM _ _

theorem aux_notin_FRow (a : Fin 12) (l : ℕ) : ((Side.Aux, a) : Var 12) ∉ (FRow l).fv :=
  notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv_all l g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-- STEEP's row (`v_L ≤ v_R ∧ D_ψ ∧ D_θ`) implies MODER's (`D_ψ ∧ D_θ`). -/
theorem FRow_steep_moder {ω : State (Var 12)} (h : Formula.sat (FRow 0) ω) :
    Formula.sat (FRow 1) ω := by
  refine FM_mono ?_ h
  intro c hc
  simp only [g, gs, ordOf, List.tail_cons, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc ⊢
  rcases hc with rfl | rfl
  · exact Or.inr (Or.inl (comps0_shift 0).symm)
  · exact Or.inr (Or.inr (comps0_shift 1).symm)

theorem FRow_two : FRow 2 = FRow 1 := by
  unfold FRow g gs; rw [comps0_two]; rfl

/-! ## The left automaton, from the file -/

def nextL : List (List ℕ) :=
  (List.range 3).map (fun l =>
    (mL l).next.filterMap (Handoff.leftModeIndex story3_rollover_ladder_rung_b_IRv2))

/-- `STEEP → [MODER, STEEP]`, `MODER → [FLAT, MODER]`, `FLAT → [FLAT]`. -/
theorem nextL_eq : nextL = [[1, 0], [2, 1], [2]] := by decide

theorem nextL_transitions :
    ((List.range 3).flatMap (fun m' => (nextL.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions story3_rollover_ladder_rung_b_IRv2 := by decide

noncomputable def guardsL : List (Formula (Var 12)) :=
  (List.range 3).map (fun l => hostGuard vsV 12 Side.L (mL l))

/-- The left automaton: mode `l`'s window re-tests `l`'s guard (the v2 entry condition) and
flows `l`'s field on the v2 left evolve (clock-capped at `dt`, one piece). -/
noncomputable def A (dt : ℝ) : LeftAut 12 :=
  { windows := (List.range 3).map (fun l =>
      gwindowSeg (hostGuard vsV 12 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1),
    guards := guardsL,
    next := nextL }

theorem A_numModes (dt : ℝ) : (A dt).numModes = 3 := rfl

theorem A_window (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (A dt).window t = gwindowSeg (hostGuard vsV 12 Side.L (mL t)) (leftBlock (fL t)) domL tg dt 1 := by
  interval_cases t <;> rfl

theorem A_guard (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (A dt).guard t = hostGuard vsV 12 Side.L (mL t) := by
  interval_cases t <;> rfl

theorem A_succ (dt : ℝ) (m' : ℕ) : (A dt).succ m' = nextL.getD m' [] := rfl

theorem hnext (dt : ℝ) : ∀ m' < (A dt).numModes, ∀ t ∈ (A dt).succ m', t < (A dt).numModes := by
  intro m' hm' t ht
  rw [A_numModes] at hm' ⊢
  rw [A_succ, nextL_eq] at ht
  interval_cases m' <;> simp at ht <;> omega

theorem hgrd (dt : ℝ) : ∀ t < (A dt).numModes, ((A dt).guard t).fv ⊆ range Lv := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_guard dt t ht]
  exact hguardL t ht

theorem hwin (dt : ℝ) : ∀ t < (A dt).numModes,
    Program.vars ((A dt).window t) ⊆ {((Side.Aux, 1) : Var 12)} ∪ range Lv := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  exact vars_gwindowSegL_sub _ (fL t) domL 1 dt 1 (hguardL t ht) (hfL t ht) hdomL

/-! ## Freshness of `u_L` and `mv` -/

theorem hulenv : uL ∉ env.fv := fun h => by
  rcases h with h | h
  · exact aux_notin_range_Lv 2 (hdomL h)
  · exact aux_notin_range_Rv 2 (hdomRV h)

theorem hmvenv : mv ∉ env.fv := fun h => by
  rcases h with h | h
  · exact aux_notin_range_Lv 0 (hdomL h)
  · exact aux_notin_range_Rv 0 (hdomRV h)

theorem hmvreg : ∀ q, mv ∉ (region q).fv := fun q h => aux_notin_range_Rv 0 (region_fv q h)

theorem hulBk : uL ∉ (mvRegion mv region GrV.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv region GrV.modes.length (fun q _ => region_fv q) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hulG (dt : ℝ) : ∀ t, uL ∉ ((A dt).guard t).fv := by
  intro t h
  by_cases ht : t < 3
  · exact aux_notin_range_Lv 2 (hgrd dt t ht h)
  · have : (A dt).guard t = Formula.tt := by
      unfold LeftAut.guard A guardsL
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem framesGw (t : ℕ) (dt : ℝ) (a : Fin 12) (ha : a ≠ 1) :
    FramesMv (gwindowSeg (hostGuard vsV 12 Side.L (mL t)) (leftBlock (fL t)) domL tg dt 1)
      ((Side.Aux, a) : Var 12) := by
  refine framesMv_gwindow _ (fL t) domL tg dt 1 _ (by simpa [Prod.ext_iff] using ha) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL t) _ h
  exact aux_ne_Lv a i hi

theorem hframesUl (dt : ℝ) : ∀ t, FramesMv ((A dt).window t) uL := by
  intro t
  by_cases ht : t < 3
  · rw [A_window dt t ht]
    exact framesGw t dt 2 (by decide)
  · have : (A dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window A
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulR : uL ∉ (rightAutomatonBody GrV mv).bv :=
  notMem_bv_rightAutomatonBody GrV mv uL (by decide) (aux_notin_range_Rv 2) httV hRvV

/-! ## The handoffs, in-kernel (nested rows) -/

theorem handoff (dt : ℝ) : ∀ m' < (A dt).numModes, ∀ t ∈ (A dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat env ω → Formula.sat ((A dt).guard t) ω →
      Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _ _
  rw [A_numModes] at hm'
  rw [A_succ, nextL_eq] at ht
  interval_cases m' <;> simp at ht <;> rcases ht with rfl | rfl
  · exact FRow_steep_moder hF
  · exact hF
  · rw [FRow_two]; exact hF
  · exact hF
  · exact hF

/-! ## The per-mode steps -/

theorem hstepM (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2)
    (h10 : Verd 1 0) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h20 : Verd 2 0) (h21 : Verd 2 1) (h22 : Verd 2 2) :
    ∀ t < (A dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) env)
      (mvRegion mv region GrV.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 12)) ((A dt).window t)
      (Program.star (rightAutomatonBody GrV mv))
      (Formula.and (Formula.and (FRow t) env)
        (mvRegion mv region GrV.modes.length))) σ := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  obtain ⟨hv0, hv1, hv2⟩ : Verd t 0 ∧ Verd t 1 ∧ Verd t 2 := by
    match t, ht with
    | 0, _ => exact ⟨h00, h01, h02⟩
    | 1, _ => exact ⟨h10, h11, h12⟩
    | 2, _ => exact ⟨h20, h21, h22⟩
  exact hstepMode_multiR GrV mv (FRow t) env region _ (aux_notin_FRow 0 t) hmvenv hmvreg
    hfreshV httV hltV (framesGw t dt 0 (by decide)) (HmultiL t ht dt hv0 hv1 hv2)

/-! ## Theorem 3, mode-keyed -/

/-- **`story3_rollover_ladder_rung_b` (suite_v2), Theorem 3 at the DECLARED mode-dependent
invariant.** Left: the file's automaton (`STEEP → [MODER, STEEP]`, `MODER → [FLAT, MODER]`,
`FLAT → [FLAT]`), each step re-testing the v2 guard (terrain zone plus settled attitude) and
flowing on the v2 left evolve; right: the file's three-mode automaton. The loop invariant keys
the declared rows by `u_L` (STEEP: `v_L ≤ v_R ∧ D_ψ ≤ 0.25 ∧ D_θ ≤ 0.25`; MODER = FLAT:
`D_ψ ≤ 0.25 ∧ D_θ ≤ 0.25`), plus both evolve envelopes and the right mode's region (its kept
odometer floor). Response: STAY in the start mode on the certified cut-narrowed joint segment
at λ = 1. Residuals: the nine packs `Verd l q`. -/
theorem story3_rollover_ladder_rung_b_modeKeyed (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2)
    (h10 : Verd 1 0) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h20 : Verd 2 0) (h21 : Verd 2 1) (h22 : Verd 2 2) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody GrV mv)
      (psiK uL ϕRow (A dt).numModes domL domRV
        (mvRegionR mv region GrV.modes.length))) := by
  refine theorem3_modeKeyed (A dt) uL GrV mv FRow ϕRow domL domRV
    (mvRegion mv region GrV.modes.length) (mvRegionR mv region GrV.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (A dt) GrV 0 1 2 (by decide) (by decide) (hwin dt) (hgrd dt)
      (hnext dt) httV hRvV
  · exact hstep_modeKeyed (A dt) uL (rightAutomatonBody GrV mv) FRow env
      (mvRegion mv region GrV.modes.length) (aux_notin_FRow 2) hulenv hulBk (hulG dt)
      (hframesUl dt) hulR (hnext dt)
      (hstepM dt h00 h01 h02 h10 h11 h12 h20 h21 h22) (handoff dt)
  · exact hddF_modeKeyed (A dt) GrV 0 1 2 (by decide) (by decide) ϕRow domL domRV
      (mvRegionR mv region GrV.modes.length) (hwin dt) (hgrd dt) (hnext dt) httV hRvV
      (fun m _ => canonInvM_varsL (g m) (gs m) (comps_fv_all m))
      (fun m _ => canonInvM_varsR (g m) (gs m)) hdomL hdomRV rfl
      (fun v hv => mvRegion_fv_sub mv region GrV.modes.length (fun q _ => region_fv q) hv)

end V2Story3RolloverRungB
end RelCertifier
