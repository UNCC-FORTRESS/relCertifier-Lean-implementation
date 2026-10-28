/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_girard08_robot`: Assumption 1 of the right model (exit to the next location)

Stated directly over the generic bridge's automaton `grOf IR 6 pruned` (no standalone
instance): the lowered right guards, `ε_r = 1`. The right model is the planner's kinematic
point mass `y₂ = (wx, wy)` (coordinates 4 and 5; the right fields of `ex, ey, zx, zy` lower to
0) of the approximate-simulation example: six locations `M1 … M6`, each a constant heading of
norm at most `0.2` (`0.1414213` for `0.1 √2`), guards the enlarged half-planes and strips, one
evolve domain for all of them, the constant atom `0.0 ≤ 1.0` (every state).
* Existence (i): the explicit linear run `x + v_q t` (`trajRs_sol`), trivially in the domain.
* Completeness (ii): every run moves `wx, wy` exactly to `x + v_q t` (`rate_le`, `rate_ge`),
  so over `t ≤ 1` each coordinate moves by at most `0.2`; the end state is in `M_q`'s own
  guard or crosses into the guard of the next location `M_{q+1}` (cyclic), a declared
  successor of every mode. Z3-free.
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.lit_girard08_robot

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2LitGirard08Robot

open DL DLCalTiming DLRel Parse Set Emitted

abbrev IR := Parse.lit_girard08_robot_IRv2

/-! ## Parse pins -/

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp02 : Run.parseRat "0.2" = some ((1 : ℚ) / 5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpc : Run.parseRat "0.1414213" = some ((1414213 : ℚ) / 10000000) := by
  have h : parseQ "0.1414213" = some (⟨1414213, 10000000⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp04 : Run.parseRat "0.4" = some ((2 : ℚ) / 5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm04 : Run.parseRat "-0.4" = some (-(2 : ℚ) / 5) := by
  have h : parseQ "-0.4" = some (⟨-4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp34 : Run.parseRat "3.4" = some ((17 : ℚ) / 5) := by
  have h : parseQ "3.4" = some (⟨34, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm34 : Run.parseRat "-3.4" = some (-(17 : ℚ) / 5) := by
  have h : parseQ "-3.4" = some (⟨-34, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp26 : Run.parseRat "2.6" = some ((13 : ℚ) / 5) := by
  have h : parseQ "2.6" = some (⟨26, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm26 : Run.parseRat "-2.6" = some (-(13 : ℚ) / 5) := by
  have h : parseQ "-2.6" = some (⟨-26, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem epsR_eq : epsR IR = 1 := by
  simp [epsR, IR, Parse.lit_girard08_robot_IRv2, hp10]

theorem nR_eq : nR IR = 6 := rfl

/-! ## The right fields, domain and guards, evaluated -/

/-- `0.1414213`, the file's `0.1 √2`. -/
noncomputable def cr : ℝ := 1414213 / 10000000

/-- The heading of location `q`: `(vx q, vy q)`. -/
noncomputable def vx (q : ℕ) : ℝ :=
  if q = 0 then 1 / 5 else if q = 1 then cr else if q = 2 then -cr else if q = 3 then -(1 / 5)
  else if q = 4 then -cr else cr
noncomputable def vy (q : ℕ) : ℝ :=
  if q = 0 then 0 else if q = 1 then -cr else if q = 2 then -cr else if q = 3 then 0
  else if q = 4 then cr else cr

/-- The velocity of coordinate `i` in location `q` (only `wx`, `wy` move). -/
noncomputable def vel (q : ℕ) (i : Fin 6) : ℝ :=
  if i.val = 4 then vx q else if i.val = 5 then vy q else 0

/-- The lowered right fields: `wx' = vx q`, `wy' = vy q`, every other coordinate frozen. -/
theorem fR_eval (q : ℕ) (hq : q < 6) (s : State (Var 6)) (i : Fin 6) :
    Term.eval (fR IR 6 q i) s = vel q i := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mRof, vars, IR, Parse.lit_girard08_robot_IRv2, Run.dynOf, Run.lowerE, hp00,
      hp02, hpc, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, vel, vx, vy, cr]

/-- The shared evolve domain `0.0 ≤ 1.0`: the constant atom, true at every state. -/
theorem sat_domR_iff (s : State (Var 6)) : Formula.sat (domR IR 6) s ↔ (0 : ℝ) ≤ 1 := by
  simp [domR, hostEvolve, mRof, vars, IR, Parse.lit_girard08_robot_IRv2, Run.lowerF, Run.lowerE,
    hp00, hp10, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]

theorem sat_domR (s : State (Var 6)) : Formula.sat (domR IR 6) s :=
  (sat_domR_iff s).mpr zero_le_one

theorem sat_g0 (s : State (Var 6)) : Formula.sat (guardR IR 6 0) s ↔
    (-(2 / 5 : ℝ) ≤ s (Rv 4) ∧ s (Rv 4) ≤ 17 / 5) ∧ -(2 / 5 : ℝ) ≤ s (Rv 5) := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_girard08_robot_IRv2, Run.lowerF, Run.lowerE,
    hp04, hpm04, hp34, hpm34, hp26, hpm26, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  norm_num

theorem sat_g1 (s : State (Var 6)) : Formula.sat (guardR IR 6 1) s ↔
    (13 / 5 : ℝ) ≤ s (Rv 4) ∧ -(2 / 5 : ℝ) ≤ s (Rv 5) := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_girard08_robot_IRv2, Run.lowerF, Run.lowerE,
    hp04, hpm04, hp34, hpm34, hp26, hpm26, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  norm_num

theorem sat_g2 (s : State (Var 6)) : Formula.sat (guardR IR 6 2) s ↔
    -(2 / 5 : ℝ) ≤ s (Rv 4) ∧ s (Rv 5) ≤ 2 / 5 := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_girard08_robot_IRv2, Run.lowerF, Run.lowerE,
    hp04, hpm04, hp34, hpm34, hp26, hpm26, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  norm_num

theorem sat_g3 (s : State (Var 6)) : Formula.sat (guardR IR 6 3) s ↔
    (-(17 / 5 : ℝ) ≤ s (Rv 4) ∧ s (Rv 4) ≤ 2 / 5) ∧ s (Rv 5) ≤ 2 / 5 := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_girard08_robot_IRv2, Run.lowerF, Run.lowerE,
    hp04, hpm04, hp34, hpm34, hp26, hpm26, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  norm_num

theorem sat_g4 (s : State (Var 6)) : Formula.sat (guardR IR 6 4) s ↔
    s (Rv 4) ≤ -(13 / 5 : ℝ) ∧ s (Rv 5) ≤ 2 / 5 := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_girard08_robot_IRv2, Run.lowerF, Run.lowerE,
    hp04, hpm04, hp34, hpm34, hp26, hpm26, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  norm_num

theorem sat_g5 (s : State (Var 6)) : Formula.sat (guardR IR 6 5) s ↔
    s (Rv 4) ≤ (2 / 5 : ℝ) ∧ -(2 / 5 : ℝ) ≤ s (Rv 5) := by
  simp [guardR, hostGuard, mRof, vars, IR, Parse.lit_girard08_robot_IRv2, Run.lowerF, Run.lowerE,
    hp04, hpm04, hp34, hpm34, hp26, hpm26, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  norm_num

theorem tgt_M1 : tgtIdx IR "M1" = 0 := by decide
theorem tgt_M2 : tgtIdx IR "M2" = 1 := by decide
theorem tgt_M3 : tgtIdx IR "M3" = 2 := by decide
theorem tgt_M4 : tgtIdx IR "M4" = 3 := by decide
theorem tgt_M5 : tgtIdx IR "M5" = 4 := by decide
theorem tgt_M6 : tgtIdx IR "M6" = 5 := by decide

/-- Landing in the guard of a declared successor `nm` of `q` discharges clause (ii). -/
theorem land (pruned : String → String → Bool) {q : ℕ} (hq : q < 6) {nm : String}
    (hnm : nm ∈ (mRof IR q).next) {y : State (Var 6)}
    (hy : Formula.sat (guardR IR 6 (tgtIdx IR nm)) y) :
    ∃ e ∈ (grOf IR 6 pruned).edgesFrom q, Formula.sat (guardR IR 6 e.tgt) y :=
  ⟨edgeOf IR 6 pruned q nm, edge_mem_grOf (by rw [nR_eq]; exact hq) hnm, hy⟩

/-- Along every run of location `q`, a coordinate moves exactly at its constant velocity. -/
theorem end_coord {q : ℕ} (hq : q < 6) {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (rightBlock (fR IR 6 q) (Term.const 1)) (domR IR 6) x t Φ) (i : Fin 6) :
    Φ t (Rv i) = x (Rv i) + vel q i * t := by
  have hmem := rightBlock_mem' (fR IR 6 q) (Term.const 1) i
  have hf : ∀ s, Term.eval (Term.binop .mul (Term.const 1) (fR IR 6 q i)) s = vel q i :=
    fun s => by rw [eval_unit_mul, fR_eval q hq]
  exact le_antisymm (H.rate_le hmem (vel q i) (fun s _ => (hf s).le))
    (H.rate_ge hmem (vel q i) (fun s _ => (hf s).ge))

/-- **Assumption 1 for `lit_girard08_robot`**, every mode, over the bridge's automaton. -/
theorem lit_girard08_robot_wellFormedR_direct (pruned : String → String → Bool) :
    WellFormedR (grOf IR 6 pruned) (guardR IR 6) (epsR IR) := by
  rw [epsR_eq]
  intro q hq m hm x hg _ _
  obtain ⟨hq6, rfl⟩ := grOf_modeAt_inv hm
  rw [nR_eq] at hq6
  refine ⟨?_, ?_⟩
  · -- existence: the explicit linear run of one period
    refine ⟨_, trajRs_sol x (fun i t => x (Rv i) + vel q i * t) 1 (by norm_num) ?_ ?_
      (fun t _ _ => sat_domR _)⟩
    · intro i; simp
    · intro i t _ _
      rw [fR_eval q hq6]
      simpa using ((hasDerivAt_id t).const_mul (vel q i)).const_add (x (Rv i))
  · -- completeness: `wx, wy` move by at most `0.2`: own guard, or the next location's
    intro t Φ ht H
    have ht0 : 0 ≤ t := H.hr
    have ha := end_coord hq6 H 4
    have hb := end_coord hq6 H 5
    have hc0 : (0 : ℝ) < cr := by norm_num [cr]
    have hc1 : cr ≤ 1 / 5 := by norm_num [cr]
    have hct : cr * t ≤ 1 / 5 := by nlinarith
    have hct0 : 0 ≤ cr * t := by positivity
    interval_cases q
    · -- M1: `wx` rises by at most 0.2; M1 below 3.4, else M2
      simp only [vel, vx, vy] at ha hb; norm_num at ha hb
      obtain ⟨⟨g1, g2⟩, g3⟩ := (sat_g0 x).mp hg
      by_cases h : Φ t (Rv 4) ≤ 17 / 5
      · exact land pruned (by norm_num) (nm := "M1") (by decide)
          (by rw [tgt_M1, sat_g0]; refine ⟨⟨?_, h⟩, ?_⟩ <;> linarith)
      · exact land pruned (by norm_num) (nm := "M2") (by decide)
          (by rw [tgt_M2, sat_g1]; constructor <;> linarith)
    · -- M2: `wx` rises, `wy` falls by at most 0.2; M2, else M3
      simp only [vel, vx, vy] at ha hb; norm_num at ha hb
      obtain ⟨g1, g2⟩ := (sat_g1 x).mp hg
      by_cases h : -(2 / 5 : ℝ) ≤ Φ t (Rv 5)
      · exact land pruned (by norm_num) (nm := "M2") (by decide)
          (by rw [tgt_M2, sat_g1]; constructor <;> nlinarith)
      · exact land pruned (by norm_num) (nm := "M3") (by decide)
          (by rw [tgt_M3, sat_g2]; constructor <;> nlinarith)
    · -- M3: both fall by at most 0.2; M3, else M4
      simp only [vel, vx, vy] at ha hb; norm_num at ha hb
      obtain ⟨g1, g2⟩ := (sat_g2 x).mp hg
      by_cases h : -(2 / 5 : ℝ) ≤ Φ t (Rv 4)
      · exact land pruned (by norm_num) (nm := "M3") (by decide)
          (by rw [tgt_M3, sat_g2]; constructor <;> nlinarith)
      · exact land pruned (by norm_num) (nm := "M4") (by decide)
          (by rw [tgt_M4, sat_g3]; refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith)
    · -- M4: `wx` falls by at most 0.2; M4 above -3.4, else M5
      simp only [vel, vx, vy] at ha hb; norm_num at ha hb
      obtain ⟨⟨g1, g2⟩, g3⟩ := (sat_g3 x).mp hg
      by_cases h : -(17 / 5 : ℝ) ≤ Φ t (Rv 4)
      · exact land pruned (by norm_num) (nm := "M4") (by decide)
          (by rw [tgt_M4, sat_g3]; refine ⟨⟨h, ?_⟩, ?_⟩ <;> linarith)
      · exact land pruned (by norm_num) (nm := "M5") (by decide)
          (by rw [tgt_M5, sat_g4]; constructor <;> linarith)
    · -- M5: `wx` falls, `wy` rises by at most 0.2; M5, else M6
      simp only [vel, vx, vy] at ha hb; norm_num at ha hb
      obtain ⟨g1, g2⟩ := (sat_g4 x).mp hg
      by_cases h : Φ t (Rv 5) ≤ 2 / 5
      · exact land pruned (by norm_num) (nm := "M5") (by decide)
          (by rw [tgt_M5, sat_g4]; constructor <;> nlinarith)
      · exact land pruned (by norm_num) (nm := "M6") (by decide)
          (by rw [tgt_M6, sat_g5]; constructor <;> nlinarith)
    · -- M6: both rise by at most 0.2; M6, else M1
      simp only [vel, vx, vy] at ha hb; norm_num at ha hb
      obtain ⟨g1, g2⟩ := (sat_g5 x).mp hg
      by_cases h : Φ t (Rv 4) ≤ 2 / 5
      · exact land pruned (by norm_num) (nm := "M6") (by decide)
          (by rw [tgt_M6, sat_g5]; constructor <;> nlinarith)
      · exact land pruned (by norm_num) (nm := "M1") (by decide)
          (by rw [tgt_M1, sat_g0]; refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith)

end V2LitGirard08Robot
end RelCertifier
