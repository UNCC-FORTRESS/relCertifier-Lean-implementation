/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Refutations, part 1: the witness, evaluated in the kernel, and the query groups

A refutation witness (`Refute.RefWitE`) is a rational joint state. Its facts (the antecedent
of Theorem 3's claim at the stored modes, the entered mode's guard, a broken component) are
decided in the kernel by evaluating the lowered IR (`ITerm.evalQ`, `IForm.evalQ`) at the
witness: `IForm.evalQ_iff` ties the evaluation to host satisfaction at the real cast.

`refGroups` builds every query a refutation rests on, as singleton groups (the bridge's
`GroupsOK` pattern); `RefVerdicts` is the green run of the runner.
-/
import RelCertifier.Proofs.Encoding.Emitted.Run
import RelCertifier.Trusted.RefuteQueries

set_option autoImplicit false

namespace RelCertifier

open DL

variable {n : ℕ}

/-! ## Rational evaluation of the lowered IR -/

/-- `AOp` on rationals. -/
def aopQ : AOp → ℚ → ℚ → ℚ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- `CompOp` on rationals, decided. -/
def cmpQ : CompOp → ℚ → ℚ → Bool
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)

/-- An IR term at a rational state. -/
def ITerm.evalQ (s : Var n → ℚ) : ITerm n → ℚ
  | .var v => s v
  | .rat q => q
  | .bin op a b => aopQ op (a.evalQ s) (b.evalQ s)

/-- An IR formula at a rational state. -/
def IForm.evalQ (s : Var n → ℚ) : IForm n → Bool
  | .tt => true
  | .cmp op a b => cmpQ op (a.evalQ s) (b.evalQ s)
  | .neg f => !(f.evalQ s)
  | .and a b => a.evalQ s && b.evalQ s

/-- The real state of a rational one. -/
def castQ (s : Var n → ℚ) : State (Var n) := fun v => (s v : ℝ)

theorem ITerm.evalQ_toHost (s : Var n → ℚ) (t : ITerm n) :
    Term.eval t.toHost (castQ s) = ((t.evalQ s : ℚ) : ℝ) := by
  induction t with
  | var v => rfl
  | rat q => rfl
  | bin op a b iha ihb =>
      cases op <;> simp [ITerm.toHost, Term.eval, AOp.interp, ITerm.evalQ, aopQ, iha, ihb]

theorem IForm.evalQ_iff (s : Var n → ℚ) (f : IForm n) :
    Formula.sat f.toHost (castQ s) ↔ f.evalQ s = true := by
  induction f with
  | tt => simp [IForm.toHost, Formula.sat, IForm.evalQ]
  | cmp op a b =>
      cases op <;> simp [IForm.toHost, Formula.sat, CompOp.interp, IForm.evalQ, cmpQ,
        ITerm.evalQ_toHost]
  | neg f ih => simp [IForm.toHost, Formula.sat, IForm.evalQ, ih]
  | and a b iha ihb => simp [IForm.toHost, Formula.sat, IForm.evalQ, iha, ihb]

/-- An optional lowered formula at a rational state, the failed lowering read as `⊤` (the
host's `getD Formula.tt`). -/
def optQ (s : Var n → ℚ) (o : Option (IForm n)) : Bool := (o.map (·.evalQ s)).getD true

theorem optQ_iff (s : Var n → ℚ) (o : Option (IForm n)) :
    Formula.sat ((o.map IForm.toHost).getD Formula.tt) (castQ s) ↔ optQ s o = true := by
  rcases o with _ | f
  · simp [optQ, Formula.sat]
  · simp [optQ, IForm.evalQ_iff]

namespace Emitted

open Parse Run Oracle Refute Set

section Data

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX)

/-- The witness state: the left and right values by coordinate, the right mode variable `a` at
the stored right mode, the left mode variable `c` at the stored left mode. -/
def witState (a c : Fin n) (w : RefWitE) : Var n → ℚ := fun v =>
  match v.1 with
  | Side.L => w.wL.getD v.2.val 0
  | Side.R => w.wR.getD v.2.val 0
  | Side.Aux => if v.2 = a then (w.q0 : ℚ) else if v.2 = c then (w.u : ℚ) else 0

/-- The witness state after the left switch `c := m`. -/
def witSwitch (c : Fin n) (w : RefWitE) (s : Var n → ℚ) : Var n → ℚ :=
  Function.update s (Side.Aux, c) (w.m : ℚ)

/-- ... and the clock reset `b := 0`. -/
def witPost (b c : Fin n) (w : RefWitE) (s : Var n → ℚ) : Var n → ℚ :=
  Function.update (witSwitch n c w s) (Side.Aux, b) 0

/-- Every component of a row at a rational state is `≤ 0` (a failed lowering reads as no
component, the host's `getD []`). -/
def compsQ (row : PForm) (s : Var n → ℚ) : Bool :=
  ((Oracle.invComponents (vars p) n row).map (·.all (fun g => decide (g.evalQ s ≤ 0)))).getD true

/-- Component `k` of a row is `> 0` at a rational state. -/
def compPosQ (row : PForm) (k : ℕ) (s : Var n → ℚ) : Bool :=
  (((Oracle.invComponents (vars p) n row).bind (·[k]?)).map (fun g => decide (0 < g.evalQ s))).getD
    false

/-- **The antecedent facts of a witness**, decided in the kernel: the indices in range and the
switch declared; at the witness, the stored left mode's row, both evolve envelopes, the stored
right mode's guard and kept atoms; after the switch, the entered mode's guard (tested twice by
the left automaton) and the left envelope (the zero-duration flow's domain). -/
def preOK (a b c : Fin n) (w : RefWitE) : Bool :=
  let s := witState n a c w
  let s' := witPost n b c w s
  decide (w.u < nL p) && ((nextL p).getD w.u []).contains w.m && decide (w.q0 < nR p) &&
  compsQ p n (rowOf p w.u) s &&
  optQ s (lowerF (vars p) n Side.L (mLof p 0).evolve) &&
  optQ s (lowerF (vars p) n Side.R (mRof p 0).evolve) &&
  optQ s (lowerF (vars p) n Side.R (mRof p w.q0).guard) &&
  (cutAtomsOfX cX.R (mRof p w.q0).name).all (fun x => optQ s (lowerF (vars p) n Side.R x.atom)) &&
  optQ s (lowerF (vars p) n Side.L (mLof p w.m).guard) &&
  optQ (witSwitch n c w s) (lowerF (vars p) n Side.L (mLof p w.m).guard) &&
  optQ s' (lowerF (vars p) n Side.L (mLof p 0).evolve)

/-- The no-partner group of kind C: one query per right mode. -/
def noPartnerGroups (w : RefWitE) : Option (List (List (IForm n))) :=
  (List.range (nR p)).mapM (fun q =>
    (noPartnerQueryOf (vars p) n (rowOf p w.m) (mRof p 0) (mRof p q)
      (cutAtomsOfX cX.R (mRof p q).name) w.wL).map ([·]))

/-- The rigidity group of a component: one query per right mode. -/
def rigidGroups (w : RefWitE) : Option (List (List (IForm n))) := do
  let cs ← Oracle.invComponents (vars p) n (rowOf p w.m)
  let g ← cs[w.k]?
  (List.range (nR p)).mapM (fun q => (rigidQueryOf (vars p) n g (mRof p 0) (mRof p q)).map ([·]))

/-- Every query of a refutation, by kind. -/
def refGroups (w : RefWitE) : Option (List (List (IForm n))) :=
  if w.kind == "C" then noPartnerGroups p n cX w else rigidGroups p n w

/-- The runner's green run: every group of the refutation has an `unsat` member. -/
def RefVerdicts (w : RefWitE) : Prop :=
  ∃ gs, refGroups p n cX w = some gs ∧ GroupsOK gs

end Data

end Emitted
end RelCertifier
