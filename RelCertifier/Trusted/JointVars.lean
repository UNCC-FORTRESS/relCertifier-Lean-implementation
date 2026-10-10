/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The joint variable list (leaf)

The lowering (`Trusted/Run.lean`) indexes the joint state `Var n = Side × Fin n` by ONE
variable list: coordinate `i` names `L_<vars[i]>` and `R_<vars[i]>`. With the left list
alone, a right-only variable (declared in `[Rsys] state_vars` but not in `[Lsys]`) would
have no coordinate and every query of the benchmark would fail to lower.

`jointVars` is the left list followed by the right-only names, in declaration order. A
right-only variable gets a left coordinate `L_w` that no left formula mentions and whose
left derivative is `0` (`dynOf`: a variable with no `ode` row is held fixed), which is
exactly the "absent on the left" reading. A benchmark whose right list is contained in
the left one gets `p.L.stateVars` back unchanged; that is every suite_v2 benchmark (41
declare the same variables on both sides, four declare a right sublist), so nothing the
kernel instances quote moves.

Leaf over `Parse` only: `Run.lean` stays untouched (it is upstream of every proof).
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- The joint variable list: the left variables, then the right-only ones. Equal to
`p.L.stateVars` whenever the right declares no variable the left lacks. -/
def PProblem.jointVars (p : PProblem) : List String :=
  p.L.stateVars ++ p.R.stateVars.filter (fun v => !p.L.stateVars.contains v)

/-- The right-only variables (empty on the emitted suite). -/
def PProblem.rightOnlyVars (p : PProblem) : List String :=
  p.R.stateVars.filter (fun v => !p.L.stateVars.contains v)

end RelCertifier.Parse
