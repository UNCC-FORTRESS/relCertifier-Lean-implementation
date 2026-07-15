/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The emitted cover record (R5 — docs/ROADMAP.md)

What the tool's successful cover search found, per benchmark — the data the Lean
instances rebuild and re-verify in kernel: the chosen λ and budget, each right mode's
certificate flags, the pruned edges, the admissible starts, and the per-(left, right)
STRATA ORDER of the invariant components (the order `checkSeg`'s fixpoint proved them
in — the exact narrowing discipline `stratified_barrier_sound` consumes).

Pure data, no IO: lives in `Checker/` so instances and the drift test can consume it;
the printer (`--emit-cover`) is the trusted door in `Trusted/`.
-/

import Mathlib.Data.Rat.Defs

namespace RelCertifier

/-- Per right mode: which certificates the tool established (at the emitted λ). -/
structure ModeFlagsE where
  name    : String
  jointOK : Bool
  repoPre : Bool
  repoPost : Bool
  dynPre  : Bool
  dynPost : Bool
  deriving Repr, DecidableEq

/-- Per (left mode, right mode): the strata order of the invariant components —
`order[k]` is the component index proven in round `k+1`; the flow-query domain of
component `order[k]` is narrowed by exactly `order.take k`. -/
structure PairStrataE where
  mR    : String
  order : List Nat
  deriving Repr, DecidableEq

/-- Per left mode: the successful cover's data. -/
structure LeftCoverE where
  mL         : String
  lamQ       : ℚ
  bBudget    : Nat
  flags      : List ModeFlagsE
  admissible : List String
  strata     : List PairStrataE
  deriving Repr, DecidableEq

/-- Per benchmark: the emitted cover (pruned edges are benchmark-global). -/
structure CoverEmitE where
  name   : String
  pruned : List (String × String)
  covers : List LeftCoverE
  deriving Repr, DecidableEq

end RelCertifier
