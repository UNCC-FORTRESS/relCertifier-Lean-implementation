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
import RelCertifier.Checker.Cover

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
  dynPreOrder  : List Nat := []
  dynPostOrder : List Nat := []
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

/-! ## The structural cover graph, from emitted data (shared: tool AND kernel replay) -/

/-- A flag row is a NODE iff it carries any certificate. -/
def ModeFlagsE.isNode (f : ModeFlagsE) : Bool :=
  f.jointOK || f.repoPre || f.repoPost || f.dynPre || f.dynPost

/-- **The structural cover graph** — the exact construction the tool gates CERTIFIED on
(`coverMode`'s `cgReal`), as a pure function of the emitted flags, the declared
successor lists, and the pruned edges. Nodes = flag rows with any certificate; an edge
to a NON-node target gets the out-of-range sentinel index (`decideCovered`'s
∀-over-successors then fails there — an uncertified declared successor is never
silently stripped). Kernel replays run `decideCovered` on THIS SAME function applied to
the SAME emitted data. -/
def buildCoverGraph {V : Type*} [Fintype V] [DecidableEq V]
    (flags : List ModeFlagsE) (succ : String → List String)
    (pruned : String → String → Bool) : SearchGraph V :=
  let nodes := flags.filter (·.isNode)
  let kSentinel := nodes.length
  let idxOf := fun (nm : String) => ((nodes.findIdx? (·.name == nm)).getD kSentinel)
  { modes := nodes.map (fun f =>
      { sys := [], dom := .tt, weight := 1,
        jointOK := f.jointOK,
        region := .tt, repoPreOK := f.repoPre,
        regionPost := .tt, repoPostOK := f.repoPost,
        dynSys := [], dynDomPre := .tt, dynDomPost := .tt,
        repoDynPreOK := f.dynPre, repoDynPostOK := f.dynPost })
    edges := nodes.flatMap (fun f => (succ f.name).map (fun tgt =>
      { src := idxOf f.name, tgt := idxOf tgt, guard := .tt, pruned := pruned f.name tgt })) }

/-- The checker fuel bound the tool uses (`bBudget·(nodes+1)+1`). -/
def coverFuel (flags : List ModeFlagsE) (bBudget : Nat) : Nat :=
  bBudget * ((flags.filter (·.isNode)).length + 1) + 1

/-- Node index of a mode name (sentinel = node count if absent). -/
def nodeIdx (flags : List ModeFlagsE) (nm : String) : Nat :=
  let nodes := flags.filter (·.isNode)
  (nodes.findIdx? (·.name == nm)).getD nodes.length

end RelCertifier
