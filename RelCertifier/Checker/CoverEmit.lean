/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The emitted cover record

What the tool's successful cover search found, per benchmark: the data the Lean instances
rebuild and re-verify in the kernel. Per left mode: the stretch λ and the budget, each right
mode's certificate flags, the admissible initial right modes, and per (left, right) pairing
the ROUND ORDER of the invariant components (the rounds of Section 4.1 in which `checkSeg`'s
fixpoint certified them, each assuming only earlier rounds, the narrowing
`stratified_barrier_sound` consumes) and the STRETCH the pairing was certified at (equal to
the left mode's λ unless the per-pairing fallback of Section 6.1 chose the cover;
`VerdictsV2/LamPinV2.lean` pins it to the verdict pack of the pairing). Per benchmark: the
edges pruned by non-connection certificates (Definition 6).

Pure data, no IO: lives in `Checker/` so instances and the drift test can consume it;
the printer (`--emit-cover`) is the trusted door in `Trusted/`.
-/

import Mathlib.Data.Rat.Defs
import RelCertifier.Checker.Cover

namespace RelCertifier

/-- Per right mode: which certificates the tool established (at the emitted λ): the joint
flow certificate, and the right-only certificates in the pre-joint and post-joint source
settings. -/
structure ModeFlagsE where
  name    : String
  jointOK : Bool
  dynPre  : Bool
  dynPost : Bool
  deriving Repr, DecidableEq

/-- Per (left mode, right mode): the round order of the invariant components (Section 4.1):
`order[k]` is the component index certified in round `k+1`; the flow-query domain of
component `order[k]` is narrowed by exactly `order.take k`. `dynPreOrder`/`dynPostOrder` are
the same for the right-only flow certificate in each source setting. -/
structure PairStrataE where
  mR    : String
  order : List Nat
  dynPreOrder  : List Nat := []
  dynPostOrder : List Nat := []
  /-- The stretch at which this pairing's joint segment was certified, as a reduced fraction
  `lamN / lamD`. With one stretch per left mode it equals the left mode's `lamQ`; the
  per-pairing fallback (`RELCERT_NO_PAIR_STRETCH` unset, Section 6.1) lets it differ per right
  mode. The kernel pin `VerdictsV2/LamPinV2.lean` ties it to the verdict pack row of the same
  pairing. `lamN = 0` is stretch 0 (the witness stands still while the left runs), emitted only
  when the run's stretch-0 feature is on (`PProblem.stutter`, the default). -/
  lamN  : Nat := 1
  lamD  : Nat := 1
  deriving Repr, DecidableEq

/-- Per left mode: the successful cover's data. `lamQ` is the left mode's stretch: the common
stretch when one closes the cover, otherwise (per-pairing fallback) the largest stretch
`λmax` among the certified pairings, so that the common segment span is `εR / lamQ` and
`bBudget = ⌈εL · lamQ / εR⌉` in both cases (Section 6.1, Appendix B.2). A left mode whose
pairings all have stretch `0` has `lamQ = εR / εL` (span `εL`, budget `1`), so `lamQ` is
always positive. -/
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
  f.jointOK || f.dynPre || f.dynPost

/-- **The structural cover graph** (the search graph of Section 5): the construction the tool
gates CERTIFIED on (`coverMode`'s `cgReal`), as a pure function of the emitted flags, the
declared successor lists, and the pruned edges. Nodes = flag rows with any certificate; an
edge to a NON-node target gets the out-of-range sentinel index (`decideCovered`'s
∀-over-successors then fails there, so an uncertified declared successor is never silently
dropped). Kernel replays run `decideCovered` on THIS SAME function applied to the SAME
emitted data. -/
def buildCoverGraph {V : Type*} [Fintype V] [DecidableEq V]
    (flags : List ModeFlagsE) (succ : String → List String)
    (pruned : String → String → Bool) : SearchGraph V :=
  let nodes := flags.filter (·.isNode)
  let kSentinel := nodes.length
  let idxOf := fun (nm : String) => ((nodes.findIdx? (·.name == nm)).getD kSentinel)
  { modes := nodes.map (fun f =>
      { sys := [], dom := .tt, weight := 1,
        jointOK := f.jointOK,
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
