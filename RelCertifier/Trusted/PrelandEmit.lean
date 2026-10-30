/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The pre-landing right-only nodes of a cover (emitted, opt-in `prelanding = true`)

A benchmark with `[problem] prelanding = true` may certify a right-only (reposition) node
`(mL, mR, pre)` by the PRE-LANDING right-only flow certificate: the stratified route A/B/C pack
of the frozen-left flow of `mR` over the reposition domain narrowed by the half-open region
`before(x, θ)` of the node's progress certificate's last stage (`x < θ` upward, `x > θ`
downward), instead of the whole-domain route-A pack (`checkDynRepo`). The witness right run
stops at its FIRST entry into the closed target `crossed(x, θ)`, ending its control cycle
early (`docs/PRELANDING.md`).

These nodes are emitted HERE, in their own record, never as the cover's `dynPre`/`dynPost`
flags: a consumer of the emitted cover that reads those flags as the whole-domain certificate
never sees a pre-landing node. The kernel merges the two (`Emitted.withPL`) for the cover
graph only, and backs every merged node by the pre-landing verdict and the progress
certificate (`Emitted/Prelanding.lean`); it admits a nonempty record only when the IR has
`prelanding := true`.
-/
import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Preland

/-- A pre-landing node: window `mL`, right mode `mR`, setting `pre` (pre-joint), and the
strata order of its pack (`order[k]` is the component proven in round `k+1`). -/
structure PrelandNodeE where
  mL    : String
  mR    : String
  pre   : Bool
  order : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- Per benchmark. -/
structure PrelandEmitE where
  name  : String
  nodes : List PrelandNodeE
  deriving Repr, DecidableEq, Inhabited

/-- The empty record (every benchmark without the key). -/
def PrelandEmitE.none : PrelandEmitE := ⟨"", []⟩

/-- The node `(mL, mR, pre)` of a record, if any. -/
def PrelandEmitE.find (pl : PrelandEmitE) (mL mR : String) (pre : Bool) : Option PrelandNodeE :=
  pl.nodes.find? (fun x => x.mL == mL && x.mR == mR && x.pre == pre)

def emitPrelandE (defname : String) (c : PrelandEmitE) : String :=
  let one := fun (x : PrelandNodeE) =>
    s!"⟨\"{x.mL}\", \"{x.mR}\", {x.pre}, {repr x.order}⟩"
  s!"def {defname} : RelCertifier.Preland.PrelandEmitE :=\n  ⟨\"{c.name}\", [\n    " ++
    String.intercalate ",\n    " (c.nodes.map one) ++ "]⟩"

end RelCertifier.Preland
