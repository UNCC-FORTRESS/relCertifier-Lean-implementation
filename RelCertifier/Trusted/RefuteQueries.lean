/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The queries of a refutation (branch `refutation`)

A refutation of Theorem 3's claim for an invariant (`Proofs/Encoding/Emitted/Refute.lean`)
rests, besides kernel-decided facts about a rational witness, on Z3 `unsat` answers to two
query shapes, built here from the records alone (pure builders; the runner
`VerdictsV2/RunRefute.lean` issues them, the refutation theorems read their `unsat`):

* `noPartnerQueryOf`: no right state pairs with the witness's left values in the entered
  left mode `m` at right mode `q`: `⋀ᵢ Lᵢ = wᵢ ∧ ⋀ⱼ gⱼ ≤ 0 ∧ evolveR ∧ guard_q ∧ cuts_q`, with
  `gⱼ` the components of `m`'s row (`invComponents`), `evolveR` the right evolve domain, the
  guard and the kept cut atoms of right mode `q` (the right region of the claim);
* `rigidQueryOf`: the right field of mode `q` cannot decrease a component `g` inside the right
  evolve domain: `evolveR ∧ ġ⁻ > 0` with `ġ⁻` the Lie derivative of `0 − g` along `q`'s field
  at stretch 1 (the right's own Lie derivative, `Bridge.ownLie`), the route-A shape.

The witness record `RefWitE` is what the (untrusted) finder emits.
-/
import RelCertifier.Trusted.BridgeQueries
import RelCertifier.Trusted.NonConnQuery

namespace RelCertifier.Refute

open RelCertifier RelCertifier.Parse RelCertifier.Run RelCertifier.Oracle

/-- A refutation witness, as the finder emits it: the kind (`"C"` no partner, `"A"` a component
broken at the switch, `"B"` a component pushed out by the left flow), the stored left mode `u`,
the entered left mode `m ∈ next(u)`, the stored right mode `q0`, the component index `k`
(kinds A and B), the left and right values (by coordinate). -/
structure RefWitE where
  kind : String
  u : ℕ
  m : ℕ
  q0 : ℕ
  k : ℕ
  wL : List ℚ
  wR : List ℚ
  deriving Repr, DecidableEq

/-- `⋀ᵢ Lᵢ = wᵢ` over every left coordinate (`0` past the list). -/
def fixLeft (n : ℕ) (wL : List ℚ) : IForm n :=
  ((List.finRange n).map (fun i =>
    IForm.cmp .eq (ITerm.var (Side.L, i)) (ITerm.rat (wL.getD i.val 0)))).foldl IForm.and IForm.tt

/-- `⋀ⱼ gⱼ ≤ 0` (the admissibility query's fold). -/
def compsConj {n : ℕ} (cs : List (ITerm n)) (b : IForm n) : IForm n :=
  cs.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) b

/-- The no-partner query of the entered row `row` at right mode `mR` (right evolve domain from
`mR0`, kept atoms `atoms`), at the left values `wL`. -/
def noPartnerQueryOf (vars : List String) (n : ℕ) (row : PForm) (mR0 mR : PMode)
    (atoms : List CutAtomX) (wL : List ℚ) : Option (IForm n) := do
  let cs ← invComponents vars n row
  let ev ← lowerF vars n Side.R mR0.evolve
  let gR ← lowerF vars n Side.R mR.guard
  let cut ← NonConn.cutOfAtoms vars n (atoms.map (·.atom))
  pure (IForm.and (IForm.and (IForm.and (compsConj cs (fixLeft n wL)) ev) gR) cut)

/-- The rigidity query of component `g` along right mode `mR` (right evolve domain from `mR0`):
`evolveR ∧ Lie_R(0 − g) > 0`. -/
def rigidQueryOf (vars : List String) (n : ℕ) (g : ITerm n) (mR0 mR : PMode) : Option (IForm n) := do
  let f ← dynOf vars n Side.R mR
  let ev ← lowerF vars n Side.R mR0.evolve
  pure (IForm.and ev
    (IForm.cmp .gt (Bridge.ownLie Side.R (ITerm.bin .sub (.rat 0) g) f) (.rat 0)))

end RelCertifier.Refute
