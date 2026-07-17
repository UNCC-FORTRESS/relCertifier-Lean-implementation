/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Invariant components (leaf)

The multi-component invariant lowering, moved out of `OracleAPI` (S4): the
kernel-facing instance layer (`CoverInstance`) needs ONLY this definition, so the
instance batteries no longer depend on the tool door — future `OracleAPI` edits
stop invalidating them.
-/
import RelCertifier.Trusted.Run

namespace RelCertifier.Oracle

open RelCertifier.Parse RelCertifier.Run

/-- The three-way oracle outcome. -/
inductive Outcome
  | certified
  | declined
  | error (msg : String)
  deriving Repr

def Outcome.tag : Outcome → String
  | .certified => "CERTIFIED"
  | .declined  => "DECLINED"
  | .error _   => "ERROR"

/-! ## Multi-conjunct invariant lowering (broadened `invToG`)

Each `≤/<` atom `a ∼ b` becomes a safe-side component `g = a − b ≤ 0` (`≥/>` flips).
Conjunctions lower every component (per-component flow certificates). `lowerE` handles
`+ − ×`, so quadratic (`x*x`) and product (`v*r`) terms lower into `Term` and flow
through the unchanged `lieDeriv`/`flowQueryStrict`. If ANY component fails to lower,
returns `none` ⟹ the caller reports `error` (never silently drops a component). -/
def invComponents (vars : List String) (n : ℕ) : PForm → Option (List (ITerm n))
  | .tt => some []
  | .cmp op a b =>
      if op == "<=" || op == "<" then do
        let ea ← lowerE vars n Side.L a; let eb ← lowerE vars n Side.L b
        some [ITerm.bin .sub ea eb]
      else if op == ">=" || op == ">" then do
        let ea ← lowerE vars n Side.L a; let eb ← lowerE vars n Side.L b
        some [ITerm.bin .sub eb ea]
      else none                                   -- '=' invariant: unsupported ⟹ error
  | .and x y => do
      let lx ← invComponents vars n x; let ly ← invComponents vars n y
      some (lx ++ ly)
  | _ => none                                     -- disjunction/negation: unsupported ⟹ error

end RelCertifier.Oracle
