/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Invariant components (leaf)

The lowering of an invariant row to its components `g_i ≤ 0` (the conjunct form of
Eq. (8)), and the oracle outcome. A leaf separate from `OracleAPI`: the kernel-facing instance
layer (`CoverInstance`) needs ONLY this definition, so `OracleAPI` edits do not invalidate
the instances.
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

/-! ## Multi-conjunct invariant lowering

Each `≤/<` atom `a ∼ b` becomes a component `g = a − b ≤ 0` (`≥/>` flips), a polynomial `p_i`
of Eq. (8); a strict atom lowers to its closure (`InvStrictFlags` records which were strict).
Conjunctions lower every component (one Lie condition per component, Section 4.1). `lowerE` handles
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
