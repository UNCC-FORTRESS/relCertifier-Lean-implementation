/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Cut-certificate data and its kernel well-formedness check

The pure content of the checked-cut channel: candidate extraction (`cutAtoms`), the
safe-side lowering (`cutAtomG`), the no-Z3 route recognizers (`contractShapeOK`,
`frozenIn`), the route tag (`CutRoute`), the emitted certificate (`EvolStrengthening`), and the
decidable well-formedness check `evolStrengtheningWF` — every listed atom IS a nonstrict guard
conjunct of its named mode (O1, syntactic), and shape/frozen tags re-check by the pure
recognizers. DI-route atoms carry their O2 obligation at the `z3_unsat_sound` leaf,
assembled by the lift (`CutChannel` + the cut-lift theorems).

The O1/O2 *search* (`OracleAPI.checkedCut`) stays untrusted tool code; only its emitted
output is certified, Faithful-style.
-/
import RelCertifier.Trusted.Run
import RelCertifier.Checker.Faithful

namespace RelCertifier.Oracle

open RelCertifier RelCertifier.Parse RelCertifier.Run

/-- Atomic NON-STRICT (`≤`/`≥`) conjuncts of a `PForm` (candidate cuts). Strict atoms are
NOT candidates: a strict guard conjunct is typically the mode's EXIT face (not invariant),
and a strict candidate would vacuously pass the boundary route (its own strictness excludes
the boundary from the domain) — a closed-set discipline keeps O2 meaningful and DI-shaped. -/
def cutAtoms : PForm → List PForm
  | .and a b => cutAtoms a ++ cutAtoms b
  | .cmp op a b =>
      if op == "<=" || op == ">=" then [.cmp op a b] else []
  | _ => []

/-- Safe-side term of an atom `c` (`c = {g ≤ 0}`), lowered at `side`. -/
def cutAtomG (vars : List String) (n : ℕ) (side : Side) : PForm → Option (ITerm n)
  | .cmp op a b =>
      if op == "<=" || op == "<" then do
        let ea ← lowerE vars n side a; let eb ← lowerE vars n side b
        some (ITerm.bin .sub ea eb)
      else if op == ">=" || op == ">" then do
        let ea ← lowerE vars n side a; let eb ← lowerE vars n side b
        some (ITerm.bin .sub eb ea)
      else none
  | _ => none

/-- Variables of a `PExpr`. -/
def pexprVars : PExpr → List String
  | .var v => [v]
  | .num _ => []
  | .neg e => pexprVars e
  | .bin _ a b => pexprVars a ++ pexprVars b

/-- Variables of a `PForm` atom. -/
def atomVars : PForm → List String
  | .cmp _ a b => pexprVars a ++ pexprVars b
  | _ => []

/-- The mode's field for `v` is syntactically zero (absent ode, or a literal 0).
Kernel-fast: numeric comparison through `parseQ`/`QF` (raw fractions), never mathlib ℚ
or `String.splitOn` (which do not kernel-reduce — the `rfl` certificates below depend
on this). -/
def frozenIn (m : PMode) (v : String) : Bool :=
  match m.odes.find? (·.1 == v) with
  | none => true
  | some (_, .num s) =>
      match parseQ s with
      | some q => qIsZero q
      | none => false
  | some _ => false

/-- CONTRACT-SHAPE O2 (the tangent case): atom `v ≤ κ` (or `v ≥ κ`) with the mode's field
for `v` of the form `k·(c − v)` (`k ≥ 0`) and equilibrium on the safe side (`c ≤ κ` resp.
`c ≥ κ`). Every solution from the safe side stays there (monotone toward the interior
equilibrium — `contract_stays`). Kernel-fast rational comparison (`QF`), no Z3.
Recognized field shapes: `(* k (- c v))`, `(- c v)`, `(* k v)` with `k ≤ 0`
(decay, `c = 0`). -/
def contractShapeOK (m : PMode) : PForm → Bool
  | .cmp op (.var v) (.num κs) =>
      let le := op == "<=" || op == "<"
      let ge := op == ">=" || op == ">"
      if !(le || ge) then false else
      match parseQ κs, m.odes.find? (·.1 == v) with
      | some κ, some (_, f) =>
          let eq? : Option (QF × QF) :=      -- (k, c)
            match f with
            | .bin "*" (.num ks) (.bin "-" (.num cs) (.var w)) =>
                if w == v then do
                  let k ← parseQ ks; let c ← parseQ cs; pure (k, c)
                else none
            | .bin "-" (.num cs) (.var w) =>
                if w == v then (parseQ cs).map (fun c => (qOfInt 1, c)) else none
            | .bin "*" (.num ks) (.var w) =>
                if w == v then (parseQ ks).map (fun k => (qNeg k, qOfInt 0)) else none
            | _ => none
          match eq? with
          | some (k, c) => !(qLt k (qOfInt 0)) && (if le then !(qLt κ c) else !(qLt c κ))
          | none => false
      | _, _ => false
  | _ => false

/-- The O2 route by which a cut atom was justified (recorded in the emitted cut
certificate; the Lean lift consumes exactly these four cases). -/
inductive CutRoute
  | shape       -- tangent-capable contract shape (no Z3; `contract_stays`)
  | frozen      -- every atom variable is frozen in this mode (no Z3)
  | diStrict    -- UNSAT(evolve ∧ g = 0 ∧ ġ ≥ 0)  (`DI_strict`)
  | diNonstrict -- UNSAT(evolve ∧ ġ > 0)          (`DI_nonstrict_domain`)
  deriving Repr, DecidableEq

def CutRoute.tag : CutRoute → String
  | .shape => "shape"
  | .frozen => "frozen"
  | .diStrict => "diB"
  | .diNonstrict => "diA"

/-- Emitted cut certificate of one benchmark: per side, mode name ↦ kept atoms with
their routes. -/
structure EvolStrengthening where
  L : List (String × List (PForm × CutRoute))
  R : List (String × List (PForm × CutRoute))
  deriving Repr, DecidableEq

/-- Kernel well-formedness of one mode's cut entry. -/
def modeCutWF (m : PMode) (atoms : List (PForm × CutRoute)) : Bool :=
  atoms.all (fun ar =>
    (cutAtoms m.guard).contains ar.1 &&
    match ar.2 with
    | .shape => contractShapeOK m ar.1
    | .frozen => (atomVars ar.1).all (frozenIn m)
    | .diStrict => true
    | .diNonstrict => true)

/-- Kernel well-formedness of one side's cut entries (every named mode must exist). -/
def sideCutWF (modes : List PMode) (mcs : List (String × List (PForm × CutRoute))) :
    Bool :=
  mcs.all (fun mc =>
    match modes.find? (·.name == mc.1) with
    | some m => modeCutWF m mc.2
    | none => false)

/-- **Cut-certificate well-formedness** against the parsed problem (kernel-decidable;
certified by `rfl` per benchmark against the parser-emitted IR literal). -/
def evolStrengtheningWF (p : PProblem) (c : EvolStrengthening) : Bool :=
  sideCutWF p.L.modes c.L && sideCutWF p.R.modes c.R

end RelCertifier.Oracle
