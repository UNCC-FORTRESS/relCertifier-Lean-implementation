/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Mode-fact records and their kernel well-formedness check

The data of the mode facts (paper Definition 2): candidate extraction (`cutAtoms`), the
safe-side lowering (`cutAtomG`), the no-Z3 route recognizers (`contractShapeOK`,
`frozenIn`), the route tag (`CutRoute`), the emitted record (`EvolStrengthening`), and the
decidable well-formedness check `evolStrengtheningWF`. A mode fact here is a conjunction of
atoms, each of which must be a nonstrict guard conjunct of its named mode, so the entry
clause `guard → fact` (O1) holds syntactically; shape and frozen tags are re-checked by
the pure recognizers. Atoms on a DI route carry their preservation clause
`fact → [flow] fact` (O2) as a Z3 verdict at the `z3_unsat_sound` leaf, assembled by the
lift (`CutChannel` and the cut-lift theorems).

The search for mode facts (`OracleAPI.checkedCut`) is untrusted tool code; only its
emitted records are checked, as with `Faithful`.
-/
import RelCertifier.Trusted.Run
import RelCertifier.Checker.Faithful

namespace RelCertifier.Oracle

open RelCertifier RelCertifier.Parse RelCertifier.Run

/-- Atomic non-strict (`≤`/`≥`) conjuncts of a `PForm`: the mode-fact candidates. Strict
atoms are not candidates: a strict guard conjunct is typically the mode's exit face (not
preserved by the flow), and a strict candidate would pass the boundary route vacuously (its
own strictness excludes the boundary from the domain). Keeping the facts closed keeps the
preservation clause O2 meaningful and in differential-invariant form. -/
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

/-- Contraction-shape route for O2 (covers the tangent case): atom `v ≤ κ` (or `v ≥ κ`)
with the mode's field for `v` of the form `k·(c − v)` (`k ≥ 0`) and its set point on the
safe side (`c ≤ κ` resp. `c ≥ κ`). Every solution from the safe side stays there
(monotone toward the set point, `contract_stays`). Kernel-fast rational comparison (`QF`),
no Z3. Recognized field shapes: `(* k (- c v))`, `(- c v)`, and `(* k v)` with `k ≤ 0`
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

/-- The route by which the preservation clause O2 of a mode-fact atom was justified
(recorded in the emitted mode-fact record; the Lean lift consumes exactly these four
cases). -/
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

/-- Emitted mode-fact record of one benchmark (paper Definition 2): per side, mode name ↦
the kept atoms, whose conjunction is that mode's fact, with their routes. -/
structure EvolStrengthening where
  L : List (String × List (PForm × CutRoute))
  R : List (String × List (PForm × CutRoute))
  deriving Repr, DecidableEq

/-- Kernel well-formedness of one mode's mode-fact entry: every atom is a non-strict guard
conjunct of the mode, and a shape or frozen tag passes its recognizer. -/
def modeCutWF (m : PMode) (atoms : List (PForm × CutRoute)) : Bool :=
  atoms.all (fun ar =>
    (cutAtoms m.guard).contains ar.1 &&
    match ar.2 with
    | .shape => contractShapeOK m ar.1
    | .frozen => (atomVars ar.1).all (frozenIn m)
    | .diStrict => true
    | .diNonstrict => true)

/-- Kernel well-formedness of one side's mode-fact entries (every named mode must exist). -/
def sideCutWF (modes : List PMode) (mcs : List (String × List (PForm × CutRoute))) :
    Bool :=
  mcs.all (fun mc =>
    match modes.find? (·.name == mc.1) with
    | some m => modeCutWF m mc.2
    | none => false)

/-- **Mode-fact record well-formedness** against the parsed problem (kernel-decidable;
certified by `rfl` per benchmark against the parser-emitted IR literal). -/
def evolStrengtheningWF (p : PProblem) (c : EvolStrengthening) : Bool :=
  sideCutWF p.L.modes c.L && sideCutWF p.R.modes c.R

end RelCertifier.Oracle
