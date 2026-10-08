/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Extended cut certificate: implied-contraction and closure atoms (L1 / L2)

The checked-cut channel of `EvolStrengthening.lean` takes only atoms that are literal
CLOSED guard conjuncts (`x <= k` / `x >= k`); O1 (entry) is syntactic membership. Two
incompleteness gaps (docs/SUITE-REDESIGN.md §7):

* **L1 — implied atoms from the dynamics.** For a mode whose field for `x` is a
  contraction `x' = k (c − x)`, `k > 0`, the half-line `{x ≤ c}` (resp. `{x ≥ c}`) is
  forward-invariant (the flow is monotone toward the interior equilibrium `c`,
  `contract_stays`). The tightest such atom the guard implies is `x ≤ max(c, cap)` =
  `x ≤ c` when the guard's cap on `x` is at most `c` (otherwise the cap itself, a guard
  conjunct or its closure, is the tightest). So the implied candidates are exactly
  `x ≤ c` and `x ≥ c`; O1 is an IMPLICATION `guard → atom`, decided by rational
  comparison when the guard carries a threshold conjunct on `x` at least as tight
  (`guardImpliesRational`), otherwise by one Z3 query `UNSAT(guard ∧ ¬atom)` (tool side,
  counted); the certificate records which (`CutEntry.rational` / `CutEntry.z3`).
* **L2 — closures of strict guard atoms.** A strict conjunct `x < k` / `x > k` offers its
  closure `x ≤ k` / `x ≥ k`; O1 holds by weakening (`CutEntry.weakening`).

O2 (invariance) for either kind is as for any closed atom: the contract-shape route
(here over the wider field grammar of `contractEq`, `contractShapeOKX`), the frozen
route, or the two DI routes (Z3). Every kept atom — the legacy guard conjuncts included,
tagged `CutKind.guardConj` / `CutEntry.membership` with their legacy routes — is listed in
one `EvolStrengtheningX` certificate, so the later Lean lift sees, per atom, WHAT it must
prove for O1 and by WHICH route O2 was discharged.

Compatibility: this module ADDS definitions only. `EvolStrengthening`, `cutAtoms`,
`contractShapeOK`, `modeCutWF` and `evolStrengtheningWF` are unchanged, and the legacy
certificate the `suite_uniform` instances `rfl`-pin is emitted exactly as before; the
extended channel is off unless `RELCERT_IMPLIED_CUT=1` (`OracleAPI.impliedCutsOn`).
-/
import RelCertifier.Checker.EvolStrengthening

namespace RelCertifier.Oracle

open RelCertifier RelCertifier.Parse RelCertifier.Run

/-- Strict (`<` / `>`) atomic conjuncts of a `PForm` — the sources of the L2 closure
candidates (the dual of `cutAtoms`). -/
def strictAtoms : PForm → List PForm
  | .and a b => strictAtoms a ++ strictAtoms b
  | .cmp op a b => if op == "<" || op == ">" then [.cmp op a b] else []
  | _ => []

/-- The closure of a strict atom (`<` ↦ `<=`, `>` ↦ `>=`); `none` otherwise. -/
def closureOf : PForm → Option PForm
  | .cmp "<" a b => some (.cmp "<=" a b)
  | .cmp ">" a b => some (.cmp ">=" a b)
  | _ => none

/-- The contraction equation of the mode's field for `v`, if it has one: `v' = k (c − v)`
with `k > 0`, returned as `(k, c-literal, c)` — the literal is reused verbatim as the
atom's constant, so the emitted atom round-trips through `parseQ` exactly. Recognized
field shapes: `(* k (- c v))` with `k > 0`, `(- c v)`, `(* k v)` with `k < 0` (decay,
`c = 0`), `(* k (- v c))` with `k < 0`. The first three are `contractShapeOK`'s grammar;
the fourth (`k (v − c)`, `k < 0`) is the other spelling of the same field. -/
def contractEq (m : PMode) (v : String) : Option (QF × String × QF) :=
  match m.odes.find? (·.1 == v) with
  | some (_, f) =>
      let r : Option (QF × String × QF) :=
        match f with
        | .bin "*" (.num ks) (.bin "-" (.num cs) (.var w)) =>
            if w == v then do
              let k ← parseQ ks; let c ← parseQ cs; pure (k, cs, c)
            else none
        | .bin "-" (.num cs) (.var w) =>
            if w == v then (parseQ cs).map (fun c => (qOfInt 1, cs, c)) else none
        | .bin "*" (.num ks) (.var w) =>
            if w == v then (parseQ ks).map (fun k => (qNeg k, "0", qOfInt 0)) else none
        | .bin "*" (.num ks) (.bin "-" (.var w) (.num cs)) =>
            if w == v then do
              let k ← parseQ ks; let c ← parseQ cs; pure (qNeg k, cs, c)
            else none
        | _ => none
      match r with
      | some (k, cs, c) => if qLt (qOfInt 0) k then some (k, cs, c) else none
      | none => none
  | none => none

/-- Contract-shape O2 for the extended atoms (closed atoms only): the atom `v ≤ κ`
(resp. `v ≥ κ`) with the field for `v` a contraction toward `c` (`contractEq`) and the
equilibrium on the safe side, `c ≤ κ` (resp. `c ≥ κ`). The same test as
`contractShapeOK`, over `contractEq`'s field grammar. No Z3. -/
def contractShapeOKX (m : PMode) : PForm → Bool
  | .cmp op (.var v) (.num κs) =>
      let le := op == "<="
      let ge := op == ">="
      if !(le || ge) then false else
      match parseQ κs, contractEq m v with
      | some κ, some (_, _, c) => if le then !(qLt κ c) else !(qLt c κ)
      | _, _ => false
  | _ => false

/-- The L1 candidates of a mode: for every variable with a contraction field toward `c`,
the atoms `v ≤ c` and `v ≥ c` (each is kept only if O1 and O2 both pass). -/
def impliedCandidates (m : PMode) : List PForm :=
  m.odes.flatMap (fun ve =>
    match contractEq m ve.1 with
    | some (_, cs, _) => [.cmp "<=" (.var ve.1) (.num cs), .cmp ">=" (.var ve.1) (.num cs)]
    | none => [])

/-- Rational O1 for a threshold atom `v ≤ c` (resp. `v ≥ c`): the guard carries a
threshold conjunct on `v`, strict or not, at least as tight (`v ≤ k` / `v < k` with
`k ≤ c`, resp. `v ≥ k` / `v > k` with `k ≥ c`). Kernel-fast rational comparison. -/
def guardImpliesRational (guard : PForm) : PForm → Bool
  | .cmp op (.var v) (.num cs) =>
      match parseQ cs with
      | none => false
      | some c =>
          (cutAtoms guard ++ strictAtoms guard).any (fun t =>
            match t with
            | .cmp top (.var w) (.num ks) =>
                w == v && (match parseQ ks with
                  | none => false
                  | some k =>
                      if op == "<=" then (top == "<=" || top == "<") && !(qLt c k)
                      else if op == ">=" then (top == ">=" || top == ">") && !(qLt k c)
                      else false)
            | _ => false)
  | _ => false

/-- Two threshold atoms are the same cut (same variable, same operator, rationally equal
constants; other shapes compared structurally). Used to avoid offering an atom twice. -/
def atomEqQ : PForm → PForm → Bool
  | .cmp op1 (.var v1) (.num c1), .cmp op2 (.var v2) (.num c2) =>
      op1 == op2 && v1 == v2 &&
        (match parseQ c1, parseQ c2 with
         | some a, some b => qEq a b
         | _, _ => c1 == c2)
  | a, b => a == b

/-- The KIND of a kept cut atom (recorded in the extended certificate). -/
inductive CutKind
  | guardConj        -- a literal closed guard conjunct (the legacy channel)
  | impliedContract  -- `v ≤ c` / `v ≥ c` for a contraction field toward `c` (L1)
  | closure          -- the closure of a strict guard conjunct (L2)
  deriving Repr, DecidableEq

/-- How O1 (entry: the mode's guard implies the atom) was justified. -/
inductive CutEntry
  | membership  -- the atom IS a guard conjunct (guardConj)
  | rational    -- a threshold guard conjunct at least as tight; rational comparison
  | z3          -- `UNSAT(guard ∧ ¬atom)`, one counted Z3 query
  | weakening   -- the strict guard conjunct implies its closure (closure)
  deriving Repr, DecidableEq

def CutKind.tag : CutKind → String
  | .guardConj => "guard-conjunct"
  | .impliedContract => "implied-contraction"
  | .closure => "closure"

def CutEntry.tag : CutEntry → String
  | .membership => "membership"
  | .rational => "rational"
  | .z3 => "z3"
  | .weakening => "weakening"

/-- One kept atom of the extended certificate. -/
structure CutAtomX where
  atom  : PForm
  kind  : CutKind
  entry : CutEntry
  route : CutRoute
  deriving Repr, DecidableEq

/-- The extended cut certificate of one benchmark: per side, mode name ↦ every kept atom
with its kind, O1 justification and O2 route. The legacy `EvolStrengthening` of the same
run is its `guardConj` subset, in order. -/
structure EvolStrengtheningX where
  L : List (String × List CutAtomX)
  R : List (String × List CutAtomX)
  deriving Repr, DecidableEq

/-- Route re-check for an extended atom (shape over the wider grammar; frozen; DI routes
carry their obligation at the Z3 leaf). -/
def routeWFX (m : PMode) (a : PForm) : CutRoute → Bool
  | .shape => contractShapeOKX m a
  | .frozen => (atomVars a).all (frozenIn m)
  | .diStrict => true
  | .diNonstrict => true

/-- Kernel well-formedness of one kept atom against its mode. -/
def atomWFX (m : PMode) (x : CutAtomX) : Bool :=
  match x.kind with
  | .guardConj => x.entry == .membership && modeCutWF m [(x.atom, x.route)]
  | .closure =>
      x.entry == .weakening &&
      (strictAtoms m.guard).any (fun s => closureOf s == some x.atom) &&
      routeWFX m x.atom x.route
  | .impliedContract =>
      (impliedCandidates m).contains x.atom &&
      (match x.entry with
       | .rational => guardImpliesRational m.guard x.atom
       | .z3 => true
       | _ => false) &&
      routeWFX m x.atom x.route

def sideCutWFX (modes : List PMode) (mcs : List (String × List CutAtomX)) : Bool :=
  mcs.all (fun mc =>
    match modes.find? (·.name == mc.1) with
    | some m => mc.2.all (atomWFX m)
    | none => false)

/-- **Extended cut-certificate well-formedness** against the parsed problem
(kernel-decidable; the later Lean lift certifies it by `rfl` per benchmark). -/
def evolStrengtheningWFX (p : PProblem) (c : EvolStrengtheningX) : Bool :=
  sideCutWFX p.L.modes c.L && sideCutWFX p.R.modes c.R

/-- Human-readable atom (diagnostics only). -/
partial def ppExpr : PExpr → String
  | .var v => v
  | .num c => c
  | .neg a => s!"-({ppExpr a})"
  | .bin op a b => s!"({ppExpr a} {op} {ppExpr b})"

partial def ppForm : PForm → String
  | .tt => "true"
  | .cmp op a b => s!"{ppExpr a} {op} {ppExpr b}"
  | .and a b => s!"{ppForm a} and {ppForm b}"
  | .or a b => s!"({ppForm a}) or ({ppForm b})"
  | .not a => s!"not ({ppForm a})"

end RelCertifier.Oracle
