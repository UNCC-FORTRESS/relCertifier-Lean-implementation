/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Extended cut certificate: implied-contraction, closure and linear-form atoms (L1 / L2 / L7)

The checked-cut channel of `EvolStrengthening.lean` takes only atoms that are literal
CLOSED guard conjuncts (`x <= k` / `x >= k`); O1 (entry) is syntactic membership. Three
incompleteness gaps (docs/SUITE-REDESIGN.md §7, §13):

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
* **L7 — linear-form cuts for second-order pairs (the domain audit).** A threshold atom
  on one variable cannot bound the overshoot of a damped second-order loop
  `x' = y, y' = −a (x − c) − b y` (the only invariant half-lines of a single coordinate
  are those the domain already gives), and no quadratic form can bound it tightly either
  (level sets are centrally symmetric about the equilibrium). For a critically or
  over-damped loop with RATIONAL eigenvalues (`b² − 4a` a rational square) the dynamics
  decouple: for each positive root `r` of `r² − b r + a = 0`, the LINEAR FORM
  `q = y + r (x − c)` satisfies `q' = −σ q` with `σ = b − r > 0` (the other root), so
  `{q ≤ K}` is forward-invariant for every `K ≥ 0` and `{q ≥ K}` for every `K ≤ 0`.
  Round 1 (`CutKind.linearForm`): the candidates are `q ≤ sup q` and `q ≥ inf q` over
  the guard's threshold box in `(x, y)` — O1 by rational interval arithmetic
  (`CutEntry.rational`; a guard without a box on both coordinates offers no candidate,
  since a Z3 entry check needs a constant to propose); O2 by the rational linear-shape
  route (`CutRouteX.linearShape`: on `{q ≥ K}` the Lie derivative `−σ q ≤ −σ K ≤ 0`),
  or the DI routes. Round 2 (`CutKind.derivedBound`, STRATIFIED on the round-1 atom it
  comes from, recorded in `given`): from `q ≤ K` the bound `x ≤ c + K / r` (resp.
  `x ≥ c + K / r` from `q ≥ K`) — O1 by `guardImpliesRational`, else one counted Z3
  query `UNSAT(guard ∧ ¬atom)`; O2 by the rational derived-shape route
  (`CutRouteX.derivedShape`: on `{x ≥ K'} ∩ {q ≤ K}`, `x' = y = q − r (x − c) ≤ K −
  r (K' − c) ≤ 0`), or the DI routes B, A and C over the evolve domain narrowed by the
  given atom. The DI routes A and B are both SAT at the tangent point `(x, q) = (K', K)`
  of a derived bound; the superlevel argument (route C, `DI_nonstrict_superlevel`) is
  what decides it, and `derivedShape` is its rational special case.
  Pairs are recognized SYNTACTICALLY (`secondOrderPairs`: `x' = y` literally a variable,
  `y' ` affine in `x, y` with both coefficients negative); no other candidate generation
  is attempted — the channel is deliberately not an invariant synthesizer.

Every kept atom — the legacy guard conjuncts included, tagged `CutKind.guardConj` /
`CutEntry.membership` with their legacy routes — is listed in one `EvolStrengtheningX`
certificate (`atom`, `kind`, `entry`, `route`, `given`), so the Lean lift
(`Proofs/Soundness/CutLiftX.lean`, kernel-checked well-formedness `evolStrengtheningWFX`
then `evolStrengtheningWFX_entryL/R`) sees,
per atom, WHAT it must prove for O1, by WHICH route O2 was discharged and on WHICH
earlier atoms the O2 domain was conditioned (sequential differential cuts, as
`strataDomIR` for the invariant components).

Compatibility: this module ADDS definitions only. `EvolStrengthening`, `cutAtoms`,
`contractShapeOK`, `modeCutWF` and `evolStrengtheningWF` are unchanged, and the
guard-conjunct certificate (the one the 19 carried-over legacy instances quote) is emitted
exactly as before; the extended channel is off unless `RELCERT_IMPLIED_CUT=1`
(`OracleAPI.impliedCutsOn`; every suite_v2 run sets it, 12 suite_v2 benchmarks need it), and
the L7 candidates can be switched off on their own with `RELCERT_NO_LINEAR_CUT=1`
(`OracleAPI.linearCutsOn`).
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

/-! ## L7 — linear-form cuts for second-order pairs -/

/-- Affine normal form of a `PExpr`: `(coefficients, constant)`, the coefficients as
`(variable, QF)` pairs (a variable may occur several times; `coeffOf` sums). `none` if
the expression is not affine (a product of two non-constant factors, a division, an
unparsable numeral). Structural recursion, kernel-fast. -/
def affineOf : PExpr → Option (List (String × QF) × QF)
  | .num s => (parseQ s).map (fun c => ([], c))
  | .var v => some ([(v, qOfInt 1)], qOfInt 0)
  | .neg a =>
      match affineOf a with
      | some (cs, k) => some (cs.map (fun vc => (vc.1, qNeg vc.2)), qNeg k)
      | none => none
  | .bin op a b =>
      match affineOf a, affineOf b with
      | some (ca, ka), some (cb, kb) =>
          if op == "+" then some (ca ++ cb, qAdd ka kb)
          else if op == "-" then
            some (ca ++ cb.map (fun vc => (vc.1, qNeg vc.2)), qSub ka kb)
          else if op == "*" then
            if ca.isEmpty then some (cb.map (fun vc => (vc.1, qMul ka vc.2)), qMul ka kb)
            else if cb.isEmpty then some (ca.map (fun vc => (vc.1, qMul kb vc.2)), qMul ka kb)
            else none
          else none
      | _, _ => none

/-- The summed coefficient of `v` in an affine coefficient list. -/
def coeffOf (cs : List (String × QF)) (v : String) : QF :=
  cs.foldl (fun acc vc => if vc.1 == v then qAdd acc vc.2 else acc) (qOfInt 0)

/-- A recognized second-order pair of a mode: `x' = y` (literally the variable) and
`y' = −a (x − c) − b y` with `a > 0`, `b > 0` (the field for `y` affine in `x` and `y`
only; `c = γ / a` for the constant term `γ`). -/
structure SOPair where
  x : String
  y : String
  a : QF
  b : QF
  c : QF
  deriving Repr, DecidableEq

/-- The second-order pairs of a mode, recognized syntactically (no other shape). -/
def secondOrderPairs (m : PMode) : List SOPair :=
  m.odes.flatMap (fun xe =>
    match xe.2 with
    | .var y =>
        if y == xe.1 then [] else
        match m.odes.find? (·.1 == y) with
        | none => []
        | some (_, fy) =>
            match affineOf fy with
            | none => []
            | some (cs, γ) =>
                if cs.all (fun vc => vc.1 == xe.1 || vc.1 == y || qIsZero vc.2) then
                  let α := coeffOf cs xe.1
                  let β := coeffOf cs y
                  if qLt α (qOfInt 0) && qLt β (qOfInt 0) then
                    let a := qNeg α
                    [{ x := xe.1, y := y, a := a, b := qNeg β, c := qDiv γ a }]
                  else []
                else []
    | _ => [])

/-- Newton iteration for `⌊√n⌋` from a start `x ≥ √n` (compiled search only; the kernel
re-checks a root by multiplication, never by this). -/
def natSqrtIter : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | fuel + 1, n, x =>
      if x == 0 then 0 else
      let y := (x + n / x) / 2
      if y ≥ x then x else natSqrtIter fuel n y

/-- Exact integer square root (`none` unless `n` is a square). -/
def natSqrt? (n : Nat) : Option Nat :=
  if n == 0 then some 0 else
  let r := natSqrtIter 400 n n
  if r * r == n then some r else none

/-- Exact rational square root (`none` unless the reduced numerator and denominator are
both squares). -/
def qSqrt? (q : QF) : Option QF :=
  if q.d ≤ 0 || q.n < 0 then none else
  let g : Int := Int.gcd q.n q.d
  if g == 0 then none else
  match natSqrt? (q.n / g).natAbs, natSqrt? (q.d / g).natAbs with
  | some sn, some sd => some ⟨sn, sd⟩
  | _, _ => none

/-- The positive rational roots of `r² − b r + a = 0` (the negated eigenvalues of the
pair; real iff `b² ≥ 4a`, rational iff the discriminant is a rational square), a double
root listed once; each root `r` is kept only with `b − r > 0` (the other root). -/
def pairRoots (a b : QF) : List QF :=
  let disc := qSub (qMul b b) (qMul (qOfInt 4) a)
  match qSqrt? disc with
  | none => []
  | some s =>
      let two := qOfInt 2
      let r1 := qDiv (qSub b s) two
      let r2 := qDiv (qAdd b s) two
      let rs := if qIsZero s then [r1] else [r1, r2]
      rs.filter (fun r => qLt (qOfInt 0) r && qLt (qOfInt 0) (qSub b r))

/-- `r` is a root of the pair's characteristic polynomial with `0 < r < b`
(kernel re-check of a root: multiplication, no square root). -/
def pairRootOK (p : SOPair) (r : QF) : Bool :=
  qIsZero (qAdd (qSub (qMul r r) (qMul p.b r)) p.a) &&
    qLt (qOfInt 0) r && qLt (qOfInt 0) (qSub p.b r)

/-- Smallest `k ≤ fuel` with `d ∣ 10^k` (`none` otherwise). -/
def pow10Mult (d : Int) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, k => if ((10 : Int) ^ k) % d == 0 then some k else pow10Mult d fuel (k + 1)

/-- Decimal numeral of a `QF` whose reduced denominator divides a power of ten (the
grammar `parseQ` accepts; `none` otherwise, e.g. `1/3`). Round-trips through `parseQ`
exactly, so an emitted constant is the rational the search computed. -/
def qDec? (q : QF) : Option String :=
  if q.d ≤ 0 then none else
  let g : Int := Int.gcd q.n q.d
  if g == 0 then none else
  let n := q.n / g
  let d := q.d / g
  match pow10Mult d 40 0 with
  | none => none
  | some k =>
      let m := n * (((10 : Int) ^ k) / d)
      let digits := (toString m.natAbs).toList
      let padded := if digits.length ≤ k
        then List.replicate (k + 1 - digits.length) '0' ++ digits else digits
      let whole := padded.take (padded.length - k)
      let frac := padded.drop (padded.length - k)
      let sign := if m < 0 then ['-'] else []
      some (String.mk (sign ++ whole ++ (if k == 0 then [] else '.' :: frac)))

/-- The linear form `y + r (x − c)` as a `PExpr`, in one fixed spelling so that the
emitted atom round-trips through `linearAtomParts`. -/
def linFormExpr (x y : String) (rS cS : String) : PExpr :=
  .bin "+" (.var y) (.bin "*" (.num rS) (.bin "-" (.var x) (.num cS)))

/-- Decompose a linear-form atom `y + r (x − c) ≤ K` / `≥ K` into
`(op, y, r, x, c, K)`. -/
def linearAtomParts : PForm →
    Option (String × String × QF × String × QF × QF)
  | .cmp op (.bin "+" (.var y) (.bin "*" (.num rS) (.bin "-" (.var x) (.num cS)))) (.num kS) =>
      if op == "<=" || op == ">=" then
        match parseQ rS, parseQ cS, parseQ kS with
        | some r, some c, some k => some (op, y, r, x, c, k)
        | _, _, _ => none
      else none
  | _ => none

/-- The tightest threshold bounds `(lo, hi)` the guard places on `v`, from its
`≤`/`<`/`≥`/`>` conjuncts with `v` alone on the left (strict bounds count: `v < k`
implies `v ≤ k`). -/
def guardBox (guard : PForm) (v : String) : Option QF × Option QF :=
  (cutAtoms guard ++ strictAtoms guard).foldl (fun acc t =>
    match t with
    | .cmp op (.var w) (.num ks) =>
        if w != v then acc else
        match parseQ ks with
        | none => acc
        | some k =>
            if op == "<=" || op == "<" then
              (acc.1, match acc.2 with
                | none => some k
                | some h => some (if qLt k h then k else h))
            else if op == ">=" || op == ">" then
              (match acc.1 with
                | none => some k
                | some l => some (if qLt l k then k else l), acc.2)
            else acc
    | _ => acc) (none, none)

/-- `sup` of `y + r (x − c)` over the guard's box in `(x, y)` (`r > 0`): needs both
upper bounds. -/
def linFormSup (guard : PForm) (p : SOPair) (r : QF) : Option QF :=
  match (guardBox guard p.x).2, (guardBox guard p.y).2 with
  | some xh, some yh => some (qAdd yh (qMul r (qSub xh p.c)))
  | _, _ => none

/-- `inf` of `y + r (x − c)` over the guard's box in `(x, y)` (`r > 0`). -/
def linFormInf (guard : PForm) (p : SOPair) (r : QF) : Option QF :=
  match (guardBox guard p.x).1, (guardBox guard p.y).1 with
  | some xl, some yl => some (qAdd yl (qMul r (qSub xl p.c)))
  | _, _ => none

/-- A round-1 linear-form candidate: the pair, the root, the side and the constant,
and the atom itself. -/
structure LinCand where
  pair : SOPair
  r    : QF
  isLe : Bool
  k    : QF
  atom : PForm
  deriving Repr, DecidableEq

/-- The L7 round-1 candidates of a mode: for every recognized pair and every positive
rational root, `q ≤ sup q` and `q ≥ inf q` over the guard box (each only when the box
bounds both coordinates on that side and the constants print as decimals). -/
def linearCandidates (m : PMode) : List LinCand :=
  (secondOrderPairs m).flatMap (fun p =>
    (pairRoots p.a p.b).flatMap (fun r =>
      match qDec? r, qDec? p.c with
      | some rS, some cS =>
          let e := linFormExpr p.x p.y rS cS
          let up := match linFormSup m.guard p r with
            | some k =>
                match qDec? k with
                | some kS => [{ pair := p, r := r, isLe := true, k := k,
                                atom := .cmp "<=" e (.num kS) : LinCand }]
                | none => []
            | none => []
          let lo := match linFormInf m.guard p r with
            | some k =>
                match qDec? k with
                | some kS => [{ pair := p, r := r, isLe := false, k := k,
                                atom := .cmp ">=" e (.num kS) : LinCand }]
                | none => []
            | none => []
          up ++ lo
      | _, _ => []))

/-- The recognized pair of a linear-form atom in this mode (parts parsed, pair found by
its coordinates and equilibrium, root re-checked by multiplication). -/
def linearAtomPair (m : PMode) (a : PForm) :
    Option (String × SOPair × QF × QF) :=
  match linearAtomParts a with
  | none => none
  | some (op, y, r, x, c, k) =>
      match (secondOrderPairs m).find? (fun p => p.x == x && p.y == y && qEq p.c c) with
      | some p => if pairRootOK p r then some (op, p, r, k) else none
      | none => none

/-- Rational O1 of a linear-form atom: its constant is at least the guard-box `sup`
(for `≤`), resp. at most the guard-box `inf` (for `≥`). -/
def linearEntryRational (m : PMode) (a : PForm) : Bool :=
  match linearAtomPair m a with
  | none => false
  | some (op, p, r, k) =>
      if op == "<=" then
        match linFormSup m.guard p r with
        | some s => !(qLt k s)
        | none => false
      else
        match linFormInf m.guard p r with
        | some s => !(qLt s k)
        | none => false

/-- Linear-shape O2 (rational, no Z3): `q = y + r (x − c)` with `q' = −(b − r) q`,
`b − r > 0`, and the constant on the safe side (`K ≥ 0` for `q ≤ K`, `K ≤ 0` for
`q ≥ K`): on `{q ≥ K}` (resp. `{q ≤ K}`) the Lie derivative of the safe-side term is
`≤ 0` (`DI_nonstrict_superlevel`). -/
def linearShapeOKX (m : PMode) (a : PForm) : Bool :=
  match linearAtomPair m a with
  | none => false
  | some (op, _, _, k) =>
      if op == "<=" then !(qLt k (qOfInt 0)) else !(qLt (qOfInt 0) k)

/-- The derived bound of a kept linear-form atom: `x ≤ c + K / r` from `q ≤ K`,
`x ≥ c + K / r` from `q ≥ K` (the point where `x' = y = q − r (x − c)` changes sign
under the cut). -/
def derivedOf (cand : LinCand) : Option PForm :=
  match qDec? (qAdd cand.pair.c (qDiv cand.k cand.r)) with
  | some kS => some (.cmp (if cand.isLe then "<=" else ">=") (.var cand.pair.x) (.num kS))
  | none => none

/-- Derived-shape O2 (rational, no Z3), GIVEN the linear-form atom `q ≤ K` (resp.
`≥`): the atom is `x ≤ K'` with `K' ≥ c + K / r` (resp. `x ≥ K'` with `K' ≤ c + K / r`)
on the same coordinate and side, so on `{x ≥ K'} ∩ {q ≤ K}` the field
`x' = y = q − r (x − c) ≤ K − r (K' − c) ≤ 0` (and symmetrically). -/
def derivedShapeOKX (m : PMode) (given : PForm) : PForm → Bool
  | .cmp op (.var w) (.num k'S) =>
      match linearAtomPair m given, parseQ k'S with
      | some (gop, p, r, k), some k' =>
          w == p.x && op == gop &&
            (let kd := qAdd p.c (qDiv k r)
             if op == "<=" then !(qLt k' kd) else !(qLt kd k'))
      | _, _ => false
  | _ => false

/-! ## The extended certificate -/

/-- The KIND of a kept cut atom (recorded in the extended certificate). -/
inductive CutKind
  | guardConj        -- a literal closed guard conjunct (the legacy channel)
  | impliedContract  -- `v ≤ c` / `v ≥ c` for a contraction field toward `c` (L1)
  | closure          -- the closure of a strict guard conjunct (L2)
  | linearForm       -- `y + r (x − c) ≤ K` / `≥ K` for a recognized 2nd-order pair (L7, round 1)
  | derivedBound     -- `x ≤ c + K/r` / `≥` from a kept linear-form atom (L7, round 2, stratified)
  deriving Repr, DecidableEq

/-- How O1 (entry: the mode's guard implies the atom) was justified. -/
inductive CutEntry
  | membership  -- the atom IS a guard conjunct (guardConj)
  | rational    -- a threshold guard conjunct at least as tight, or the guard box (linear forms); rational comparison
  | z3          -- `UNSAT(guard ∧ ¬atom)`, one counted Z3 query
  | weakening   -- the strict guard conjunct implies its closure (closure)
  deriving Repr, DecidableEq

/-- The O2 route of an extended atom: the four legacy routes plus the L7 rational
shapes and the superlevel DI route C (`UNSAT(dom ∧ g ≥ 0 ∧ ġ > 0)`,
`DI_nonstrict_superlevel`, the route that decides a derived bound at its tangent
point). Kept separate from `CutRoute` so that the legacy module stays untouched. -/
inductive CutRouteX
  | shape         -- `contractShapeOKX` (no Z3)
  | frozen        -- every atom variable frozen (no Z3)
  | diStrict      -- UNSAT(dom ∧ g = 0 ∧ ġ ≥ 0)   (route B)
  | diNonstrict   -- UNSAT(dom ∧ ġ > 0)           (route A)
  | linearShape   -- `linearShapeOKX` (no Z3)
  | derivedShape  -- `derivedShapeOKX` given the linear-form atom (no Z3)
  | diSuperlevel  -- UNSAT(dom ∧ g ≥ 0 ∧ ġ > 0)   (route C)
  deriving Repr, DecidableEq

def CutRouteX.ofLegacy : CutRoute → CutRouteX
  | .shape => .shape
  | .frozen => .frozen
  | .diStrict => .diStrict
  | .diNonstrict => .diNonstrict

def CutRouteX.tag : CutRouteX → String
  | .shape => "shape"
  | .frozen => "frozen"
  | .diStrict => "diB"
  | .diNonstrict => "diA"
  | .linearShape => "linear-shape"
  | .derivedShape => "derived-shape"
  | .diSuperlevel => "diC"

def CutKind.tag : CutKind → String
  | .guardConj => "guard-conjunct"
  | .impliedContract => "implied-contraction"
  | .closure => "closure"
  | .linearForm => "linear-form"
  | .derivedBound => "derived-bound"

def CutEntry.tag : CutEntry → String
  | .membership => "membership"
  | .rational => "rational"
  | .z3 => "z3"
  | .weakening => "weakening"

/-- One kept atom of the extended certificate. `given` lists the earlier kept atoms of
the same mode conjoined to this atom's O2 domain (sequential differential cut); `[]`
means the O2 was unconditioned over the bare evolve domain. -/
structure CutAtomX where
  atom  : PForm
  kind  : CutKind
  entry : CutEntry
  route : CutRouteX
  given : List PForm
  deriving Repr, DecidableEq

/-- The extended cut certificate of one benchmark: per side, mode name ↦ every kept atom
with its kind, O1 justification, O2 route and conditioning. The legacy
`EvolStrengthening` of the same run is its `guardConj` subset, in order. -/
structure EvolStrengtheningX where
  L : List (String × List CutAtomX)
  R : List (String × List CutAtomX)
  deriving Repr, DecidableEq

/-- Route re-check for an extended atom (the rational shapes re-run; frozen re-checked;
DI routes carry their obligation at the Z3 leaf). -/
def routeWFX (m : PMode) (a : PForm) (given : List PForm) : CutRouteX → Bool
  | .shape => contractShapeOKX m a
  | .frozen => (atomVars a).all (frozenIn m)
  | .diStrict => true
  | .diNonstrict => true
  | .linearShape => linearShapeOKX m a
  | .derivedShape =>
      match given with
      | [g] => derivedShapeOKX m g a
      | _ => false
  | .diSuperlevel => true

/-- The derived-bound atom has the shape `x op K'` on the given linear-form atom's
coordinate and side (what every route of a derived bound presupposes). -/
def derivedShapeWF (m : PMode) (given : PForm) : PForm → Bool
  | .cmp op (.var w) (.num k'S) =>
      match linearAtomPair m given, parseQ k'S with
      | some (gop, p, _, _), some _ => w == p.x && op == gop
      | _, _ => false
  | _ => false

/-- Kernel well-formedness of one kept atom against its mode, given the atoms kept
before it in the same mode (`prev`, for the stratified kinds). -/
def atomWFX (m : PMode) (prev : List CutAtomX) (x : CutAtomX) : Bool :=
  match x.kind with
  | .guardConj =>
      x.entry == .membership && x.given.isEmpty &&
      (match x.route with
       | .shape => modeCutWF m [(x.atom, .shape)]
       | .frozen => modeCutWF m [(x.atom, .frozen)]
       | .diStrict => modeCutWF m [(x.atom, .diStrict)]
       | .diNonstrict => modeCutWF m [(x.atom, .diNonstrict)]
       | _ => false)
  | .closure =>
      x.entry == .weakening && x.given.isEmpty &&
      (strictAtoms m.guard).any (fun s => closureOf s == some x.atom) &&
      routeWFX m x.atom [] x.route
  | .impliedContract =>
      x.given.isEmpty &&
      (impliedCandidates m).contains x.atom &&
      (match x.entry with
       | .rational => guardImpliesRational m.guard x.atom
       | .z3 => true
       | _ => false) &&
      routeWFX m x.atom [] x.route
  | .linearForm =>
      x.given.isEmpty && x.entry == .rational &&
      (linearAtomPair m x.atom).isSome &&
      linearEntryRational m x.atom &&
      routeWFX m x.atom [] x.route
  | .derivedBound =>
      match x.given with
      | [g] =>
          prev.any (fun p => p.kind == .linearForm && p.atom == g) &&
          derivedShapeWF m g x.atom &&
          (match x.entry with
           | .rational => guardImpliesRational m.guard x.atom
           | .z3 => true
           | _ => false) &&
          routeWFX m x.atom [g] x.route
      | _ => false

/-- All atoms of one mode, each checked against the ones before it. -/
def modeCutWFX (m : PMode) : List CutAtomX → List CutAtomX → Bool
  | _, [] => true
  | prev, x :: xs => atomWFX m prev x && modeCutWFX m (prev ++ [x]) xs

def sideCutWFX (modes : List PMode) (mcs : List (String × List CutAtomX)) : Bool :=
  mcs.all (fun mc =>
    match modes.find? (·.name == mc.1) with
    | some m => modeCutWFX m [] mc.2
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
