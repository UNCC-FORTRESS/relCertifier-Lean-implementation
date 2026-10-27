/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The Assumption 1 check of the right model (TRUSTED harness layer; strict in the recipe)

The paper's Assumption 1 (Well-Formedness): from every state satisfying a source-mode guard,
an evolution spanning the control interval `ε_r` exists, and every evolution of duration at
most `ε_r` ends in a state satisfying the guard of at least one declared successor mode.
The kernel states and proves (or refutes) it per benchmark (`WellFormedR`,
`InstancesV2/WellFormedBattery.lean`). This file is the tool's CHEAP, SUFFICIENT check of
BOTH halves, per right mode: completeness (clause (ii), steps 1–3) and, since 2026-10-26,
nonblocking (clause (i), steps 4–6; until then only clause (ii) was checked, and a right
model that blocks at its domain boundary, `vehicle_hypercert` with `s ≤ 8` in the right
evolve domain, passed). It is reported per right mode and counted. It only ever declines:
a single `relcert` run changes no verdict unless `RELCERT_WELLFORMED_STRICT=1`;
`--check-quick-v2` certifies in the strict mode (`certifyWFWith true`) and gates the report
against declared counts (the suite's right-mode count, 0 `UNKNOWN`, 0 `BLOCKING`,
`VerdictsV2.ExpectedSuiteV2`), since 2026-10-10.

Per right mode `q` (guard `G_q`, a conjunction of comparison atoms `gₐ ≤ 0` / `gₐ < 0`,
lowered on the right; field `f_q`; evolve domain `D_q`), clause (ii) first:

1. **Stratified invariance of the guard atoms** (the cut channel's O2 routes, run on `q`'s
   own flow, the left held still): round by round, an atom is kept by the contraction-shape
   route (`contractShapeOK`, `contractShapeOKX`: `x ≤ κ` / `x ≥ κ` under `x' = k (c − x)`, the set
   point on the safe side; no Z3), the frozen route, route B
   `UNSAT(D_q ∧ I ∧ gₐ = 0 ∧ ġₐ ≥ 0)` or route A `UNSAT(D_q ∧ I ∧ ġₐ > 0)`, `I` the atoms
   kept in EARLIER rounds (sequential differential cuts, never mutual). Every route keeps
   `gₐ ≤ 0` and `gₐ < 0` along every run inside `D_q ∧ I`. If every atom is kept and
   `q` declares its self-loop: **`ok (invariant)`**: every run from `G_q` stays in `G_q`.
1b. **Successor-guard facts.** An atom of a declared successor's guard joins the facts when
   `UNSAT(D_q ∧ G_q ∧ ¬c)` (it holds initially) and a step-1 route keeps it over the facts
   so far. It only narrows step 2, so it never turns an `ok` into `UNKNOWN` (added
   2026-10-20: `watertank`'s `Low`, whose crude rate bound overshot after the 10/3 pump-rate
   rescale, is `ok (exit)` with `x < 17` from MidEco's guard).
2. **Exit within one interval.** Otherwise, for each atom `a` not kept, a rate bound
   `Lₐ ≥ 0` with `UNSAT(D_q ∧ I ∧ ġₐ > Lₐ)` (bisection on the grid `k/100`, `k ≤ 10⁶`). A run
   of duration `t ≤ ε_r` from `G_q` stays in `D_q ∧ I` and ends with `gₐ ≤ gₐ(0) + Lₐ t ≤
   Lₐ ε_r` (strict when the atom is strict). One coverage query
   `UNSAT(D_q ∧ I ∧ ⋀ₐ gₐ ≤ Lₐ ε_r ∧ ⋀_{s ∈ next(q)} ¬G_s)` then shows that every such end
   state satisfies a declared successor's guard: **`ok (exit→S)`**, `S` the successors the
   query needs (greedily minimized, one query per dropped successor).
3. Anything else (a route not `unsat`, an unlowerable guard or field, a disjunctive guard,
   no rate bound): **`UNKNOWN`**. Sufficient, not necessary.

Then clause (i), on a mode whose clause (ii) is `ok`: from every state of `X₀ = G_q ∧ D_q`
the (unique, polynomial-field) solution exists on `[0, ε_r]` and stays in `D_q`, so a run of
the full interval exists (`WellFormedR`'s first conjunct, with its domain conjunct). `I` is the
fact formula of steps 1/1b (it holds along every run inside `D_q` from `X₀`).

4. **The domain persists, atom by atom.** Every atom `d ≤ 0` of `D_q` (a conjunction of
   comparisons, else `UNKNOWN`) is shown to persist past the first time `τ < ε_r` the
   solution would leave the set of atoms shown, by one of: (R1) the contraction-shape or
   frozen route (exact for the unconstrained flow: the atom's variable has a scalar field);
   (R3, closed atoms) the boundary route `UNSAT(D_q ∧ I ∧ d = 0 ∧ ḋ ≥ 0)`; (R5)
   `UNSAT(P ∧ ¬(d ≤ 0))`, (R4) `UNSAT(P ∧ ḋ > 0)` or, for a threshold atom `x ⋈ c`, (R6)
   `UNSAT(P ∧ ḋ[x := c] > 0)` (`ḋ = q d + r` with `r ≤ 0`), R4/R6 for closed atoms, `P` the
   atoms shown before (sequential, never mutual); (R2) the interval margin: a rate bound
   `UNSAT(D_q ∧ I ∧ ḋ > L)` and `UNSAT(X₀ ∧ d + L ε_r > 0)` (`≥ 0` when `L = 0` or the atom
   is strict), so `d(τ) ≤ d(0) + L τ < 0`. The closures of the guard atoms (they hold on
   `X₀`) are optional candidates for `P`. Route A over `D_q` (`ḋ ≤ 0` on the domain) is NOT a
   route here: it speaks only of runs that stay in `D_q`, which is what clause (i) has to
   establish.
5. **Or the domain polyhedron persists.** Otherwise, when every domain atom is closed and
   affine: the polyhedron `K` of the domain atoms and the affine candidates is invariant if
   at each face the field points inward, `UNSAT(K ∧ k = 0 ∧ k̇ > 0)` for every atom `k` of
   `K` (Nagumo / Bony–Brezis: the tangent cone of a polyhedron is cut out by its active
   faces; the field is polynomial, so locally Lipschitz), a greatest fixpoint over the
   candidates (e.g. the satellites' `h ≤ 2` under `h' = 2.5 w₃`, kept on the face `h = 2` by
   the conserved band `h + 5 w₃ ≤ 2`).
6. **Existence.** Every field affine (`affineOf`): solutions are global. Otherwise every
   moving coordinate's field is bounded on `D_q ∧ I` (`|fᵢ| ≤ 10⁴`, two queries), so the
   solution stays bounded while it stays in `D_q` and cannot blow up before `ε_r`.

A domain atom no route keeps is checked for an immediate exit,
`SAT(X₀ ∧ d = 0 ∧ ḋ > 0)`: some start state leaves `D_q` at once, so no run of duration
`ε_r > 0` exists and clause (i) is FALSE: **`BLOCKING (d)`** (a Z3 `sat` only ever turns a
mode into a failure, never into `ok`). Otherwise **`UNKNOWN (nonblocking)`**. The
per-mode label of an `ok` mode stays the clause (ii) style (`invariant` / `exit→S`, the Lean
proofs' styles (a) / (b)); `ok` now means both clauses.

Only `unsat` counts, as everywhere in the tool; any other answer degrades to `UNKNOWN`.
-/
import RelCertifier.Trusted.OracleAPI
import RelCertifier.Trusted.KeyAudit

namespace RelCertifier.WellFormed

open RelCertifier RelCertifier.Parse RelCertifier.Run RelCertifier.Oracle

/-- A guard atom: the source form, its safe-side term `g` (`g ≤ 0`, or `g < 0` when
strict), lowered on the right. -/
structure GAtom (n : ℕ) where
  form   : PForm
  g      : ITerm n
  strict : Bool

/-- The comparison atoms of a conjunctive guard; `none` for a disjunction / negation /
equation or an atom that does not lower (the mode is then `UNKNOWN`). -/
def guardAtoms (vars : List String) (n : ℕ) : PForm → Option (List (GAtom n))
  | .tt => some []
  | .and a b => do
      let xs ← guardAtoms vars n a
      let ys ← guardAtoms vars n b
      pure (xs ++ ys)
  | .cmp op a b => do
      if !(op == "<=" || op == "<" || op == ">=" || op == ">") then none
      let g ← cutAtomG vars n Side.R (.cmp op a b)
      pure [{ form := .cmp op a b, g := g, strict := op == "<" || op == ">" }]
  | _ => none

/-- An atom as a formula: `g ≤ 0` / `g < 0`. -/
def GAtom.toF {n : ℕ} (a : GAtom n) : IForm n :=
  IForm.cmp (if a.strict then .lt else .le) a.g (.rat 0)

/-- The per-mode result. `invariant` / `exit` are `ok` (both clauses shown; the label is
the clause (ii) style); `unknown` is clause (ii) undecided, `unknownRun` clause (ii) shown
and clause (i) undecided, `blocking` clause (i) refuted (a start state leaves the domain at
once). -/
inductive ModeWF
  | invariant
  | exit (succ : List String)
  | unknown (why : String)
  | unknownRun (why : String)
  | blocking (atom : String)

def ModeWF.ok : ModeWF → Bool
  | .invariant => true
  | .exit _ => true
  | _ => false

def ModeWF.show (q : String) : ModeWF → String
  | .invariant => s!"{q} ok (invariant)"
  | .exit ss => s!"{q} ok (exit→{String.intercalate "," ss})"
  | .unknown _ => s!"{q} UNKNOWN"
  | .unknownRun _ => s!"{q} UNKNOWN (nonblocking)"
  | .blocking a => s!"{q} BLOCKING (leaves {a})"

/-- The smallest `k/100` (`k ≤ 10⁶`) with `UNSAT(dom ∧ ġ > k/100)`, by bisection; `none`
if even `10⁴` is not a bound (or a query is not `unsat`). -/
def rateBound {n : ℕ} (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (coord : Fin n → String) (dom : IForm n) (gdot : ITerm n) : IO (Option ℚ) := do
  let bounded (k : Nat) : IO Bool :=
    probeUnsat s cnt maxQ maxSmt deadline coord
      (IForm.and dom (IForm.cmp .gt gdot (.rat ((k : ℚ) / 100))))
  if !(← bounded 1000000) then return none
  let mut lo := 0          -- lo: not known to be a bound (or 0)
  let mut hi := 1000000    -- hi: a bound
  if ← bounded 0 then return some 0
  while hi - lo > 1 do
    let mid := (lo + hi) / 2
    if ← bounded mid then hi := mid else lo := mid
  return some ((hi : ℚ) / 100)

/-- One Z3 probe answered `sat` (budget-counted). Used ONLY to report a mode `BLOCKING`
(a failure); never to accept anything. -/
def probeSat {n : ℕ} (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (coord : Fin n → String) (q : IForm n) : IO Bool := do
  let script := q.toScript coord
  if script.length > maxSmt then pure false
  else do
    cnt.modify (· + 1)
    if (← cnt.get) > maxQ then throw (IO.userError "query budget exceeded")
    if (← IO.monoMsNow) > deadline then throw (IO.userError "time budget exceeded")
    match ← s.check script with
    | .ok .sat => pure true
    | _ => pure false

/-- Conjoin atoms onto a formula. -/
def conjAtoms {n : ℕ} (base : IForm n) (as : List (GAtom n)) : IForm n :=
  as.foldl (fun d c => IForm.and d c.toF) base

/-- Substitute the rational `c` for the coordinate `x` (the remainder of a polynomial
Lie derivative on the hyperplane `x = c`). -/
def substVar {n : ℕ} (x : Var n) (c : ℚ) : ITerm n → ITerm n
  | .var v => if v = x then .rat c else .var v
  | .rat q => .rat q
  | .bin op a b => .bin op (substVar x c a) (substVar x c b)

/-- A threshold atom `x ⋈ c` (either orientation): the coordinate of `x`, resolved on the
right as the atom itself is lowered (`cutAtomG … Side.R`), and `c`. -/
def thresholdOf (vars : List String) (n : ℕ) : PForm → Option (Var n × ℚ)
  | .cmp _ (.var x) (.num cs) | .cmp _ (.num cs) (.var x) => do
      let c ← parseRat cs
      let v ← resolveVar vars n Side.R x
      pure (v, c)
  | _ => none

/-- The closure of a guard atom (`<` ↦ `≤`): the same term, not strict. -/
def GAtom.closure {n : ℕ} (a : GAtom n) : GAtom n := { a with strict := false }

/-- An atom with affine sides (`affineOf`): a half-space. -/
def GAtom.affine {n : ℕ} (a : GAtom n) : Bool :=
  match a.form with
  | .cmp _ x y => (affineOf x).isSome && (affineOf y).isSome
  | _ => false

/-- **Clause (i), stratified routes** (module docstring, step 4): the indices among the
first `nReq` atoms (the domain atoms) NOT shown to persist. `atoms` are the domain atoms
followed by optional candidates (closures of guard atoms, which hold on `X₀`): a candidate
that persists joins `P`, one that does not is dropped. `start` is `X₀`, `inv` is `D_q ∧ I`.
Routes per atom: R1 (exact), R3 (boundary, closed atoms) once each; then rounds of R5
(implied by `P`), R4 (`ḋ ≤ 0` on `P`) and R6 (threshold atoms `x ⋈ c`: the remainder
`ḋ[x := c] ≤ 0` on `P`; `ḋ − ḋ[x := c]` is a polynomial multiple of `d`, so `d` obeys
`ḋ = q d + r` with `r ≤ 0`, and `d ≤ 0` persists by variation of constants) while `P`
grows; then the margin R2 once per remaining domain atom, and rounds again after any
progress. R4/R6 are for closed atoms. Each route shows that the atom persists for a while
after the first time `τ < ε_r` the solution would leave the set of atoms shown, so that set
is not left before `ε_r`. -/
def persistStrat {n : ℕ} (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (coord : Fin n → String) (m : PMode) (epsR : ℚ)
    (f : Fin n → ITerm n) (atoms : List (GAtom n)) (nReq : Nat) (start inv : IForm n) :
    IO (List Nat) := do
  let zeroF : Fin n → ITerm n := fun _ => ITerm.rat 0
  let gdotOf (a : GAtom n) : ITerm n := ilieDeriv a.g zeroF f (ITerm.rat 1)
  let probe := probeUnsat s cnt maxQ maxSmt deadline coord
  let idx := List.range atoms.length
  let mut done : List Nat := []
  let mut pers : IForm n := IForm.tt
  -- R1, R3 (independent of `P`)
  for j in idx do
    match atoms[j]? with
    | none => pure ()
    | some a =>
        let exact := contractShapeOK m a.form || contractShapeOKX m a.form ||
          (atomVars a.form).all (frozenIn m)
        let ok ← if exact then pure true
          else if a.strict then pure false
          else probe (IForm.and inv (IForm.and (IForm.cmp .eq a.g (.rat 0))
            (IForm.cmp .ge (gdotOf a) (.rat 0))))
        if ok then done := done ++ [j]; pers := IForm.and pers a.toF
  let mut margined : List Nat := []
  for _ in List.range (atoms.length + 1) do
    -- R5 / R4 / R6 rounds over the atoms shown so far
    for _ in List.range (atoms.length + 1) do
      let mut progress := false
      for j in idx do
        if done.contains j then pure () else
        match atoms[j]? with
        | none => pure ()
        | some a =>
            let gd := gdotOf a
            let ok ← if ← probe (IForm.and pers (IForm.neg a.toF)) then pure true
              else if a.strict then pure false
              else if ← probe (IForm.and pers (IForm.cmp .gt gd (.rat 0))) then pure true
              else match thresholdOf vars n a.form with
                | some (x, c) =>
                    probe (IForm.and pers (IForm.cmp .gt (substVar x c gd) (.rat 0)))
                | none => pure false
            if ok then done := done ++ [j]; pers := IForm.and pers a.toF; progress := true
      if !progress then break
    -- R2, the interval margin, once per remaining domain atom
    let mut progress := false
    for j in idx do
      if done.contains j || margined.contains j || j ≥ nReq then pure () else
      match atoms[j]? with
      | none => pure ()
      | some a =>
          margined := margined ++ [j]
          match ← rateBound s cnt maxQ maxSmt deadline coord inv (gdotOf a) with
          | none => pure ()
          | some L =>
              let reach := ITerm.bin .add a.g (.rat (L * epsR))
              if ← probe (IForm.and start
                  (IForm.cmp (if L == 0 || a.strict then .ge else .gt) reach (.rat 0))) then
                done := done ++ [j]; pers := IForm.and pers a.toF; progress := true
    if !progress then break
  return (List.range nReq).filter (fun j => !done.contains j)

/-- **Clause (i), the polyhedral route** R8 (module docstring, step 5): the polyhedron `K`
of the (closed, affine) domain atoms and the affine candidates is kept by the flow when at
each face the field points inward, `UNSAT(K ∧ k = 0 ∧ k̇ > 0)` for every atom `k` of `K`
(the tangent cone of a polyhedron is cut out by its active faces; Nagumo / Bony–Brezis, the
field polynomial hence locally Lipschitz). A greatest fixpoint over the candidates (a
failing candidate is dropped and the rest re-checked); `true` iff every domain atom stays.
`X₀ ⊆ K`: the domain atoms hold on `D_q`, the candidates are closures of guard atoms. -/
def persistPoly {n : ℕ} (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (coord : Fin n → String) (f : Fin n → ITerm n) (datoms cands : List (GAtom n)) :
    IO Bool := do
  if !(datoms.all (fun a => a.affine && !a.strict)) then return false
  let zeroF : Fin n → ITerm n := fun _ => ITerm.rat 0
  let face (kf : IForm n) (a : GAtom n) : IO Bool :=
    probeUnsat s cnt maxQ maxSmt deadline coord (IForm.and kf (IForm.and
      (IForm.cmp .eq a.g (.rat 0)) (IForm.cmp .gt (ilieDeriv a.g zeroF f (ITerm.rat 1)) (.rat 0))))
  let mut ks := cands.filter (fun c => c.affine && !c.strict)
  for _ in List.range (ks.length + 1) do
    let kf := conjAtoms IForm.tt (datoms ++ ks)
    for a in datoms do
      if !(← face kf a) then return false
    let keep ← ks.filterM (face kf)
    if keep.length == ks.length then return true
    ks := keep
  return false

/-- The clause (i) result of one right mode. -/
inductive RunWF
  | ok
  | unknown (why : String)
  | blocking (atom : String)

/-- **Clause (i) of one right mode** (module docstring, steps 4–6): `start` is
`X₀ = G_q ∧ D_q`, `inv` the clause (ii) facts `D_q ∧ I`. -/
def checkRun {n : ℕ} (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (coord : Fin n → String) (m : PMode) (epsR : ℚ)
    (f : Fin n → ITerm n) (start inv : IForm n) : IO RunWF := do
  let some datoms := guardAtoms vars n m.evolve
    | return .unknown "the evolve domain is not a conjunction of comparisons"
  -- 6. existence: global for an affine field, else every moving coordinate's field bounded
  -- on `D_q ∧ I`
  if !(m.odes.all (fun ve => (affineOf ve.2).isSome)) then
    for i in List.finRange n do
      if f i != ITerm.rat 0 then
        let hi ← probeUnsat s cnt maxQ maxSmt deadline coord
          (IForm.and inv (IForm.cmp .gt (f i) (.rat 10000)))
        let lo ← probeUnsat s cnt maxQ maxSmt deadline coord
          (IForm.and inv (IForm.cmp .lt (f i) (.rat (-10000))))
        if !(hi && lo) then return .unknown s!"no bound on the field of {coord i}"
  -- 4./5. the domain persists (the closures of the guard atoms as optional candidates)
  let some gatoms := guardAtoms vars n m.guard
    | return .unknown "the guard is not a conjunction of comparisons"
  let cands := (gatoms.map GAtom.closure).filter (fun c => !(datoms.any (·.form == c.form)))
  let fails ← persistStrat s cnt maxQ maxSmt deadline vars coord m epsR f (datoms ++ cands)
    datoms.length start inv
  if fails.isEmpty then return .ok
  if ← persistPoly s cnt maxQ maxSmt deadline coord f datoms cands then return .ok
  let failAtoms := fails.filterMap (datoms[·]?)
  -- refutation: a start state on the boundary of a failing closed atom that leaves at once
  if epsR > 0 then
    let zeroF : Fin n → ITerm n := fun _ => ITerm.rat 0
    for a in failAtoms do
      if !a.strict then
        if ← probeSat s cnt maxQ maxSmt deadline coord (IForm.and start
            (IForm.and (IForm.cmp .eq a.g (.rat 0))
              (IForm.cmp .gt (ilieDeriv a.g zeroF f (ITerm.rat 1)) (.rat 0)))) then
          return .blocking (ppForm a.form)
  return .unknown s!"domain atom(s) not shown to persist: \
{String.intercalate ", " (failAtoms.map (ppForm ·.form))}"

/-- **Clause (ii) of one right mode** (module docstring, steps 1–3), with the fact formula
`D_q ∧ I` it established (steps 1/1b). -/
def checkSucc (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (p : PProblem) (vars : List String) (n : ℕ) (coord : Fin n → String) (epsR : ℚ)
    (m : PMode) (atoms : List (GAtom n)) (dom : IForm n) (f : Fin n → ITerm n) :
    IO (ModeWF × IForm n) := do
      let zeroF : Fin n → ITerm n := fun _ => ITerm.rat 0
      let gdotOf (a : GAtom n) : ITerm n := ilieDeriv a.g zeroF f (ITerm.rat 1)
      -- 1. stratified invariance
      let mut kept : List Nat := []
      for _ in List.range (atoms.length + 1) do
        let mut progress := false
        let strata := kept.foldl (fun d i =>
          match atoms[i]? with
          | some a => IForm.and d a.toF
          | none => d) dom
        for i in List.range atoms.length do
          if kept.contains i then pure () else
          match atoms[i]? with
          | none => pure ()
          | some a =>
              let gd := gdotOf a
              let rB := IForm.and strata (IForm.and (IForm.cmp .eq a.g (.rat 0))
                (IForm.cmp .ge gd (.rat 0)))
              -- the cut channel's Z3-free routes first: the contraction shape (`x ≤ κ` /
              -- `x ≥ κ` under `x' = k (c − x)` with the set point on the safe side) and a
              -- frozen atom
              if contractShapeOK m a.form || contractShapeOKX m a.form ||
                  (atomVars a.form).all (frozenIn m) then
                kept := kept ++ [i]; progress := true
              else if ← probeUnsat s cnt maxQ maxSmt deadline coord rB then
                kept := kept ++ [i]; progress := true
              else if ← probeUnsat s cnt maxQ maxSmt deadline coord
                  (IForm.and strata (IForm.cmp .gt gd (.rat 0))) then
                kept := kept ++ [i]; progress := true
        if !progress then break
      let guardF := atoms.foldl (fun d a => IForm.and d a.toF) dom
      let selfLoop := m.next.contains m.name
      if kept.length == atoms.length && selfLoop then return (.invariant, guardF)
      -- 1b. successor-guard facts: an atom of a declared successor's guard joins the
      -- invariant facts when the mode's guard and domain imply it initially
      -- (`UNSAT(D_q ∧ G_q ∧ ¬c)`) and a route keeps it along `q`'s flow, in rounds over
      -- the facts kept so far (the same sequential cuts as step 1). Sound: every fact holds
      -- along every run from `G_q` inside `D_q`, so it may narrow the rate bounds and the
      -- reach box below. Only ever adds facts, so it can turn UNKNOWN into ok, never the
      -- reverse.
      let mut inv := kept.foldl (fun d i =>
        match atoms[i]? with
        | some a => IForm.and d a.toF
        | none => d) dom
      let mut cands : List (GAtom n) := []
      for nm in m.next do
        match p.R.modes.find? (·.name == nm) with
        | none => pure ()
        | some ms =>
            match guardAtoms vars n ms.guard with
            | none => pure ()
            | some cs => cands := cands ++ cs
      let mut extra : List Nat := []
      for _ in List.range (cands.length + 1) do
        let mut progress := false
        for i in List.range cands.length do
          if extra.contains i then pure () else
          match cands[i]? with
          | none => pure ()
          | some c =>
              if ← probeUnsat s cnt maxQ maxSmt deadline coord
                  (IForm.and guardF (IForm.neg c.toF)) then
                let gd := gdotOf c
                let rB := IForm.and inv (IForm.and (IForm.cmp .eq c.g (.rat 0))
                  (IForm.cmp .ge gd (.rat 0)))
                if contractShapeOK m c.form || contractShapeOKX m c.form ||
                    (atomVars c.form).all (frozenIn m) ||
                    (← probeUnsat s cnt maxQ maxSmt deadline coord rB) ||
                    (← probeUnsat s cnt maxQ maxSmt deadline coord
                      (IForm.and inv (IForm.cmp .gt gd (.rat 0)))) then
                  extra := extra ++ [i]; inv := IForm.and inv c.toF; progress := true
        if !progress then break
      -- 2. exit within one interval
      let mut reach := inv
      for i in List.range atoms.length do
        if kept.contains i then pure () else
        match atoms[i]? with
        | none => pure ()
        | some a =>
            match ← rateBound s cnt maxQ maxSmt deadline coord inv (gdotOf a) with
            | none => return (.unknown s!"no rate bound for {ppForm a.form}", inv)
            | some L =>
                reach := IForm.and reach
                  (IForm.cmp (if a.strict then .lt else .le) a.g (.rat (L * epsR)))
      -- the declared successors and their lowered guards
      let mut succs : List (String × IForm n) := []
      for nm in m.next do
        match p.R.modes.find? (·.name == nm) with
        | none => return (.unknown s!"undeclared successor {nm}", inv)
        | some ms =>
            match lowerF vars n Side.R ms.guard with
            | none => return (.unknown s!"unlowerable guard of {nm}", inv)
            | some gs => succs := succs ++ [(nm, gs)]
      let covers (ss : List (String × IForm n)) : IO Bool :=
        probeUnsat s cnt maxQ maxSmt deadline coord
          (ss.foldl (fun d sg => IForm.and d (IForm.neg sg.2)) reach)
      if !(← covers succs) then
        return (.unknown "the reach box leaves every successor guard", inv)
      -- greedy minimization: drop a successor when the rest still cover (the other
      -- successors first, the self-loop last)
      let mut need := succs
      for sg in (succs.filter (·.1 != m.name)) ++ (succs.filter (·.1 == m.name)) do
        let rest := need.filter (·.1 != sg.1)
        if ← covers rest then need := rest
      let others := (need.map (·.1)).filter (· != m.name)
      if others.isEmpty then return (.invariant, inv)   -- covered by its own guard (self-loop)
      return (.exit others, inv)

/-- **The check of one right mode** (see the module docstring): clause (ii), then, on an
`ok`, clause (i) over the facts clause (ii) established. -/
def checkMode (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (p : PProblem) (vars : List String) (n : ℕ) (coord : Fin n → String) (epsR : ℚ)
    (m : PMode) : IO ModeWF := do
  match guardAtoms vars n m.guard, lowerF vars n Side.R m.evolve, dynOf vars n Side.R m with
  | some atoms, some dom, some f =>
      let (r, inv) ← checkSucc s cnt maxQ maxSmt deadline p vars n coord epsR m atoms dom f
      if !r.ok then return r
      let start := atoms.foldl (fun d a => IForm.and d a.toF) dom
      match ← checkRun s cnt maxQ maxSmt deadline vars coord m epsR f start inv with
      | .ok => return r
      | .unknown why => return .unknownRun why
      | .blocking a => return .blocking a
  | none, _, _ => return .unknown "guard is not a conjunction of comparisons"
  | _, none, _ => return .unknown "unlowerable evolve domain"
  | _, _, none => return .unknown "unlowerable field"

/-- One benchmark: per right mode, in declaration order; the query count. -/
def checkProblem (s : Z3Session) (p : PProblem) : IO (List (String × ModeWF) × Nat) := do
  let vars := p.jointVars
  let n := vars.length
  let coord := fun (i : Fin n) => vars.getD i.val "v"
  let epsR := (parseRat p.R.epsilon).getD 1
  let cnt ← IO.mkRef 0
  let maxQ := 5000
  let maxSmt := 200000
  let deadline := (← IO.monoMsNow) + 60000
  let mut rows : List (String × ModeWF) := []
  for m in p.R.modes do
    let r ← try checkMode s cnt maxQ maxSmt deadline p vars n coord epsR m
      catch e => pure (ModeWF.unknown s!"budget ({e})")
    if (← IO.getEnv "RELCERT_DEBUG").isSome then
      match r with
      | .unknown why | .unknownRun why => IO.eprintln s!"    [wellformed] {p.name}.{m.name}: {why}"
      | _ => pure ()
    rows := rows ++ [(m.name, r)]
  pure (rows, ← cnt.get)

/-- The report line of one benchmark. -/
def reportLine (name : String) (rows : List (String × ModeWF)) (q : Nat) : String :=
  s!"[wellformed] {name}: " ++ String.intercalate " | " (rows.map (fun r => r.2.show r.1)) ++
    s!"  ({q} queries)"

/-- Tally: modes, ok (invariant), ok (exit), UNKNOWN (either clause undecided), BLOCKING
(clause (i) refuted). `ok` means both clauses shown. -/
structure Tally where
  benches : Nat := 0
  modes : Nat := 0
  inv : Nat := 0
  exit : Nat := 0
  unknown : Nat := 0
  unknownRun : Nat := 0
  blocking : Nat := 0
  unknownBenches : Nat := 0
  queries : Nat := 0

/-- The modes that are not `ok` (UNKNOWN or BLOCKING). -/
def Tally.failing (t : Tally) : Nat := t.unknown + t.blocking

def Tally.add (t : Tally) (rows : List (String × ModeWF)) (q : Nat) : Tally :=
  let inv := (rows.filter (fun r => match r.2 with | .invariant => true | _ => false)).length
  let ex := (rows.filter (fun r => match r.2 with | .exit _ => true | _ => false)).length
  let bl := (rows.filter (fun r => match r.2 with | .blocking _ => true | _ => false)).length
  let ur := (rows.filter (fun r => match r.2 with | .unknownRun _ => true | _ => false)).length
  let un := (rows.filter (fun r => !r.2.ok)).length - bl
  { benches := t.benches + 1, modes := t.modes + rows.length, inv := t.inv + inv,
    exit := t.exit + ex, unknown := t.unknown + un, unknownRun := t.unknownRun + ur,
    blocking := t.blocking + bl,
    unknownBenches := t.unknownBenches + (if un + bl > 0 then 1 else 0),
    queries := t.queries + q }

def Tally.summary (t : Tally) : String :=
  s!"[wellformed] summary: {t.benches} benchmark(s), {t.modes} right mode(s): " ++
    s!"{t.inv} ok (invariant), {t.exit} ok (exit), {t.unknown} UNKNOWN " ++
    s!"({t.unknownRun} of them nonblocking), {t.blocking} BLOCKING " ++
    s!"({t.unknownBenches} benchmark(s) with a mode not ok); both clauses checked; " ++
    s!"{t.queries} queries"

/-- `--wellformed <inputs>`: the check per benchmark on one warm session, then the summary.
Informational: the exit code is 0 unless a file does not parse or Z3 is missing. -/
def runWellformed (cfg : Z3Config) (paths : List String) : IO (Tally × Bool) := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3 session: {e}"; pure ({}, false)
  | .ok s =>
      let mut t : Tally := {}
      let mut okParse := true
      for path in paths do
        match ← readProblemStrict path with
        | .error e => IO.println s!"[wellformed] {path}: ERROR [parse: {e}]"; okParse := false
        | .ok p =>
            let (rows, q) ← checkProblem s p
            IO.println (reportLine p.name rows q)
            t := t.add rows q
      s.close
      IO.println t.summary
      pure (t, okParse)

/-- `RELCERT_WELLFORMED_STRICT=1`: an `UNKNOWN` or `BLOCKING` mode turns a CERTIFIED into a
DECLINED. -/
def strictOn : IO Bool := do
  pure ((← IO.getEnv "RELCERT_WELLFORMED_STRICT") == some "1")

/-- The certifier with the strict switch passed explicitly: `strict = false` is `certify`;
`strict = true` turns a CERTIFIED benchmark whose right model has a mode that is not `ok`
(`UNKNOWN`, or `BLOCKING`) into DECLINED (with a `[wellformed]` line on stderr). `--check-quick-v2` runs it with
`strict = true` (the recipe's strict mode, 2026-10-10). -/
def certifyWFWith (strict : Bool) (s : Z3Session) (p : PProblem) : IO Outcome := do
  let o ← certify s p
  if !strict then return o
  match o with
  | .certified =>
      let (rows, q) ← checkProblem s p
      IO.eprintln (reportLine p.name rows q)
      if rows.all (·.2.ok) then return .certified
      let why := if rows.any (fun r => match r.2 with | .blocking _ => true | _ => false)
        then "a BLOCKING right mode" else "an UNKNOWN right mode"
      IO.eprintln s!"  [wellformed] STRICT: {p.name} DECLINED ({why})"
      return .declined
  | _ => return o

/-- The certifier with the environment switch: identical to `certify` unless
`RELCERT_WELLFORMED_STRICT=1`. -/
def certifyWF (s : Z3Session) (p : PProblem) : IO Outcome := do
  certifyWFWith (← strictOn) s p

end RelCertifier.WellFormed
