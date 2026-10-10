/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The Assumption 1 check of the right model (TRUSTED harness layer, informational)

The paper's Assumption 1 (Well-Formedness): from every state satisfying a source-mode guard,
an evolution spanning the control interval `ε_r` exists, and every evolution of duration at
most `ε_r` ends in a state satisfying the guard of at least one declared successor mode.
The kernel states and proves (or refutes) it per benchmark (`WellFormedR`,
`InstancesV2/WellFormedBattery.lean`). This file is the tool's CHEAP, SUFFICIENT check of
its successor-completeness half (clause (ii)); it is reported per right mode, counted, and
changes no verdict unless `RELCERT_WELLFORMED_STRICT=1`.

Per right mode `q` (guard `G_q`, a conjunction of comparison atoms `gₐ ≤ 0` / `gₐ < 0`,
lowered on the right; field `f_q`; evolve domain `D_q`):

1. **Stratified invariance of the guard atoms** (the cut channel's O2 routes, run on `q`'s
   own flow, the left held still): round by round, an atom is kept by the contraction-shape
   route (`contractShapeOK`, `contractShapeOKX`: `x ≤ κ` / `x ≥ κ` under `x' = k (c − x)`, the set
   point on the safe side; no Z3), the frozen route, route B
   `UNSAT(D_q ∧ I ∧ gₐ = 0 ∧ ġₐ ≥ 0)` or route A `UNSAT(D_q ∧ I ∧ ġₐ > 0)`, `I` the atoms
   kept in EARLIER rounds (sequential differential cuts, never mutual). Every route keeps
   `gₐ ≤ 0` and `gₐ < 0` along every run inside `D_q ∧ I`. If every atom is kept and
   `q` declares its self-loop: **`ok (invariant)`**: every run from `G_q` stays in `G_q`.
2. **Exit within one interval.** Otherwise, for each atom `a` not kept, a rate bound
   `Lₐ ≥ 0` with `UNSAT(D_q ∧ I ∧ ġₐ > Lₐ)` (bisection on the grid `k/100`, `k ≤ 10⁶`). A run
   of duration `t ≤ ε_r` from `G_q` stays in `D_q ∧ I` and ends with `gₐ ≤ gₐ(0) + Lₐ t ≤
   Lₐ ε_r` (strict when the atom is strict). One coverage query
   `UNSAT(D_q ∧ I ∧ ⋀ₐ gₐ ≤ Lₐ ε_r ∧ ⋀_{s ∈ next(q)} ¬G_s)` then shows that every such end
   state satisfies a declared successor's guard: **`ok (exit→S)`**, `S` the successors the
   query needs (greedily minimized, one query per dropped successor).
3. Anything else (a route not `unsat`, an unlowerable guard or field, a disjunctive guard,
   no rate bound): **`UNKNOWN`**. Sufficient, not necessary.

Not checked here: clause (i), that a run of the full interval exists (the kernel's
`WellFormedR` covers it; e.g. the satellites' momentum band).

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

/-- The per-mode result. -/
inductive ModeWF
  | invariant
  | exit (succ : List String)
  | unknown (why : String)

def ModeWF.ok : ModeWF → Bool
  | .unknown _ => false
  | _ => true

def ModeWF.show (q : String) : ModeWF → String
  | .invariant => s!"{q} ok (invariant)"
  | .exit ss => s!"{q} ok (exit→{String.intercalate "," ss})"
  | .unknown _ => s!"{q} UNKNOWN"

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

/-- **The check of one right mode** (see the module docstring). -/
def checkMode (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (p : PProblem) (vars : List String) (n : ℕ) (coord : Fin n → String) (epsR : ℚ)
    (m : PMode) : IO ModeWF := do
  match guardAtoms vars n m.guard, lowerF vars n Side.R m.evolve, dynOf vars n Side.R m with
  | some atoms, some dom, some f =>
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
      let selfLoop := m.next.contains m.name
      if kept.length == atoms.length && selfLoop then return .invariant
      -- 2. exit within one interval
      let inv := kept.foldl (fun d i =>
        match atoms[i]? with
        | some a => IForm.and d a.toF
        | none => d) dom
      let mut reach := inv
      for i in List.range atoms.length do
        if kept.contains i then pure () else
        match atoms[i]? with
        | none => pure ()
        | some a =>
            match ← rateBound s cnt maxQ maxSmt deadline coord inv (gdotOf a) with
            | none => return .unknown s!"no rate bound for {ppForm a.form}"
            | some L =>
                reach := IForm.and reach
                  (IForm.cmp (if a.strict then .lt else .le) a.g (.rat (L * epsR)))
      -- the declared successors and their lowered guards
      let mut succs : List (String × IForm n) := []
      for nm in m.next do
        match p.R.modes.find? (·.name == nm) with
        | none => return .unknown s!"undeclared successor {nm}"
        | some ms =>
            match lowerF vars n Side.R ms.guard with
            | none => return .unknown s!"unlowerable guard of {nm}"
            | some gs => succs := succs ++ [(nm, gs)]
      let covers (ss : List (String × IForm n)) : IO Bool :=
        probeUnsat s cnt maxQ maxSmt deadline coord
          (ss.foldl (fun d sg => IForm.and d (IForm.neg sg.2)) reach)
      if !(← covers succs) then return .unknown "the reach box leaves every successor guard"
      -- greedy minimization: drop a successor when the rest still cover (the other
      -- successors first, the self-loop last)
      let mut need := succs
      for sg in (succs.filter (·.1 != m.name)) ++ (succs.filter (·.1 == m.name)) do
        let rest := need.filter (·.1 != sg.1)
        if ← covers rest then need := rest
      let others := (need.map (·.1)).filter (· != m.name)
      if others.isEmpty then return .invariant   -- covered by its own guard (self-loop)
      return .exit others
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
    rows := rows ++ [(m.name, r)]
  pure (rows, ← cnt.get)

/-- The report line of one benchmark. -/
def reportLine (name : String) (rows : List (String × ModeWF)) (q : Nat) : String :=
  s!"[wellformed] {name}: " ++ String.intercalate " | " (rows.map (fun r => r.2.show r.1)) ++
    s!"  ({q} queries)"

/-- Tally: modes, ok (invariant), ok (exit), UNKNOWN. -/
structure Tally where
  benches : Nat := 0
  modes : Nat := 0
  inv : Nat := 0
  exit : Nat := 0
  unknown : Nat := 0
  unknownBenches : Nat := 0
  queries : Nat := 0

def Tally.add (t : Tally) (rows : List (String × ModeWF)) (q : Nat) : Tally :=
  let inv := (rows.filter (fun r => match r.2 with | .invariant => true | _ => false)).length
  let ex := (rows.filter (fun r => match r.2 with | .exit _ => true | _ => false)).length
  let un := (rows.filter (fun r => !r.2.ok)).length
  { benches := t.benches + 1, modes := t.modes + rows.length, inv := t.inv + inv,
    exit := t.exit + ex, unknown := t.unknown + un,
    unknownBenches := t.unknownBenches + (if un > 0 then 1 else 0),
    queries := t.queries + q }

def Tally.summary (t : Tally) : String :=
  s!"[wellformed] summary: {t.benches} benchmark(s), {t.modes} right mode(s): " ++
    s!"{t.inv} ok (invariant), {t.exit} ok (exit), {t.unknown} UNKNOWN " ++
    s!"({t.unknownBenches} benchmark(s) with an UNKNOWN mode); {t.queries} queries"

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

/-- `RELCERT_WELLFORMED_STRICT=1`: an `UNKNOWN` mode turns a CERTIFIED into a DECLINED. -/
def strictOn : IO Bool := do
  pure ((← IO.getEnv "RELCERT_WELLFORMED_STRICT") == some "1")

/-- The certifier with the strict switch: identical to `certify` unless
`RELCERT_WELLFORMED_STRICT=1`, in which case a CERTIFIED benchmark whose right model has an
`UNKNOWN` mode is DECLINED (with a `[wellformed]` line on stderr). -/
def certifyWF (s : Z3Session) (p : PProblem) : IO Outcome := do
  let o ← certify s p
  if !(← strictOn) then return o
  match o with
  | .certified =>
      let (rows, q) ← checkProblem s p
      IO.eprintln (reportLine p.name rows q)
      if rows.all (·.2.ok) then return .certified
      IO.eprintln s!"  [wellformed] STRICT: {p.name} DECLINED (an UNKNOWN right mode)"
      return .declined
  | _ => return o

end RelCertifier.WellFormed
