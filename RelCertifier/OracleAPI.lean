/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The oracle API (TRUSTED harness layer, not verified)

The in-process entry point synthesis calls thousands of times. Three distinct,
never-conflated outcomes:

* `certified` — the verified cover closed via sound routes only (every segment on a
  covering path returned Z3 `unsat` on its `flowQueryStrict`). A real, sound YES.
* `declined`  — every query returned a definitive `sat`/`unsat`, and no cover closes.
  A real, sound NO (genuine incompleteness).
* `error msg` — ANY harness/solver/environment failure: unlowerable invariant, Z3
  spawn/crash/EOF, malformed SMT, `unknown`/timeout verdict. NEVER a verdict — the
  synthesis driver must treat this as retry/abort, never as signal.

Honesty invariant: an `error` can never masquerade as `declined`/`certified`. A Z3
`unknown` or process failure taints only routes it touches; if a covering route needed
it, the outcome is `error`, not `declined`. `certified` is only ever produced by actual
`unsat` verdicts, so it is trustworthy regardless of errors on unneeded routes.
-/
import RelCertifier.Run
import RelCertifier.CutCertDefs
import RelCertifier.Z3
import RelCertifier.Checker
import Std.Data.HashMap

namespace RelCertifier.Oracle

open RelCertifier RelCertifier.Parse RelCertifier.Run

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
partial def invComponents (vars : List String) (n : ℕ) : PForm → Option (List (ITerm n))
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

/-! ## Error-aware cover -/

/-- Per-segment status after checking all invariant components at a `(qL,qR,λ)`. -/
inductive Seg | pass | fail | incon
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Three-valued cover result. `incon` = a needed query was inconclusive (Z3 error /
`unknown` / unbuildable) — must surface as `error`, never `declined`. -/
inductive Cov3 | cov | nocov | incon
  deriving DecidableEq, Repr, BEq, Inhabited

/-! ## The checked-cut channel (differential cuts with re-derived justification)

A mode's flow-query domain may be narrowed by a CUT `S` — but only after the certifier
itself re-derives BOTH obligations, per atomic conjunct:

* **O1 (entry)**: the mode's guard implies the conjunct. Free for guard conjuncts (the
  default candidates).
* **O2 (invariance)**: the conjunct is flow-invariant along THIS mode's own field, checked
  by the same trusted routes as the main certificates — route B (`DI_strict` boundary:
  `dom ∧ g=0 ∧ ġ≥0` UNSAT), route A (`DI_nonstrict_domain` whole-domain: `dom ∧ ġ>0`
  UNSAT), or the CONTRACT-SHAPE route for the tangent case DI cannot see (`v ≤ κ` with
  field `k(c−v)`, `k ≥ 0`, `c ≤ κ` — rational comparison, no Z3; Lean backing
  `contract_stays`/`WellFormedFlowB_contract`, the explicit exponential witness).

Candidates supporting each other are handled by a greatest-fixpoint filter (check each
with ALL current candidates in the O2 domain; drop failures; repeat). Discipline: a cut
conjunct is USED only on a definitive pass — anything else silently drops it, so a wrong
or unprovable candidate costs completeness (DECLINE), never soundness. `evolve` itself is
NEVER modified: the model (and the Lean proof structure, which requires the uniform shared
envelope as every mode's domain) sees only `evolve`; cuts narrow the queries alone. -/

/-- One Z3 UNSAT probe (budget-counted); `true` ⟺ definitive `unsat`. -/
def probeUnsat {n : ℕ} (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (coord : Fin n → String) (q : IForm n) : IO Bool := do
  let script := q.toScript coord
  if script.length > maxSmt then pure false
  else do
    cnt.modify (· + 1)
    if (← cnt.get) > maxQ then throw (IO.userError "query budget exceeded")
    if (← IO.monoMsNow) > deadline then throw (IO.userError "time budget exceeded")
    match ← s.check script with
    | .ok .unsat => pure true
    | _ => pure false

/-- **The checked cut of a mode** (one side): the guard conjuncts that survive the O2
invariance filter, returned as the conjoined `IForm` to add to this mode's flow-query
domains, plus the kept atoms with their routes (the cut certificate's content).

O1 (entry) is syntactic — every candidate IS a guard conjunct. O2 is UNCONDITIONED:
each atom must be flow-invariant over the bare evolve domain on its own (per-atom
`DI_strict` / `DI_nonstrict_domain` / `contract_stays` — no mutual-barrier coupling),
so a single pass suffices and the Lean lift composes per atom. -/
def checkedCut (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String) (side : Side) (m : PMode) :
    IO (IForm n × List (PForm × CutRoute)) := do
  -- own-side field (the other side frozen, λ irrelevant for a one-sided Lie)
  let fOwn := dynOf vars n side m
  let zeroF : Fin n → ITerm n := fun _ => ITerm.rat 0
  let evolveI := (lowerF vars n side m.evolve).getD IForm.tt
  let mkCand (a : PForm) : Option (PForm × IForm n × ITerm n) := do
    let fI ← lowerF vars n side a
    let g  ← cutAtomG vars n side a
    pure (a, fI, g)
  let gCands := (cutAtoms m.guard).filterMap mkCand
  let dbg := (← IO.getEnv "RELCERT_DEBUG").isSome
  let mut kept : List (PForm × IForm n × CutRoute) := []
  for (a, fI, g) in gCands do
    if contractShapeOK m a then do
      if dbg then IO.eprintln s!"    [route] {m.name}: shape"
      kept := kept ++ [(a, fI, CutRoute.shape)]
    else if (atomVars a).all (frozenIn m) then do
      if dbg then IO.eprintln s!"    [route] {m.name}: frozen"
      kept := kept ++ [(a, fI, CutRoute.frozen)]
    else
      match fOwn with
      | none => pure ()
      | some f =>
        let gdot := match side with
          | Side.L => ilieDeriv g f zeroF (ITerm.rat 1)
          | _      => ilieDeriv g zeroF f (ITerm.rat 1)
        -- route B (DI_strict boundary), then route A (DI_nonstrict_domain whole-domain)
        let rB := IForm.and evolveI (IForm.and (IForm.cmp .eq g (.rat 0))
          (IForm.cmp .ge gdot (.rat 0)))
        if ← probeUnsat s cnt maxQ maxSmt deadline coord rB then do
          if dbg then IO.eprintln s!"    [route] {m.name}: DI-strict(B)"
          kept := kept ++ [(a, fI, CutRoute.diStrict)]
        else
          if ← probeUnsat s cnt maxQ maxSmt deadline coord
              (IForm.and evolveI (IForm.cmp .gt gdot (.rat 0))) then do
            if dbg then IO.eprintln s!"    [route] {m.name}: DI-nonstrict(A)"
            kept := kept ++ [(a, fI, CutRoute.diNonstrict)]
  let cut := kept.foldl (fun d c => IForm.and d c.2.1) IForm.tt
  pure (cut, kept.map (fun c => (c.1, c.2.2)))

/-- Check one segment `(qL=mL, qR=mR, λ)`: `pass` iff EVERY component's strict flow query
is Z3-`unsat`; `fail` iff some component is definitively `sat`; `incon` on any Z3
error/`unknown` or unbuildable query. -/
def checkSeg (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String)
    (comps : List (ITerm n)) (cutL cutR : IForm n) (mL mR : PMode) (lam : ℚ) : IO Seg := do
  -- Each component certifies via ANY of the 3 sound routes (A domain / B strict /
  -- C superlevel); the OTHER components restrict the domain (multi-barrier coupling).
  -- Segment status: fail if some component definitively fails all routes; else incon if
  -- some component is inconclusive; else pass (fail dominates incon).
  let mut sawFail := false
  let mut sawIncon := false
  for i in List.range comps.length do
    match comps[i]? with
    | none => pure ()
    | some g =>
      match segParts vars n g mL mR lam with
      | none => sawIncon := true                     -- couldn't build the query
      | some (baseDom, gdot) =>
          let others := (List.range comps.length).filterMap
            (fun j => if j == i then none else comps[j]?)
          -- CHECKED-CUT domains: narrow by the modes' re-derived cuts (O1/O2 above)
          let baseDom := IForm.and (IForm.and baseDom cutL) cutR
          let dom := others.foldl (fun d gj => IForm.and d (IForm.cmp .le gj (.rat 0))) baseDom
          let mut compPass := false
          let mut compIncon := false
          for q in routeQueries dom g gdot do
            if compPass then pure () else do
              cnt.modify (· + 1)
              if (← cnt.get) > maxQ then throw (IO.userError "query budget exceeded")
              if (← IO.monoMsNow) > deadline then throw (IO.userError "time budget exceeded")
              let script := q.toScript coord
              if script.length > maxSmt then compIncon := true
              else match ← s.check script with
                | .error _ => compIncon := true
                | .ok .unknown => compIncon := true
                | .ok .unsat => compPass := true
                | .ok .sat => pure ()
          if compPass then pure ()
          else if compIncon then sawIncon := true
          else do
            sawFail := true
            if (← IO.getEnv "RELCERT_DBGC").isSome then
              IO.eprintln s!"      FAIL comp#{i} @ {mL.name}->{mR.name} λ={lam}"
  return (if sawFail then Seg.fail else if sawIncon then Seg.incon else Seg.pass)

/-- **REPOSITION region-invariant check** over a supplied `region`. `true` ⟺ `rel_inv` holds
everywhere in `region`: `¬rel_inv ∧ region` UNSAT iff **for every component** `gᵢ`,
`UNSAT(region ∧ gᵢ > 0)`. STATIC — no ODE, no Lie, no `t²`. Used twice: with the **pre-j** region
`guardL ∧ guardR ∧ evolveL ∧ evolveR` (obligation 1) and the **post-j** region
`guardR ∧ evolveL ∧ evolveR` (obligation 2, no guardL — stronger).

Discipline (soundness): returns `true` ONLY when **every** component is a definitive Z3 `unsat`;
any `sat`/`unknown`/`error`/over-long → `false` (withhold reposition). A query bug can only
withhold reposition (over-decline), never wrongly offer it. -/
def regionUnsat {n : ℕ} (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (coord : Fin n → String) (comps : List (ITerm n)) (region : IForm n) : IO Bool := do
  let mut allUnsat := true
  for g in comps do
    if allUnsat then
      let q := IForm.and region (IForm.cmp .gt g (.rat 0))     -- region ∧ (gᵢ > 0) = ¬rel_inv part
      let script := q.toScript coord
      if script.length > maxSmt then allUnsat := false
      else do
        cnt.modify (· + 1)
        if (← cnt.get) > maxQ then throw (IO.userError "query budget exceeded")
        if (← IO.monoMsNow) > deadline then throw (IO.userError "time budget exceeded")
        match ← s.check script with
        | .ok .unsat => pure ()
        | _          => allUnsat := false
  pure allUnsat

/-- Build the (pre-j, post-j) reposition region `IForm`s for `(mL, mR)`:
* pre-j: `guardL(mL) ∧ guardR(mR) ∧ evolveL(mL) ∧ evolveR(mR)` (obligation 1, left in guard);
* post-j: `guardR(mR) ∧ evolveL(mL) ∧ evolveR(mR)` (obligation 2, NO guardL — false post-joint,
  left carried by `evolveL`). Both include the evolve domains. -/
def repoRegions (vars : List String) (n : ℕ) (cutL cutR : IForm n) (mL mR : PMode) :
    Option (IForm n × IForm n) := do
  let gL ← lowerF vars n Side.L mL.guard
  let gR ← lowerF vars n Side.R mR.guard
  let eL ← lowerF vars n Side.L mL.evolve
  let eR ← lowerF vars n Side.R mR.evolve
  -- CHECKED CUTS narrow the regions: every reachable σ-state satisfies the checked cuts
  -- (entry by O1, invariance by O2), so the region-invariant obligation may assume them.
  let ev := IForm.and (IForm.and (IForm.and eL eR) cutL) cutR
  pure (IForm.and (IForm.and gL gR) ev, IForm.and gR ev)

/-- **DYNAMIC REPOSITION check (certificate 3)** — the right-only FLOW cert via the **whole-domain**
`DI_nonstrict_domain` route (route A: `UNSAT(ġ > 0 ∧ domain)`), left FROZEN (`fL=0`, `ġ` via
`segPartsRO`). `withGuardL` selects σ: pre-j domain `guardL ∧ evolveL ∧ evolveR`, post-j
`evolveL ∧ evolveR`. **Whole-domain, NOT boundary** (`g=0 ∧ ġ≥0`) — that is the `t²` guard and the
reason the right-only flow segment is sound this time. Per component, the OTHER components restrict
the domain (multi-barrier). `true` iff every component's route-A query is definitive Z3 `unsat`;
any sat/unknown/error → `false` (withhold — drop-only-on-UNSAT). -/
def checkDynRepo (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String)
    (comps : List (ITerm n)) (cutL cutR : IForm n) (mL mR : PMode) (withGuardL : Bool) : IO Bool := do
  let gLform : IForm n := (if withGuardL then lowerF vars n Side.L mL.guard else some IForm.tt).getD IForm.tt
  let mut allUnsat := true
  for i in List.range comps.length do
    if allUnsat then
      match comps[i]? with
      | none => pure ()
      | some g =>
        match segPartsRO vars n g mL mR with        -- (evolveL∧evolveR, ġ) with fL=0, λ=1
        | none => allUnsat := false
        | some (baseDom, gdot) =>
            let baseDom := IForm.and (IForm.and baseDom cutL) cutR   -- checked-cut narrowing
            let others := (List.range comps.length).filterMap
              (fun j => if j == i then none else comps[j]?)
            let dom0 := others.foldl (fun d gj => IForm.and d (IForm.cmp .le gj (.rat 0))) baseDom
            let dom := IForm.and dom0 gLform            -- σ-matched: add guardL iff pre-j
            -- route A (DI_nonstrict_domain, WHOLE-DOMAIN): domain ∧ ġ>0 UNSAT
            let q := IForm.and dom (IForm.cmp .gt gdot (.rat 0))
            let script := q.toScript coord
            if script.length > maxSmt then allUnsat := false
            else do
              cnt.modify (· + 1)
              if (← cnt.get) > maxQ then throw (IO.userError "query budget exceeded")
              if (← IO.monoMsNow) > deadline then throw (IO.userError "time budget exceeded")
              match ← s.check script with
              | .ok .unsat => pure ()
              | _          => allUnsat := false
  pure allUnsat

/-- The multi-segment all-successors cover, three-valued, **memoized** on `(qR, f)` (the
budget `B` is a function of `f`, so the state is finite: `modes × fuel`). Without the memo
this is `(M+1)^fuel` pure recursion — the fuel can be huge when `δL` is tiny (large λ),
which hangs Lean (not Z3). `seg qR` is the precomputed segment status; `nocov` dominates
`incon` (a definitely-uncovered successor fails all-successors regardless of siblings). -/
partial def dfsCov3 (memo : IO.Ref (Std.HashMap (String × Nat) Cov3))
    (seg : String → Seg) (succ : String → List String) (deltaL : ℚ)
    (f : Nat) (qR : String) (B : ℚ) : IO Cov3 := do
  if B ≤ 0 then return .cov
  if f == 0 then return .nocov
  match (← memo.get)[(qR, f)]? with
  | some r => return r
  | none =>
    let r ← (match seg qR with
      | .fail => pure .nocov
      | .incon => pure .incon
      | .pass => do
          let B' := B - deltaL
          if B' ≤ 0 then pure .cov
          else do
            let mut rs : List Cov3 := []
            for q' in (qR :: succ qR) do
              rs := rs ++ [← dfsCov3 memo seg succ deltaL (f - 1) q' B']
            pure (if rs.any (· == Cov3.nocov) then .nocov
                  else if rs.any (· == Cov3.incon) then .incon else .cov))
    memo.modify (·.insert (qR, f) r)
    return r

/-- **Definition 4, executable.** From start mode `q` with segment budget `B` (`= ⌈εL/δL⌉`,
weight 1 per segment), return the modes the cover **visits**, or `none` if it fails:

* the mode must be certified (`seg q = pass` — Definition 4's *joint certified*);
* **base** (`B ≤ 1`): one segment closes the budget → visit `{q}` only, **do not** descend
  into successors (the terminating base case);
* **step** (`B ≥ 2`): every retained successor (`q` self-loop + declared `next`) must itself
  cover at `B-1`; the visited set is `q` with all their visited sets.

The result is exactly the modes the `SearchGraph`/`CoverCert` must range over — for a
single-sync (base) cover that is just `{q}`, so closed-leaf successors are never required to
certify. Mirrors the verified `decideCovered`'s base/step split. -/
partial def coverVisit (seg : String → Seg) (succ : String → List String)
    (B : Nat) (q : String) : Option (List String) :=
  if seg q != Seg.pass then none
  else if B ≤ 1 then some [q]
  else
    let kids := (q :: succ q).map (coverVisit seg succ (B - 1))
    if kids.all Option.isSome then some (q :: (kids.filterMap id).flatten) else none

/-- **Precise admissibility** (FIX 1, soundness-critical — *drop only on UNSAT*). Right start
mode `mR` is admissible for left mode `mL` iff some invariant-satisfying initial pair exists:
`guardL(mL) ∧ guardR(mR) ∧ ⋀ᵢ (gᵢ ≤ 0)` is SAT (`gᵢ ≤ 0` = the relational invariant `ϕ_rel`).
Returns `true` = **required** (admissible), `false` = **droppable** (definitively inadmissible).

Soundness discipline: we return `false` (drop `mR` from the required-start set) ONLY on a
definitive Z3 `unsat` — the same trusted oracle the flow certificates use. On `sat`, `unknown`,
`error`, an over-long script, or a query we cannot even build, we return `true` (keep it
required). Over-requiring is sound (it can only make the cover decline more); the *only* way a
required start could be wrongly dropped is a spurious `unsat`, so `unsat` is the sole drop
trigger. The query reuses the trusted `lowerF` encoding (same as the flow queries) with `guardL`
on the L-side and `guardR` on the R-side. -/
def admissible (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String)
    (comps : List (ITerm n)) (mL mR : PMode) : IO Bool := do
  match (do
      let gL ← lowerF vars n Side.L mL.guard
      let gR ← lowerF vars n Side.R mR.guard
      pure (comps.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0)))
              (IForm.and gL gR)) : Option (IForm n)) with
  | none => pure true                                 -- can't build ⟹ can't prove inadmissible ⟹ require
  | some q =>
      let script := q.toScript coord
      if script.length > maxSmt then pure true         -- can't check ⟹ require
      else do
        cnt.modify (· + 1)
        if (← cnt.get) > maxQ then throw (IO.userError "query budget exceeded")
        if (← IO.monoMsNow) > deadline then throw (IO.userError "time budget exceeded")
        match ← s.check script with
        | .ok .unsat => pure false                     -- DEFINITIVELY no initial pair ⟹ droppable
        | _          => pure true                      -- sat / unknown / error ⟹ keep required

/-- **Def-3 non-connection pruning** (FIX 3, soundness-critical — *prune only on UNSAT*). For a
declared right edge `mR → mSuc`, the successor is unreachable along `mR`'s right flow exactly when
the two `nonconn_sound` checks both hold: `sourceCheck = source ∧ {g>0}` UNSAT (entry strictly
safe, `g ≤ 0` at entry) and `barrierCheck = domain ∧ g=0 ∧ (Lie g sysR) ≥ 0` UNSAT (strict
flow-away on the threshold, `DI_strict`). Here `g` is the successor guard's safe-side term with
`guard = {g > 0}` (so `hlink` holds by construction), and `sysR`/`domain`/`source` are `mR`'s
right flow / evolution domain / entry region (`guard ∧ evolve`). `Lie g sysR` is the right-only
Lie `ilieDeriv g 0 fR 1` (`fL = 0`, `λ = 1`; `g` has no L-vars, so this is exactly `Σ ∂g/∂Rᵢ·fRᵢ`).

Returns `true` = **prune** (drop the edge from `retainedSucc`), `false` = **keep required**. We
prune ONLY when BOTH checks are definitive `unsat` (`| .ok .unsat, .ok .unsat => true`); every
other pair (`sat`/`unknown`/`error`), an over-long script, or an unbuildable / non-strict-scalar
guard keeps the edge (`| _, _ => false`). A query bug can then only fail to prune (over-decline),
never wrongly prune (false-certify). The drop's soundness is the proven `nonconn_sound`; here we
supply its two UNSAT hypotheses. Only STRICT scalar successor guards (`a > b` / `a < b`) are
prunable — a CLOSED guard (`≥`/`≤`) has a boundary the strict barrier cannot exclude, so it is
kept (scope, not unsoundness). -/
def nonConnPrune (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String) (cutR : IForm n)
    (mR mSuc : PMode) : IO Bool := do
  -- safe-side term `g` with successor `guard = {g > 0}`; STRICT scalar comparisons only.
  let gOpt : Option (ITerm n) :=
    match mSuc.guard with
    | PForm.cmp ">" a b =>
        (lowerE vars n Side.R a).bind fun ea =>
          (lowerE vars n Side.R b).map fun eb => ITerm.bin .sub ea eb    -- {a>b} = {a−b>0}
    | PForm.cmp "<" a b =>
        (lowerE vars n Side.R a).bind fun ea =>
          (lowerE vars n Side.R b).map fun eb => ITerm.bin .sub eb ea    -- {a<b} = {b−a>0}
    | _ => none                                                          -- closed / non-atomic ⟹ keep
  match gOpt with
  | none => pure false
  | some g =>
    match (do
        let domR0 ← lowerF vars n Side.R mR.evolve
        let domR := IForm.and domR0 cutR                             -- checked-cut narrowing
        let srcR0 ← lowerF vars n Side.R (PForm.and mR.guard mR.evolve)
        let srcR := IForm.and srcR0 cutR
        let fR   ← dynOf vars n Side.R mR
        let lie  := ilieDeriv g (fun _ => ITerm.rat 0) fR (ITerm.rat 1)  -- right-only Lie
        let gPos := IForm.cmp .gt g (ITerm.rat 0)
        pure (IForm.and srcR gPos,                                       -- sourceCheck = source ∧ {g>0}
              IForm.and domR (IForm.and (IForm.cmp .eq g (ITerm.rat 0))
                (IForm.cmp .ge lie (ITerm.rat 0)))) )                    -- barrierCheck = dom ∧ g=0 ∧ ġ≥0
      with
    | none => pure false
    | some (srcCheck, barCheck) =>
      let s1 := srcCheck.toScript coord
      let s2 := barCheck.toScript coord
      if s1.length > maxSmt || s2.length > maxSmt then pure false        -- can't check ⟹ keep
      else do
        cnt.modify (· + 2)
        if (← cnt.get) > maxQ then throw (IO.userError "query budget exceeded")
        if (← IO.monoMsNow) > deadline then throw (IO.userError "time budget exceeded")
        let r1 ← s.check s1
        let r2 ← s.check s2
        match r1, r2 with
        | .ok .unsat, .ok .unsat => pure true    -- BOTH UNSAT ⟹ Def-3 non-connection ⟹ PRUNE
        | _, _                   => pure false   -- anything else ⟹ keep the edge required

/-- Cover a single left mode: `cov` if some (start,λ) closes definitively; `incon` if none
close but a route was inconclusive; `nocov` if all routes are definitive fails. -/
def coverMode (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat) (p : PProblem)
    (vars : List String) (n : ℕ)
    (coord : Fin n → String) (comps : List (ITerm n))
    (prunedOf : String → String → Bool)
    (cutL : IForm n) (cutOfR : String → IForm n)
    (epsL epsR lmin lmax : ℚ) (mL : PMode) : IO Cov3 := do
  let mut sawIncon := false
  -- FIX 1 (precise admissibility): the admissible initial right modes for `mL` — those with an
  -- invariant-satisfying initial pair. λ-independent (guards + `ϕ_rel` only), so computed ONCE.
  -- `.cov` will require every admissible start to cover (the ∀ over initial pairs); an
  -- inadmissible mode (no `guardL ∧ guardR ∧ ϕ_rel` pair, proven by Z3 `unsat`) is dropped.
  let mut admMods : List PMode := []
  for mR in p.R.modes do
    if ← admissible s cnt maxQ maxSmt deadline vars n coord comps mL mR then
      admMods := admMods ++ [mR]
  -- REPOSITION: BOTH source-setting region-invariants per right mode (left `mL` frozen).
  -- λ-independent (guards + invariant only), computed ONCE. `repoPreOK` uses the pre-j region
  -- (with guardL), `repoPostOK` the stronger post-j region (without guardL). σ selects between
  -- them in the cover. For watertank `(Mid_L, High_R)`: pre-j PASSES (enables the initial-pair
  -- reposition `High_R → Mid_R`).
  let mut repoMap : List (String × Bool × Bool) := []   -- (name, preOK, postOK)
  for mR in p.R.modes do
    let (pre, post) ← (match repoRegions vars n cutL (cutOfR mR.name) mL mR with
      | none => pure (false, false)                       -- unbuildable ⟹ no reposition
      | some (rPre, rPost) => do
          let pre  ← regionUnsat s cnt maxQ maxSmt deadline coord comps rPre
          let post ← regionUnsat s cnt maxQ maxSmt deadline coord comps rPost
          pure (pre, post))
    repoMap := repoMap ++ [(mR.name, pre, post)]
  let repoPreOK  := fun (nm : String) => (repoMap.find? (·.1 == nm)).map (·.2.1) |>.getD false
  let repoPostOK := fun (nm : String) => (repoMap.find? (·.1 == nm)).map (·.2.2) |>.getD false
  -- DYNAMIC reposition (certificate 3): right-only whole-domain flow cert (route A), σ-matched.
  -- λ-independent (fL=0, λ=1; sign λ-invariant), computed ONCE. For the rover cross-terrain hop,
  -- `ġ_s=−v_R≤0` and `ġ_v` on the terrain's v-evolve-cap ⟹ route-A UNSAT ⟹ the advancing reposition.
  let mut dynMap : List (String × Bool × Bool) := []
  for mR in p.R.modes do
    let pre  ← checkDynRepo s cnt maxQ maxSmt deadline vars n coord comps cutL (cutOfR mR.name) mL mR true
    let post ← checkDynRepo s cnt maxQ maxSmt deadline vars n coord comps cutL (cutOfR mR.name) mL mR false
    dynMap := dynMap ++ [(mR.name, pre, post)]
  let repoDynPreOK  := fun (nm : String) => (dynMap.find? (·.1 == nm)).map (·.2.1) |>.getD false
  let repoDynPostOK := fun (nm : String) => (dynMap.find? (·.1 == nm)).map (·.2.2) |>.getD false
  if (← IO.getEnv "RELCERT_DEBUG").isSome then
    let preL := repoMap.filterMap (fun p => if p.2.1 then some p.1 else none)
    let postL := repoMap.filterMap (fun p => if p.2.2 then some p.1 else none)
    let dpreL := dynMap.filterMap (fun p => if p.2.1 then some p.1 else none)
    IO.eprintln s!"  [repo-pre] {mL.name}_L: {preL} [repo-post]: {postL} [repo-dyn-pre]: {dpreL}"
  for lam in lambdaCandidates lmin lmax epsL epsR do
    let deltaL := if lam == 0 then epsR else epsR / lam
    if deltaL ≤ 0 then continue
    -- precompute per-right-mode segment status at this λ
    let mut segMap : List (String × Seg) := []
    for mR in p.R.modes do
      segMap := segMap ++ [(mR.name,
        ← checkSeg s cnt maxQ maxSmt deadline vars n coord comps cutL (cutOfR mR.name) mL mR lam)]
    let seg := fun q => (segMap.find? (·.1 == q)).map (·.2) |>.getD Seg.incon
    if (← IO.getEnv "RELCERT_DEBUG").isSome then
      IO.eprintln (s!"  [{mL.name}_L λ={lam} #comps={comps.length}] " ++
        String.intercalate " " (segMap.map (fun p => s!"{p.1}={repr p.2}")))
    -- segment budget B = ⌈εL/δL⌉ (weight 1 per segment), capped; single-sync ⟺ B ≤ 1
    let bBudget := min (epsL / deltaL).ceil.toNat 256
    -- VERIFIED structural gate (Step 4 + Def-4 fidelity): CERTIFIED flows through the verified
    -- computable `decideCovered`, not the untrusted `dfsCov3`. For each start, `coverVisit`
    -- runs Definition 4 (certified-aware) to find the visited mode set; we build `decideCovered`'s
    -- graph over EXACTLY that set (every visited mode certifies ⟹ `CoverCert` holds, and — by
    -- Def 4 — a `step` node's successors are all visited, so no real edge is dropped). A single-
    -- sync cover hits the `base` case (`B ≤ 1`), visiting only the start, so its non-certifying
    -- closed-leaf successors are correctly irrelevant. `decideCovered = true` ⟹ `Covered` ⟹
    -- (via `check_sound`) the ∀∃-throughout invariant. Its `false` ⟹ decline (never false CERTIFIED).
    -- FIX 1 (soundness): the initial right mode is NOT a free ∃-pick. Def 4 / the ∀∃ property
    -- quantify over EVERY admissible initial pair `(mL, mR0)`; the right's start mode is
    -- determined by `s_R`. So `.cov` requires that EVERY admissible initial mode (`admMods`,
    -- computed once above via `admissible`) covers — not that some start does.
    -- FIX 2 (soundness): run the VERIFIED `decideCovered` on the REAL declared-successor graph,
    -- NOT the `coverVisit` visited set (which the checker would merely rubber-stamp). Nodes =
    -- the certified (`seg = pass`) right modes; EDGES = ALL declared edges. An edge whose target
    -- is UNCERTIFIED points to an out-of-range sentinel index `k`, so `decideCovered`'s
    -- ∀-over-`retainedSucc` hits `modeAt = none` there and fails — an uncertified declared
    -- successor cannot be silently stripped from the ∀. Weight 1 / budget `⌈εL/δL⌉` is the
    -- faithful ℕ-discretization of `(B = εL, w = εR/λ)`: base fires at `B ≤ 1 ⟺ εL ≤ εR/λ`
    -- (one segment closes the residence), matching the paper's real-valued base condition.
    -- REPOSITION: NODES = modes joint-certified OR reposition-certified (pre-j OR post-j). Each
    -- node carries `jointOK`, `repoPreOK`, `repoPostOK`; `decideCovered` offers base/joint-step
    -- where `jointOK`, and the zero-budget reposition step σ-matched (pre-j → `repoPreOK`, post-j
    -- → `repoPostOK`). `region`/`regionPost` are structural placeholders (`decideCovered` is
    -- structural; the real `repoPresPre/Post` are the Z3-established region-invariants).
    -- a mode is a node iff joint-certified OR reposition-certified by ANY of the 3 kinds
    -- (static pre/post OR dynamic pre/post).
    let repoOK := fun nm => repoPreOK nm || repoPostOK nm || repoDynPreOK nm || repoDynPostOK nm
    let nodeMods := p.R.modes.filter (fun m => seg m.name == Seg.pass || repoOK m.name)
    let kSentinel := nodeMods.length
    let idxOf := fun (nm : String) => (nodeMods.findIdx? (·.name == nm)).getD kSentinel
    let cgReal : SearchGraph (Var n) :=
      { modes := nodeMods.map (fun m =>
          { sys := [], dom := .tt, weight := 1,
            jointOK := seg m.name == Seg.pass,
            region := .tt, repoPreOK := repoPreOK m.name,
            regionPost := .tt, repoPostOK := repoPostOK m.name,
            dynSys := [], dynDomPre := .tt, dynDomPost := .tt,
            repoDynPreOK := repoDynPreOK m.name, repoDynPostOK := repoDynPostOK m.name })
        edges := nodeMods.flatMap (fun m => (succOf p m.name).map (fun tgt =>
          -- FIX 3: `pruned` set by the Def-3 non-connection certificate (`prunedOf`).
          { src := idxOf m.name, tgt := idxOf tgt, guard := .tt, pruned := prunedOf m.name tgt })) }
    -- fuel bounds `decideCovered`'s depth: joint steps decrease budget (≤ `bBudget`), reposition
    -- steps keep budget but recurse only through repo-OK nodes' non-self exits. A budget-decrement
    -- can be interleaved with a zero-budget reposition through EACH node (Approach→Return→Approach
    -- alternation at high λ ⟹ high `bBudget`), so the worst-case depth is `bBudget·(nodeMods+1)`, not
    -- `bBudget + nodeMods`. Fuel only bounds the checker's search depth — larger is always sound
    -- (`decideCovered_sound` is fuel-generic); too-small merely over-declines.
    let fuel := bBudget * (nodeMods.length + 1) + 1
    let startCovers := fun (mR : PMode) =>
      -- a start is usable iff it is a node; the verified checker decides base / joint-step /
      -- reposition-step on the real graph. Initial source setting σ = **preJ** (no joint yet).
      (seg mR.name == Seg.pass || repoOK mR.name) &&
        decideCovered cgReal fuel ⟨idxOf mR.name, bBudget, SrcSetting.preJ⟩
    -- `.cov` for this λ iff every admissible initial mode covers. Empty `admMods` ⟹ do NOT
    -- certify (safe: a possibly-buggy all-drop cannot vacuously certify; over-decline instead).
    if !admMods.isEmpty && admMods.all startCovers then return .cov
    if admMods.any (fun mR => seg mR.name == Seg.incon) then sawIncon := true
  return (if sawIncon then .incon else .nocov)

/-- Core cover, parameterized by a query counter/budget (`throw`s on overrun). -/
def certifyCore (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat) (p : PProblem) : IO Outcome := do
  let vars := p.L.stateVars
  let n := vars.length
  let coord := fun (i : Fin n) => vars.getD i.val "v"
  let epsL := (parseRat p.L.epsilon).getD 1
  let epsR := (parseRat p.R.epsilon).getD 1
  let lmin := (parseRat p.lambdaMin).getD 1
  let lmax := (parseRat p.lambdaMax).getD 1
  -- CHECKED CUTS (λ- and pair-independent: each mode's own guard + own field),
  -- computed ONCE per mode per side. Used ONLY to narrow query domains (never the model).
  -- RELCERT_NO_CUT=1 disables the checked-cut channel entirely (ablation switch:
  -- queries fall back to the bare evolution domains).
  let noCut := (← IO.getEnv "RELCERT_NO_CUT").isSome
  let mut cutMapL : List (String × IForm n) := []
  for mM in p.L.modes do
    let (c, kept) ← if noCut then pure (IForm.tt, [])
      else checkedCut s cnt maxQ maxSmt deadline vars n coord Side.L mM
    if (← IO.getEnv "RELCERT_DEBUG").isSome then
      IO.eprintln s!"  [cut] L.{mM.name}: {kept.length} conjunct(s)"
    cutMapL := cutMapL ++ [(mM.name, c)]
  let mut cutMapR : List (String × IForm n) := []
  for mM in p.R.modes do
    let (c, kept) ← if noCut then pure (IForm.tt, [])
      else checkedCut s cnt maxQ maxSmt deadline vars n coord Side.R mM
    if (← IO.getEnv "RELCERT_DEBUG").isSome then
      IO.eprintln s!"  [cut] R.{mM.name}: {kept.length} conjunct(s)"
    cutMapR := cutMapR ++ [(mM.name, c)]
  let cutOfL := fun (nm : String) => (cutMapL.find? (·.1 == nm)).map (·.2) |>.getD IForm.tt
  let cutOfR := fun (nm : String) => (cutMapR.find? (·.1 == nm)).map (·.2) |>.getD IForm.tt
  -- FIX 3: Def-3 non-connection pruning. mL- AND λ-independent (right flow + right guards only),
  -- so computed ONCE for the whole problem. Edge `mR → tgt` pruned iff BOTH nonconn checks are
  -- definitive Z3 UNSAT (`nonConnPrune`); any other verdict keeps it. Drop-only-on-UNSAT ⟹ sound.
  let mut prunedPairs : List (String × String) := []
  for mR in p.R.modes do
    for tgt in mR.next do
      match p.R.modes.find? (·.name == tgt) with
      | none => pure ()
      | some mSuc =>
          if ← nonConnPrune s cnt maxQ maxSmt deadline vars n coord (cutOfR mR.name) mR mSuc then
            prunedPairs := prunedPairs ++ [(mR.name, tgt)]
  if (← IO.getEnv "RELCERT_DEBUG").isSome then
    IO.eprintln s!"  [prune] {p.name}: {prunedPairs.map (fun e => s!"{e.1}->{e.2}")}"
  let prunedOf := fun (src tgt : String) => prunedPairs.contains (src, tgt)
  let mut sawIncon := false
  for mL in p.L.modes do
    -- invariant for this left mode (key = mode name, else first)
    -- strict: every left mode must carry its own invariant row (the old head-of-list
    -- fallback silently certified the FIRST row's formula for unmatched modes — an
    -- accept-and-weaken route at key resolution)
    let invF := (p.invariants.find? (·.1 == mL.name)).map Prod.snd
    match invF with
    | none => return .error s!"no invariant for left mode {mL.name}"
    | some f =>
        match invComponents vars n f with
        | none => return .error s!"unlowerable invariant for mode {mL.name}"
        | some comps =>
            match ← coverMode s cnt maxQ maxSmt deadline p vars n coord comps prunedOf
                (cutOfL mL.name) cutOfR epsL epsR lmin lmax mL with
            | .cov => pure ()
            | .incon => sawIncon := true
            | .nocov => return .declined   -- definitive uncovered ⟹ sound DECLINE
  if sawIncon then return .error "inconclusive Z3 verdict on a candidate route"
  else return .certified

/-- **In-process oracle entry.** Certify problem `p` on a warm session `s`. No shelling.
A deterministic query budget (`RELCERT_MAX_QUERIES`, default 1500) bounds every call: a
candidate whose exhaustive search exceeds it ⟹ `error "query budget exceeded"` (never a
verdict, never a hang) — the same input always hits the same count. -/
def certify (s : Z3Session) (p : PProblem) : IO Outcome := do
  let cnt ← IO.mkRef 0
  let maxQ := (← IO.getEnv "RELCERT_MAX_QUERIES").bind String.toNat? |>.getD 5000
  let budgetMs := (← IO.getEnv "RELCERT_TIME_BUDGET_MS").bind String.toNat? |>.getD 40000
  let maxSmt := (← IO.getEnv "RELCERT_MAX_SMT").bind String.toNat? |>.getD 200000
  let deadline := (← IO.monoMsNow) + budgetMs
  try certifyCore s cnt maxQ maxSmt deadline p
  catch e => return .error s!"budget exceeded ({e})"

/-- File entry: parse + certify on a fresh warm session (for the CLI / batch). Parse
failure ⟹ `error` (unparsed), never a verdict. -/
def certifyFile (cfg : Z3Config) (path : String) : IO Outcome := do
  let txt? ← try some <$> IO.FS.readFile path catch _ => pure none
  match txt? with
  | none => return .error s!"cannot read {path}"
  | some txt =>
      match parseProblemE txt with
      | .error e => return .error s!"parse: {e}"
      | .ok p =>
          match ← Z3Session.start cfg with
          | .error e => return .error e
          | .ok s => let r ← certify s p; s.close; return r

end RelCertifier.Oracle
