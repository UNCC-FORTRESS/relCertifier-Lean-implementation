/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The certifier (TRUSTED harness layer, not verified)

`certify` decides one benchmark on a warm Z3 session (`relcert <input.txt>`). The search
is untrusted: what soundness rests on is the verdicts it records (Z3 `unsat`, consumed
through `z3_unsat_sound`) and the cover decision, which is made by the verified checker
`decideCovered` and replayed in the kernel from the emitted flags.

* **Checked cuts** (`checkedCut`; `checkedCutX` under `RELCERT_IMPLIED_CUT=1`, the widened
  channel of `Checker/EvolStrengtheningX.lean`): per mode, atoms implied by its guard (O1)
  and kept by its own flow (O2); they only narrow query domains.
* **Non-connection pruning** (`nonConnPrune`): a declared right edge is dropped when both
  queries of `Trusted/NonConnQuery.lean` are `unsat`.
* **Per left mode** (`coverMode`): the admissible right starts (`admissible`); per right
  mode the dynamic right-only reposition (`checkDynRepo`: the right flows under its own
  field with the left frozen, the invariant preserved on the whole domain, before and after
  the left jump); per λ on the grid and per right mode the joint segment (`checkSeg`: every
  invariant component certified by route A, B or C over the cut-narrowed, stratified
  domain). The cover closes when `decideCovered` accepts from every admissible start.
  One stretch per left mode when one closes the cover; otherwise the per-pairing fallback
  (each right mode at the smallest stretch its joint segment passed, every joint segment
  cut to the common left span `εR / max λ`, same integer budget; `RELCERT_NO_PAIR_STRETCH=1`
  disables it). The emitted cover records the stretch of every pairing
  (`PairStrataE.lamN / lamD`), pinned to the verdict packs by `VerdictsV2/LamPinV2.lean`.
  These are the only two step kinds: joint segments and dynamic right-only reposition.
  There is no zero-duration right switch.

Budgets, per benchmark (env-overridable): query budget `RELCERT_MAX_QUERIES` = 20000,
wall-clock budget `RELCERT_TIME_BUDGET_MS` = 300000 ms; per query (`Trusted/Z3.lean`):
timeout 10 s, rlimit 64 000 000.

Three distinct, never-conflated outcomes:

* `certified` — the verified cover closed via sound routes only (every component of every
  segment on a covering path returned Z3 `unsat` on one of its route queries). A real,
  sound YES.
* `declined`  — every query returned a definitive `sat`/`unsat`, and no cover closes.
  A real, sound NO (genuine incompleteness).
* `error msg` — ANY harness/solver/environment failure: unlowerable invariant, Z3
  spawn/crash/EOF, malformed SMT, `unknown`/timeout verdict, budget exceeded. NEVER a
  verdict.

Honesty invariant: an `error` can never masquerade as `declined`/`certified`. A Z3
`unknown` or process failure taints only routes it touches; if a covering route needed
it, the outcome is `error`, not `declined`. `certified` is only ever produced by actual
`unsat` verdicts, so it is trustworthy regardless of errors on unneeded routes.
-/
import RelCertifier.Trusted.Run
import RelCertifier.Trusted.InvComponents
import RelCertifier.Trusted.InvStrictFlags
import RelCertifier.Trusted.NonConnQuery
import RelCertifier.Trusted.JointVars
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.Trusted.Z3
import RelCertifier.Checker.Checker
import RelCertifier.Checker.CoverEmit
import RelCertifier.Trusted.ProgressEmit
import RelCertifier.Trusted.PrelandEmit
import RelCertifier.Trusted.ChoiceEmit
import Std.Data.HashMap

namespace RelCertifier.Oracle

open RelCertifier RelCertifier.Parse RelCertifier.Run

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

/-- **The extended cut channel switch** (L1 implied-contraction atoms and L2 closures,
`Checker/EvolStrengtheningX.lean`). Default OFF, so that a run without it searches with
the guard-conjunct certificate alone (the certificate the 19 carried-over legacy instances
quote). `RELCERT_IMPLIED_CUT=1` turns the channel on (every suite_v2 run,
`scripts/suite_v2_matrix.py`; 12 suite_v2 benchmarks DECLINE without it);
`RELCERT_NO_IMPLIED_CUT=1` overrides to
off (the matrix's counter-run: legacy cuts only, so a benchmark that then DECLINES is
load-bearing on the implied atoms — the "M6+" cell). -/
def impliedCutsOn : IO Bool := do
  if (← IO.getEnv "RELCERT_NO_IMPLIED_CUT").isSome then pure false
  else pure (← IO.getEnv "RELCERT_IMPLIED_CUT").isSome

/-- **The L7 linear-form switch** (`Checker/EvolStrengtheningX.lean`, the domain
audit): the linear-form and derived-bound candidates run whenever the extended channel
is on, unless `RELCERT_NO_LINEAR_CUT=1` overrides them off (the counter-run of the
`suite_v2` matrix: a benchmark that then DECLINES is load-bearing on the linear-form
chain — the "M6L" cell). -/
def linearCutsOn : IO Bool := do
  if (← IO.getEnv "RELCERT_NO_LINEAR_CUT").isSome then pure false
  else impliedCutsOn

/-- **The extended checked cut of a mode** (`RELCERT_IMPLIED_CUT=1` path): the legacy
guard-conjunct atoms (computed by `checkedCut`, unchanged, tagged `guardConj` /
`membership`), then the L2 closures of the strict guard conjuncts (O1 by weakening),
then the L1 implied-contraction atoms `v ≤ c` / `v ≥ c` of every contraction field
(O1 by rational comparison against a threshold guard conjunct, else by one counted Z3
query `UNSAT(guard ∧ ¬atom)`). O2 for these atoms is as for any closed atom: the
contract-shape route over `contractEq`'s grammar (no Z3), the frozen route, then the DI
routes B and A — each atom over the bare evolve domain, unconditioned, so the lift
composes per atom. Then (`linearCutsOn`) the L7 chain in two rounds: the linear-form
atoms `y + r (x − c) ≤ sup` / `≥ inf` of every recognized second-order pair
(`linearCandidates`; O1 rational from the guard box; O2 by the rational linear-shape
route, else DI B, A, C over the bare evolve domain), and for each kept linear-form
atom its derived bound `x ≤ c + K/r` / `≥` (O1 by `guardImpliesRational`, else one
counted Z3 query; O2 by the rational derived-shape route, else DI B, A, C over the
evolve domain narrowed by THAT linear-form atom — stratified, recorded in `given`). An
atom already kept (rationally the same threshold) is not offered twice. Returns the
conjoined domain narrowing (every kept atom) and the full extended certificate entry. -/
def checkedCutX (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String) (side : Side) (m : PMode) :
    IO (IForm n × List CutAtomX) := do
  let dbg := (← IO.getEnv "RELCERT_DEBUG").isSome
  let linear ← linearCutsOn
  let (_, legacy) ← checkedCut s cnt maxQ maxSmt deadline vars n coord side m
  let fOwn := dynOf vars n side m
  let zeroF : Fin n → ITerm n := fun _ => ITerm.rat 0
  let evolveI := (lowerF vars n side m.evolve).getD IForm.tt
  let guardI? := lowerF vars n side m.guard
  -- the DI queries of an atom over a domain: route B, route A, and (L7 only) route C
  let diRoutes (a : PForm) (dom : IForm n) (withC : Bool) : IO (Option CutRouteX) := do
    match fOwn, cutAtomG vars n side a with
    | some f, some g =>
        let gdot := match side with
          | Side.L => ilieDeriv g f zeroF (ITerm.rat 1)
          | _      => ilieDeriv g zeroF f (ITerm.rat 1)
        let rB := IForm.and dom (IForm.and (IForm.cmp .eq g (.rat 0))
          (IForm.cmp .ge gdot (.rat 0)))
        if ← probeUnsat s cnt maxQ maxSmt deadline coord rB then pure (some .diStrict)
        else if ← probeUnsat s cnt maxQ maxSmt deadline coord
            (IForm.and dom (IForm.cmp .gt gdot (.rat 0))) then
          pure (some .diNonstrict)
        else if withC then
          let rC := IForm.and dom (IForm.and (IForm.cmp .ge g (.rat 0))
            (IForm.cmp .gt gdot (.rat 0)))
          if ← probeUnsat s cnt maxQ maxSmt deadline coord rC then pure (some .diSuperlevel)
          else pure none
        else pure none
    | _, _ => pure none
  -- O2 of an L1 / L2 (closed threshold) atom: unconditioned, legacy routes only
  let o2 (a : PForm) : IO (Option CutRouteX) := do
    if contractShapeOKX m a then pure (some .shape)
    else if (atomVars a).all (frozenIn m) then pure (some .frozen)
    else diRoutes a evolveI false
  -- the O1 Z3 fallback: one counted query `UNSAT(guard ∧ ¬atom)`
  let entryZ3 (a : PForm) : IO Bool := do
    match guardI?, cutAtomG vars n side a with
    | some gI, some g =>
        probeUnsat s cnt maxQ maxSmt deadline coord (IForm.and gI (IForm.cmp .gt g (.rat 0)))
    | _, _ => pure false
  let mut out : List CutAtomX :=
    legacy.map (fun ar => { atom := ar.1, kind := .guardConj, entry := .membership,
                            route := CutRouteX.ofLegacy ar.2, given := [] })
  let mut seen : List PForm := legacy.map (·.1)
  -- L2: closures of the strict guard conjuncts (O1 by weakening)
  for sa in strictAtoms m.guard do
    match closureOf sa with
    | none => pure ()
    | some a =>
        if seen.any (atomEqQ a) then pure () else
        match ← o2 a with
        | some r =>
            seen := seen ++ [a]
            out := out ++ [{ atom := a, kind := .closure, entry := .weakening, route := r, given := [] }]
            if dbg then IO.eprintln s!"    [route] {m.name}: closure {ppForm a}: {r.tag}"
        | none => pure ()
  -- L1: implied-contraction atoms (O1 rational, else one Z3 query)
  for a in impliedCandidates m do
    if seen.any (atomEqQ a) then pure () else
    let entry? : Option CutEntry ←
      if guardImpliesRational m.guard a then pure (some CutEntry.rational)
      else if ← entryZ3 a then pure (some CutEntry.z3)
      else pure none
    match entry? with
    | none => pure ()
    | some e =>
        match ← o2 a with
        | some r =>
            seen := seen ++ [a]
            out := out ++ [{ atom := a, kind := .impliedContract, entry := e, route := r, given := [] }]
            if dbg then IO.eprintln s!"    [route] {m.name}: implied {ppForm a}: O1 {e.tag}, O2 {r.tag}"
        | none => pure ()
  -- L7 round 1: linear-form atoms of the recognized second-order pairs (O1 rational
  -- from the guard box, by construction; O2 linear-shape, else DI B / A / C)
  let mut kept1 : List LinCand := []
  if linear then
    if dbg then
      -- diagnostics: recognized pairs whose guard offers no candidate (no box on the
      -- pair's coordinates, or irrational eigenvalues)
      for p in secondOrderPairs m do
        let roots := pairRoots p.a p.b
        if roots.isEmpty then
          IO.eprintln s!"    [lin-skip] {m.name}: pair ({p.x}, {p.y}) has no positive rational root (b² − 4a not a rational square)"
        else if (linearCandidates m).all (fun c => c.pair != p) then
          IO.eprintln s!"    [lin-skip] {m.name}: pair ({p.x}, {p.y}) with {roots.length} root(s) but the guard bounds neither side of ({p.x}, {p.y}) — no O1 constant"
    for cand in linearCandidates m do
      if seen.any (· == cand.atom) then pure () else
      let r? : Option CutRouteX ←
        if linearShapeOKX m cand.atom then pure (some .linearShape)
        else diRoutes cand.atom evolveI true
      match r? with
      | some r =>
          seen := seen ++ [cand.atom]
          kept1 := kept1 ++ [cand]
          out := out ++ [{ atom := cand.atom, kind := .linearForm, entry := .rational,
                           route := r, given := [] }]
          if dbg then IO.eprintln s!"    [route] {m.name}: linear-form {ppForm cand.atom}: O1 rational, O2 {r.tag}"
      | none => pure ()
    -- L7 round 2: the derived bound of each kept linear-form atom, STRATIFIED on it
    for cand in kept1 do
      match derivedOf cand with
      | none => pure ()
      | some a =>
          -- not offered twice, and not when the evolve box already implies it (a bound
          -- wider than the domain narrows nothing)
          if seen.any (atomEqQ a) || guardImpliesRational m.evolve a then pure () else
          let entry? : Option CutEntry ←
            if guardImpliesRational m.guard a then pure (some CutEntry.rational)
            else if ← entryZ3 a then pure (some CutEntry.z3)
            else pure none
          match entry? with
          | none => pure ()
          | some e =>
              let r? : Option CutRouteX ←
                if derivedShapeOKX m cand.atom a then pure (some .derivedShape)
                else
                  let dom := match lowerF vars n side cand.atom with
                    | some gI => IForm.and evolveI gI
                    | none => evolveI
                  diRoutes a dom true
              match r? with
              | some r =>
                  seen := seen ++ [a]
                  out := out ++ [{ atom := a, kind := .derivedBound, entry := e, route := r,
                                   given := [cand.atom] }]
                  if dbg then IO.eprintln s!"    [route] {m.name}: derived-bound {ppForm a} given {ppForm cand.atom}: O1 {e.tag}, O2 {r.tag}"
              | none => pure ()
  let cut := out.foldl (fun d x =>
    match lowerF vars n side x.atom with
    | some fI => IForm.and d fI
    | none => d) IForm.tt
  pure (cut, out)

/-- Conjoin the checked cuts, shape-normalized: `tt` cuts (the `RELCERT_NO_CUT` path)
leave the base formula UNCHANGED, so emitted-cover instances mirror the exact query. -/
def andCuts {n : ℕ} (base cutL cutR : IForm n) : IForm n :=
  let b1 := if cutL == IForm.tt then base else IForm.and base cutL
  if cutR == IForm.tt then b1 else IForm.and b1 cutR

/-- Check one segment `(qL=mL, qR=mR, λ)`: `pass` iff EVERY component has a route query
(A, B or C, `Run.routeQueries`) that is Z3-`unsat`; `fail` iff some component is definitively `sat`; `incon` on any Z3
error/`unknown` or unbuildable query. -/
def checkSeg (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String)
    (comps : List (ITerm n)) (cutL cutR : IForm n) (mL mR : PMode) (lam : ℚ)
    (strict : List Bool := []) :
    IO (Seg × List Nat) := do
  -- STRATIFIED DIFFERENTIAL CUTS (soundness-critical, 2026-07-15). A component may
  -- narrow its query domain ONLY by components proven in EARLIER rounds (sequential,
  -- acyclic DC — Platzer's differential cut, iterated). The previous MUTUAL narrowing
  -- (every component assuming all siblings simultaneously) was a circular cut and
  -- UNSOUND for routes A/C: with `comps = [x², x²]`, `x' = 1`, each narrowed domain is
  -- `{x = 0}` and route A's query `x = 0 ∧ 2x > 0` is UNSAT — falsely certifying
  -- `x² ≤ 0` under `x' = 1` (the t²-pathology; see `nonstrict_boundary_insufficient`
  -- and docs/history/COVER-AUDIT.md R4). Stratified soundness: round-1 components certify on
  -- the bare domain (single-component theorems); a round-k component's runs lie in the
  -- earlier-strata-narrowed ode because those invariants hold pointwise by induction.
  -- The checked cuts remain in all domains (independently justified, O1/O2).
  -- Fixpoint: at most |comps| + 1 bounded rounds (the proven set strictly grows).
  -- Status: pass iff ALL components eventually certify; the final (fixed-point) round
  -- classifies the unproven ones — incon if any was inconclusive there, else fail.
  let mut proven : List Nat := []
  let mut lastIncon := false
  for _ in List.range (comps.length + 1) do
    let mut progress := false
    lastIncon := false
    for i in List.range comps.length do
      if proven.contains i then pure () else
      match comps[i]? with
      | none => pure ()
      | some g =>
        match segParts vars n g mL mR lam with
        | none => lastIncon := true                  -- couldn't build the query
        | some (baseDom, gdot) =>
            -- CHECKED-CUT domains + the PROVEN strata (never unproven siblings)
            let baseDom := andCuts baseDom cutL cutR
            let dom := strataDomIR comps proven baseDom
            let mut compPass := false
            let mut compIncon := false
            -- a strict component (`invStrictFlags`) is certified by route A or B only
            for q in routeQueriesS (strict.getD i false) dom g gdot do
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
            if compPass then do
              proven := proven ++ [i]
              progress := true
            else if compIncon then lastIncon := true
            else if (← IO.getEnv "RELCERT_DBGC").isSome then
              IO.eprintln s!"      FAIL comp#{i} @ {mL.name}->{mR.name} λ={lam} (strata {proven})"
    if !progress then break
  return ((if proven.length == comps.length then Seg.pass
           else if lastIncon then Seg.incon else Seg.fail), proven)

/-- **DYNAMIC REPOSITION check (the right-only flow certificate of Lemma 4)**, on a region.
The left FROZEN (`fL=0`, `ġ` via `segPartsRO`), stratified like `checkSeg` (a component's domain
is narrowed only by components proven in earlier rounds, docs/history/COVER-AUDIT.md R4).
`withGuardL` selects σ: pre-j domain `guardL ∧ evolveL ∧ evolveR`, post-j `evolveL ∧ evolveR`.
* `rg = none` (default): the WHOLE domain, route A only (`UNSAT(ġ > 0 ∧ domain)`,
  `DI_nonstrict_domain`). Whole-domain, NOT boundary (`g=0 ∧ ġ≥0`): the `t²` guard.
* `rg = some (Bo, Bc)` (opt-in `prelanding = true`, `docs/PRELANDING.md`): the PRE-LANDING region
  of the node's progress certificate, `Bo` = before its last threshold (`x < θ`), `Bc` its
  closure (`x ≤ θ`). A non-strict component: routes A, B or C over `domain ∧ Bo` (the invariant
  at the first entry into the target follows by continuity); a strict one (`strict`, the row's
  `invStrictFlags`): route A over `domain ∧ Bc` (the limit along `Bo` gives only `≤ 0`; route A
  on the closure keeps `< 0` up to and including the stop point).
`true` iff every component has a definitive `unsat` route; sat/unknown/error → withhold. -/
def checkDynRepo (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String)
    (comps : List (ITerm n)) (cutL cutR : IForm n) (mL mR : PMode) (withGuardL : Bool)
    (rg : Option (IForm n × IForm n) := none) (strict : List Bool := []) :
    IO (Bool × List Nat) := do
  let gLform : IForm n := (if withGuardL then lowerF vars n Side.L mL.guard else some IForm.tt).getD IForm.tt
  let mut proven : List Nat := []
  for _ in List.range (comps.length + 1) do
    let mut progress := false
    for i in List.range comps.length do
      if proven.contains i then pure () else
      match comps[i]? with
      | none => pure ()
      | some g =>
        match segPartsRO vars n g mL mR with        -- (evolveL∧evolveR, ġ) with fL=0, λ=1
        | none => pure ()
        | some (baseDom, gdot) =>
            let isStrict := strict.getD i false
            let baseDom := andCuts baseDom cutL cutR   -- checked-cut narrowing
            let baseDom := match rg with
              | none => baseDom
              | some (bo, bc) => IForm.and baseDom (if isStrict then bc else bo)
            let dom0 := strataDomIR comps proven baseDom
            -- σ-matched, shape-normalized: conjoin guardL ONLY pre-j (no tt-noise post-j)
            let dom := if withGuardL then IForm.and dom0 gLform else dom0
            -- route A first (the whole-domain pack's only route); B, C on the pre-landing region
            let qs := match rg with
              | none => (routeQueries dom g gdot).take 1
              | some _ => if isStrict then (routeQueries dom g gdot).take 1 else routeQueries dom g gdot
            let mut compPass := false
            for q in qs do
              if compPass then pure () else
              let script := q.toScript coord
              if script.length > maxSmt then pure ()
              else do
                cnt.modify (· + 1)
                if (← cnt.get) > maxQ then throw (IO.userError "query budget exceeded")
                if (← IO.monoMsNow) > deadline then throw (IO.userError "time budget exceeded")
                match ← s.check script with
                | .ok .unsat => compPass := true
                | _          => pure ()
            if compPass then
              proven := proven ++ [i]
              progress := true
    if !progress then break
  pure (proven.length == comps.length, proven)

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

/-- **Definition 8, executable.** From start mode `q` with segment budget `B` (`= ⌈εL/δL⌉`,
weight 1 per segment), return the modes the cover **visits**, or `none` if it fails:

* the mode must be certified (`seg q = pass` — Definition 8's *joint certified*);
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

/-- **Non-connection pruning (Definition 6)** (FIX 3, soundness-critical — *prune only on UNSAT*). For a
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
supply its two UNSAT hypotheses. Only a STRICT scalar successor guard (`a > b` / `a < b`), or a
conjunction whose LEADING conjunct is one (the barrier is that conjunct; the guard implies it;
added 2026-10-10 for the latched multi-link AEB sinks of `platoon3_*`), is prunable — a CLOSED
guard (`≥`/`≤`) has a boundary the strict barrier cannot exclude, so it is kept (scope, not
unsoundness). -/
def nonConnPrune (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String) (cutR : IForm n)
    (mR mSuc : PMode) : IO Bool := do
  -- The two queries are built ONCE, in `Trusted/NonConnQuery.lean` (shared with the
  -- verdict runner and the kernel bridge); `none` = a closed guard (or a compound one whose
  -- leading conjunct is not strict) or a part that does not lower ⟹ keep the edge.
  match NonConn.queries vars n cutR mR mSuc with
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
      | .ok .unsat, .ok .unsat => pure true    -- BOTH UNSAT ⟹ Definition 6 non-connection ⟹ PRUNE
      | _, _                   => pure false   -- anything else ⟹ keep the edge required

/-! ## Existential mode choice (default; `RELCERT_NO_CHOICE=1` disables it)

Definition 8 with its committed-subset cases: two moves in which the witness CHOOSES the right system's next
mode instead of covering every successor:

* **chosen successors**: after a joint (resp. right-only) segment in `q`, cover only a
  subset `S` of the retained (resp. exit) successors, provided the coverage query
  `EndRegion(q) ∧ ⋀_{q'∈S} ¬guard(q')` is `unsat` (wherever the segment ends, some
  successor in `S` is enabled);
* **entry hop**: a zero-duration switch from `q` into a successor `q'`, provided the
  coverage query over `StartRegion(q)` is `unsat`; at most one hop before each segment.

Coverage is monotone in `S`, so only the maximal coverable subset is queried. This search
is tried only after the `decideCovered` gate has failed, so it can only add certificates; a
cover it accepts is reported on stderr as `[choice] …`, and the chosen sets are emitted
under `RELCERT_CHOICE_OUT` (`Trusted/ChoiceEmit.lean`). Soundness: the argument is
`docs/CHOICE-SOUNDNESS.md`, mechanized as the general Theorem 3 with choice
(`theorem3_of_coverX`, `docs/THEOREM3-GENERAL.md`); the generic bridge replays the emitted
chosen sets through `decideCoveredX` and reads each coverage query's `unsat` as the
coverage premise (`Proofs/Encoding/Emitted/Choice.lean`, `docs/BRIDGE.md`). -/

/-- One choice-cover decision context (per left mode and stretch). -/
structure ChoiceCtx (n : ℕ) where
  node      : String → Bool
  jointOK   : String → Bool
  dynOK     : String → Bool → Bool          -- σ: true = pre-joint
  retained  : String → List String          -- self-loop + non-pruned declared successors
  exits     : String → List String          -- non-pruned, non-self declared successors
  hopTgts   : String → List String          -- non-pruned, non-self declared successors
  guardR    : String → Option (IForm n)
  jointEnd  : String → IForm n
  repoEnd   : String → Bool → IForm n
  startReg  : String → Bool → IForm n

/-- Coverage query: `region ∧ ⋀_{q'∈S} ¬guard(q')`; `true` iff definitively `unsat`. -/
def coverageUnsat {n : ℕ} (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (coord : Fin n → String) (cx : ChoiceCtx n) (region : IForm n) (S : List String) :
    IO Bool := do
  let negs := S.map (fun q' => (cx.guardR q').map IForm.neg)
  if S.isEmpty || negs.any Option.isNone then return false
  let q := (negs.filterMap id).foldl IForm.and region
  probeUnsat s cnt maxQ maxSmt deadline coord q

/-- Definition 8 with committed subsets (name-based, memoized). `path` rejects budget-neutral cycles
(a revisit of an in-progress configuration is uncovered, as in Definition 8). -/
partial def choiceCover {n : ℕ} (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (coord : Fin n → String) (cx : ChoiceCtx n)
    (memo : IO.Ref (Std.HashMap (String × Nat × Bool × Bool) Bool))
    (log : IO.Ref (List String)) (clog : IO.Ref (List Choice.ChoiceEntryE))
    (path : List (String × Nat × Bool × Bool))
    (q : String) (B : Nat) (pre hop : Bool) : IO Bool := do
  let key := (q, B, pre, hop)
  if path.contains key then return false
  if let some r := (← memo.get)[key]? then return r
  let path := key :: path
  let rec' := fun (q' : String) (B' : Nat) (pre' hop' : Bool) =>
    choiceCover s cnt maxQ maxSmt deadline coord cx memo log clog path q' B' pre' hop'
  let mut ok := false
  -- base: a joint segment closes the remaining budget
  if cx.node q && cx.jointOK q && B ≤ 1 then ok := true
  -- joint step: all retained successors (old rule), else a chosen covered subset
  if !ok && cx.node q && cx.jointOK q && 1 < B then
    let R := cx.retained q
    let mut C : List String := []
    for q' in R do
      if ← rec' q' (B - 1) false true then C := C ++ [q']
    if C.length == R.length then ok := true
    else if !C.isEmpty then
      if ← coverageUnsat s cnt maxQ maxSmt deadline coord cx (cx.jointEnd q) C then
        ok := true
        log.modify (· ++ [s!"joint {q} B={B} chose {C} of {R}"])
        clog.modify (· ++ [⟨"", q, .joint, false, C⟩])
  -- right-only reposition: all exits (old rule), else a chosen covered subset
  if !ok && cx.node q && cx.dynOK q pre && 0 < B then
    let E := cx.exits q
    if !E.isEmpty then
      let mut C : List String := []
      for q' in E do
        if ← rec' q' B pre true then C := C ++ [q']
      if C.length == E.length then ok := true
      else if !C.isEmpty then
        if ← coverageUnsat s cnt maxQ maxSmt deadline coord cx (cx.repoEnd q pre) C then
          ok := true
          log.modify (· ++ [s!"repo {q} B={B} pre={pre} chose {C} of {E}"])
          clog.modify (· ++ [⟨"", q, .repo, pre, C⟩])
  -- entry hop: zero-duration switch into a chosen covered successor
  if !ok && hop && 0 < B then
    let T := cx.hopTgts q
    let mut C : List String := []
    for q' in T do
      if ← rec' q' B pre false then C := C ++ [q']
    if !C.isEmpty then
      if ← coverageUnsat s cnt maxQ maxSmt deadline coord cx (cx.startReg q pre) C then
        ok := true
        log.modify (· ++ [s!"hop {q} B={B} pre={pre} into {C}"])
        clog.modify (· ++ [⟨"", q, .hop, pre, C⟩])
  memo.modify (·.insert key ok)
  return ok


/-! ## The progress certificate search (`Trusted/ProgressEmit.lean`) -/

/-- The progress certificates found in the current run (per benchmark; reset by
`certifyWithData`), for emission. -/
initialize progressLog : IO.Ref (List Progress.ProgressE) ← IO.mkRef []

/-- The chosen sets of the current run (per benchmark; reset by `certifyWithData`), for
emission (`RELCERT_CHOICE_OUT`). -/
initialize choiceLog : IO.Ref (List Choice.ChoiceEntryE) ← IO.mkRef []

/-- The pre-landing nodes of the current run (per benchmark; reset by `certifyWithData`), for
emission (`RELCERT_PRELANDING_OUT`); nonempty only under `prelanding = true`. -/
initialize prelandLog : IO.Ref (List Preland.PrelandNodeE) ← IO.mkRef []

/-- The variables of an IR term. -/
def itermVars {n : ℕ} : ITerm n → List (Var n)
  | .var v => [v]
  | .rat _ => []
  | .bin _ a b => itermVars a ++ itermVars b

/-- The nonstrict threshold atoms `x ≥ c` / `x ≤ c` of a guard (a strict one cannot hold at the
crossing state `x = c`). -/
partial def thresholdAtoms : PForm → List (String × ℚ × Bool)
  | .cmp op (.var x) (.num c) =>
      match parseRat c with
      | some q => if op == ">=" then [(x, q, true)] else if op == "<=" then [(x, q, false)] else []
      | none => []
  | .cmp op (.num c) (.var x) =>
      match parseRat c with
      | some q => if op == "<=" then [(x, q, true)] else if op == ">=" then [(x, q, false)] else []
      | none => []
  | .and a b => thresholdAtoms a ++ thresholdAtoms b
  | _ => []

/-- **The progress search** at a reposition node with region `R` (the facts its right-only
flow preserves), field `fR`, and exits. Candidates: a threshold atom of an exit guard as the
last stage (its landing query first, then its rate on a geometric grid); failing that, one
helper stage on a coordinate the field reads (its keep query, its rate, then the last stage's
rate under the helper's crossed fact). Two stages at most. `accept` (the pre-landing check,
`checkDynRepo` on the region, which reads only the last stage): a found stage list is returned only if it
holds, otherwise the next candidate is tried; the default accepts, so without the key the
search is the old one. -/
def checkProgress {n : ℕ} (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (coord : Fin n → String) (R guardq : IForm n) (fR : Fin n → ITerm n)
    (exits : List PMode)
    (accept : List Progress.ProgressStageE → IO Bool := fun _ => pure true) :
    IO (Option (List Progress.ProgressStageE)) := do
  let guards := exits.map (fun m => lowerF vars n Side.R m.guard)
  if exits.isEmpty || guards.any Option.isNone then return none
  let gs := guards.filterMap id
  let probe := fun (q : IForm n) => probeUnsat s cnt maxQ maxSmt deadline coord q
  let probeAll := fun (qs : List (IForm n)) => do
    let mut ok := true
    for q in qs do
      if ok then ok := ← probe q
    pure ok
  let cands := (exits.flatMap (fun m => thresholdAtoms m.guard)).eraseDups
  let rates : List ℚ := [1, 1/2, 1/4, 1/8, 1/16, 1/32, 1/64, 1/128]
  let y0s : List ℚ := [5, 2, 1, 1/2, 3/10, 1/5, 1/10, 1/20]
  for (x, θ, up) in cands do
    match resolveVar vars n Side.R x with
    | none => pure ()
    | some v =>
      let stLast := fun (r : ℚ) => ({ var := x, theta := θ, up := up, rate := r } : Progress.ProgressStageE)
      if !(← probeAll (Progress.landQueries R guardq v (stLast 1) gs)) then continue
      let mut found : Option (List Progress.ProgressStageE) := none
      for r in rates do
        if found.isSome then break
        let st := stLast r
        if ← probe (Progress.rateQuery R fR [(v, st)] 0 v st) then found := some [st]
      match found with
      | some sts => if ← accept sts then return found else continue
      | none => pure ()
      let ys := (itermVars (fR v.2)).eraseDups.filter (fun w => w.1 == Side.R && w != v)
      for w in ys do
        for upY in [true, false] do
          for y0 in y0s do
            if found.isSome then break
            let stY := fun (r1 : ℚ) =>
              ({ var := coord w.2, theta := y0, up := upY, rate := r1 } : Progress.ProgressStageE)
            if !(← probe (Progress.keepQuery R fR [(w, stY 1)] 0 w (stY 1))) then continue
            let mut r1 : Option ℚ := none
            for r in rates do
              if r1.isSome then break
              if ← probe (Progress.rateQuery R fR [(w, stY r)] 0 w (stY r)) then r1 := some r
            match r1 with
            | none => pure ()
            | some r1v =>
              for r in rates do
                if found.isSome then break
                let vs := [(w, stY r1v), (v, stLast r)]
                if ← probe (Progress.rateQuery R fR vs 1 v (stLast r)) then
                  found := some [stY r1v, stLast r]
      match found with
      | some sts => if ← accept sts then return found
      | none => pure ()
  return none

/-- Cover a single left mode: `cov` if some (start,λ) closes definitively; `incon` if none
close but a route was inconclusive; `nocov` if all routes are definitive fails. -/
def coverMode (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat) (p : PProblem)
    (vars : List String) (n : ℕ)
    (coord : Fin n → String) (comps : List (ITerm n))
    (prunedOf : String → String → Bool)
    (cutL : IForm n) (cutOfR : String → IForm n)
    (epsL epsR lmin lmax : ℚ) (mL : PMode) (strict : List Bool := []) :
    IO (Cov3 × Option LeftCoverE) := do
  let mut sawIncon := false
  -- FIX 1 (precise admissibility): the admissible initial right modes for `mL` — those with an
  -- invariant-satisfying initial pair. λ-independent (guards + `ϕ_rel` only), so computed ONCE.
  -- `.cov` will require every admissible start to cover (the ∀ over initial pairs); an
  -- inadmissible mode (no `guardL ∧ guardR ∧ ϕ_rel` pair, proven by Z3 `unsat`) is dropped.
  let mut admMods : List PMode := []
  for mR in p.R.modes do
    if ← admissible s cnt maxQ maxSmt deadline vars n coord comps mL mR then
      admMods := admMods ++ [mR]
  let lowL := fun (f : PForm) => (lowerF vars n Side.L f).getD IForm.tt
  let lowR := fun (f : PForm) => (lowerF vars n Side.R f).getD IForm.tt
  let modeOf := fun (nm : String) => p.R.modes.find? (·.name == nm)
  let invI : IForm n := comps.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) IForm.tt
  let leftFacts := fun (pre : Bool) =>
    let b := IForm.and (IForm.and (lowL mL.evolve) cutL) invI
    if pre then IForm.and b (lowL mL.guard) else b
  let rightFacts := fun (nm : String) => match modeOf nm with
    | some m => IForm.and (lowR m.evolve) (cutOfR nm)
    | none => IForm.tt
  let declared := fun (nm : String) =>
    ((succOf p nm).filter (fun t => !prunedOf nm t)).eraseDups
  -- The only right-only move is the DYNAMIC reposition below: a full-interval right-only flow.
  -- There is no zero-duration right switch (one that would switch at a single instant with no
  -- check that the successor's guard holds there).
  -- DYNAMIC reposition (the right-only flow certificate of Lemma 4): right-only whole-domain flow cert (route A), σ-matched.
  -- λ-independent (fL=0, λ=1; sign λ-invariant), computed ONCE. For the rover cross-terrain hop,
  -- `ġ_s=−v_R≤0` and `ġ_v` on the terrain's v-evolve-cap ⟹ route-A UNSAT ⟹ the advancing reposition.
  let mut dynMap : List (String × Bool × Bool) := []
  let mut dynOrders : List (String × List Nat × List Nat) := []
  -- With `prelanding = true` the whole-domain pack is not tried: every reposition node is a
  -- pre-landing node (below), whose pack is implied by the whole-domain one on the same strata.
  for mR in p.R.modes do
    let (pre, preOrd)  ← if p.prelanding then pure (false, []) else
      checkDynRepo s cnt maxQ maxSmt deadline vars n coord comps cutL (cutOfR mR.name) mL mR true
    let (post, postOrd) ← if p.prelanding then pure (false, []) else
      checkDynRepo s cnt maxQ maxSmt deadline vars n coord comps cutL (cutOfR mR.name) mL mR false
    dynMap := dynMap ++ [(mR.name, pre, post)]
    dynOrders := dynOrders ++ [(mR.name, preOrd, postOrd)]
  -- PROGRESS (default; `RELCERT_NO_PROGRESS=1` disables): a reposition node must also certify that its right-only
  -- flow reaches an exit (`checkProgress`, `Trusted/ProgressEmit.lean`); otherwise it is not
  -- a node. The certificates found are logged for emission (`RELCERT_PROGRESS_OUT`).
  -- the progress certificate is required of every reposition node by default
  -- (`RELCERT_NO_PROGRESS=1` disables it: the ablation of the right-only kind's progress)
  let progressOn := (← IO.getEnv "RELCERT_NO_PROGRESS").isNone
  let mut progMap : List (String × Bool × Bool) := []
  -- PRE-LANDING (`prelanding = true`, `docs/PRELANDING.md`): the progress search runs first;
  -- each candidate stage list is accepted only if the pre-landing pack holds on the half-open
  -- region before its last stage (`checkDynRepo` on the region). `(mR, pre, order)` per node found.
  let mut plMap : List (String × Bool × List Nat) := []
  let plOrd ← IO.mkRef ([] : List Nat)
  if progressOn then
    for mR in p.R.modes do
      let dyn := (dynMap.find? (·.1 == mR.name)).getD (mR.name, false, false)
      let exitsL := (declared mR.name).filter (· != mR.name)
      let exitModes := exitsL.filterMap modeOf
      let mut pp := false
      let mut qq := false
      for pre in [true, false] do
        let dynOK := if pre then dyn.2.1 else dyn.2.2
        if (dynOK || p.prelanding) && !exitModes.isEmpty then
          match dynOf vars n Side.R mR with
          | none => pure ()
          | some fRm =>
            let R := IForm.and (leftFacts pre) (rightFacts mR.name)
            let guardq := (lowerF vars n Side.R mR.guard).getD IForm.tt
            let accept := fun (sts : List Progress.ProgressStageE) => do
              if !p.prelanding then return true
              match sts.getLast? with
              | none => return false
              | some st =>
                match resolveVar vars n Side.R st.var with
                | none => return false
                | some v =>
                  let (ok, ord) ← checkDynRepo s cnt maxQ maxSmt deadline vars n coord comps cutL
                    (cutOfR mR.name) mL mR pre (some (Progress.before v st, Progress.beforeCl v st))
                    strict
                  if ok then plOrd.set ord
                  return ok
            match ← checkProgress s cnt maxQ maxSmt deadline vars coord R guardq fRm exitModes accept with
            | some stages =>
                IO.eprintln s!"  [progress] {p.name} {mL.name}_L/{mR.name} pre={pre}: {stages.map (fun st => s!"{st.var}{if st.up then "≥" else "≤"}{st.theta}@{st.rate}")} exits={exitsL}"
                progressLog.modify (· ++ [⟨mL.name, mR.name, pre, stages, exitsL⟩])
                if p.prelanding then plMap := plMap ++ [(mR.name, pre, ← plOrd.get)]
                if pre then pp := true else qq := true
            | none =>
                IO.eprintln s!"  [progress] {p.name} {mL.name}_L/{mR.name} pre={pre}: NONE exits={exitsL}"
      progMap := progMap ++ [(mR.name, pp, qq)]
  let progOK := fun (nm : String) (pre : Bool) =>
    !progressOn || (((progMap.find? (·.1 == nm)).map (fun t => if pre then t.2.1 else t.2.2)).getD false)
  -- BASELINE `RELCERT_SYNC=1` (time-synchronous matching): λ = 1 only, no right-only
  -- reposition, no per-pairing fallback; multi-step joint covers stay allowed.
  let sync := (← IO.getEnv "RELCERT_SYNC").isSome
  -- `RELCERT_NO_REPO=1`: no right-only reposition nodes of the all-successors kind (the
  -- chosen-exits form of the choice cover is the hop, which needs no reposition node).
  let noRepo := (← IO.getEnv "RELCERT_NO_REPO").isSome
  -- MEASUREMENT `RELCERT_SINGLE_STEP=1` (information only, 2026-10-30): single-step covers
  -- only, one right control step per left window: a cover whose segment budget B exceeds 1 is
  -- not accepted (the common pass, the per-pairing fallback and the choice cover alike). It only
  -- removes covers, so it can turn CERTIFIED into DECLINED, never the reverse.
  let singleStep := (← IO.getEnv "RELCERT_SINGLE_STEP").isSome
  let repoDynPreOK  := fun (nm : String) => !sync && !noRepo && progOK nm true &&
    ((dynMap.find? (·.1 == nm)).map (·.2.1) |>.getD false)
  let repoDynPostOK := fun (nm : String) => !sync && !noRepo && progOK nm false &&
    ((dynMap.find? (·.1 == nm)).map (·.2.2) |>.getD false)
  -- the pre-landing nodes (empty without the key): a NEW flag, never `dynPre`/`dynPost` (the
  -- emitted rows keep those for the whole-domain pack); the cover graph uses the merged rows
  let plOK := fun (nm : String) (pre : Bool) => !sync && !noRepo &&
    plMap.any (fun t => t.1 == nm && t.2.1 == pre)
  let repoPreE := fun (nm : String) => repoDynPreOK nm || plOK nm true
  let repoPostE := fun (nm : String) => repoDynPostOK nm || plOK nm false
  if p.prelanding && !sync && !noRepo then
    let nodes : List Preland.PrelandNodeE := plMap.map (fun t => ⟨mL.name, t.1, t.2.1, t.2.2⟩)
    prelandLog.modify (· ++ nodes)
  if (← IO.getEnv "RELCERT_DEBUG").isSome then
    IO.eprintln s!"  [admissible] {mL.name}_L: {admMods.map (·.name)}"
    let dpreL := dynMap.filterMap (fun p => if p.2.1 then some p.1 else none)
    let dpostL := dynMap.filterMap (fun p => if p.2.2 then some p.1 else none)
    IO.eprintln s!"  [repo-dyn-pre] {mL.name}_L: {dpreL} [repo-dyn-post]: {dpostL}"
    if p.prelanding then
      IO.eprintln s!"  [repo-prelanding] {mL.name}_L: {plMap.map (fun t => s!"{t.1}{if t.2.1 then "/pre" else "/post"}")}"
  -- PER-PAIRING STRETCH (fallback). The common pass below keeps one λ per left mode. When no
  -- common λ closes the cover, each right mode may use its own stretch: the smallest positive
  -- candidate at which its joint segment passed, or the stutter stretch `0` (under the key) only
  -- if it passed at no positive one (`firstPass`, recorded during the common pass, so the
  -- fallback asks Z3 nothing new). Every joint segment is then cut to the common left span
  -- δ = εR / λmax (λmax the largest chosen stretch): a segment of mode `mR` at stretch λ_mR
  -- lasting δ of left time reaches τ_R = λ_mR·δ ≤ εR, inside the right interval, and the
  -- budget stays the integer count ⌈εL/δ⌉ with unit weights, so the verified `decideCovered`
  -- gate and its soundness proof are unchanged. Soundness: each pairing's flow obligation is
  -- certified at its own λ (the per-pair `Verd` the instance replays, `couple_cutX` takes λ
  -- per coupling); the shorter span only cuts segments short, which Lemma 2 (its conclusion holds
  -- throughout a segment) and Assumption 1 (every duration ≤ εR ends in a successor's guard)
  -- admit. Partial right cycles are within the model the bridge proves Theorem 3 over: its
  -- clocked right automaton `rightAutomatonBodyC` tests `tr ≤ εR`, so a right cycle may end
  -- early (the unclocked right automaton of the archived standalone route admitted them too).
  -- `RELCERT_NO_PAIR_STRETCH=1` disables the fallback (ablation: one stretch per left mode).
  let mut firstPass : List (String × ℚ × List Nat) := []   -- per mR: smallest passing λ, its order
  let mut lastOrder : List (String × List Nat) := []       -- per mR: the last computed order
  let mut everIncon : List String := []                      -- mR inconclusive at some λ
  let dpairOf := fun (nm : String) => match dynOrders.find? (fun t => t.1 == nm) with
    | some t => (t.2.1, t.2.2)
    | none => ([], [])
  -- the structural gate at a given segment status / strata / window stretch: `.cov` iff every
  -- admissible initial mode covers (shared by the common pass and the fallback)
  let gate := fun (seg : String → Seg) (strataMap : List PairStrataE) (lamQ deltaL : ℚ) =>
    -- segment budget B = ⌈εL/δL⌉ (weight 1 per segment), capped; single-sync ⟺ B ≤ 1
    let bBudget := min (epsL / deltaL).ceil.toNat 256
    let flagRows : List ModeFlagsE := p.R.modes.map (fun m =>
      { name := m.name, jointOK := seg m.name == Seg.pass,
        dynPre := repoDynPreOK m.name, dynPost := repoDynPostOK m.name })
    -- the rows the graph is built on: the emitted rows with the pre-landing nodes merged in
    -- (equal to `flagRows` without the key); `Emitted.withPL` is the kernel's same merge
    let effRows : List ModeFlagsE := flagRows.map (fun f =>
      { f with dynPre := f.dynPre || plOK f.name true, dynPost := f.dynPost || plOK f.name false })
    let repoOK := fun nm => repoPreE nm || repoPostE nm
    let idxOf := nodeIdx effRows
    let cgReal : SearchGraph (Var n) := buildCoverGraph effRows (succOf p) prunedOf
    let fuel := coverFuel effRows bBudget
    let startCovers := fun (mR : PMode) =>
      (seg mR.name == Seg.pass || repoOK mR.name) &&
        decideCovered cgReal fuel ⟨idxOf mR.name, bBudget, SrcSetting.preJ⟩
    if !admMods.isEmpty && !(singleStep && bBudget > 1) && admMods.all startCovers then
      some ({ mL := mL.name, lamQ := lamQ, bBudget := bBudget, flags := flagRows,
              admissible := admMods.map (·.name), strata := strataMap } : LeftCoverE)
    else none
  -- existential mode choice context (default, `RELCERT_NO_CHOICE=1` disables; see `choiceCover`)
  let choiceOn := (← IO.getEnv "RELCERT_NO_CHOICE").isNone
  let mut choiceCands : List (ℚ × ℚ × List (String × Seg) × List PairStrataE) := []
  -- MEASUREMENT `RELCERT_LAMBDA_SCAN=1`: evaluate every λ candidate (no early exit at the first
  -- closing cover) and print, per pairing, the candidates at which its joint segment passed.
  -- The verdict and the emitted cover are those of the first closing λ, as without the switch.
  let scan := (← IO.getEnv "RELCERT_LAMBDA_SCAN").isSome
  let mut scanCover : Option LeftCoverE := none
  let mut scanPass : List (String × List ℚ) := []
  let mut scanGrid : List ℚ := []
  let mkCtx := fun (seg : String → Seg) => ({
      node := fun nm => seg nm == Seg.pass || repoPreE nm || repoPostE nm
      jointOK := fun nm => seg nm == Seg.pass
      dynOK := fun nm pre => if pre then repoPreE nm else repoPostE nm
      retained := fun nm => (nm :: declared nm).eraseDups
      exits := fun nm => (declared nm).filter (· != nm)
      hopTgts := fun nm => (declared nm).filter (· != nm)
      guardR := fun nm => (modeOf nm).bind (fun m => lowerF vars n Side.R m.guard)
      jointEnd := fun nm => IForm.and (leftFacts false) (rightFacts nm)
      repoEnd := fun nm pre => IForm.and (leftFacts pre) (rightFacts nm)
      startReg := fun nm pre => IForm.and (IForm.and (leftFacts pre) (rightFacts nm))
        ((modeOf nm).map (fun m => lowR m.guard) |>.getD IForm.tt) } : ChoiceCtx n)
  for lam in (if sync then [(1 : ℚ)] else lambdaCandidates lmin lmax epsL epsR p.stutter) do
    -- `winLam`: the window stretch (`lamQ`); `lam` itself is every pairing's stretch here, `0`
    -- only for the stutter candidate (`windowOf`, `docs/STUTTER.md`)
    let (winLam, deltaL) := windowOf lam epsL epsR
    if deltaL ≤ 0 then continue
    -- precompute per-right-mode segment status at this λ
    let mut segMap : List (String × Seg) := []
    let mut strataMap : List PairStrataE := []
    for mR in p.R.modes do
      let (st, order) ←
        checkSeg s cnt maxQ maxSmt deadline vars n coord comps cutL (cutOfR mR.name) mL mR lam
          strict
      segMap := segMap ++ [(mR.name, st)]
      lastOrder := (mR.name, order) :: lastOrder.filter (·.1 != mR.name)
      if st == Seg.pass then
        match firstPass.find? (·.1 == mR.name) with
        -- the smallest POSITIVE passing stretch; the stutter candidate `0` (last) only for a
        -- pairing that passed at no positive one (the reference keeps pace where it can)
        | some t => if lam != 0 && lam < t.2.1 then
            firstPass := (mR.name, lam, order) :: firstPass.filter (·.1 != mR.name)
        | none => firstPass := firstPass ++ [(mR.name, lam, order)]
      if st == Seg.incon && !everIncon.contains mR.name then everIncon := everIncon ++ [mR.name]
      if scan && st == Seg.pass then
        scanPass := match scanPass.find? (·.1 == mR.name) with
          | some t => (mR.name, t.2 ++ [lam]) :: scanPass.filter (·.1 != mR.name)
          | none => scanPass ++ [(mR.name, [lam])]
      let dpair := dpairOf mR.name
      strataMap := strataMap ++
        [({ mR := mR.name, order := order, dynPreOrder := dpair.1,
            dynPostOrder := dpair.2, lamN := lam.num.toNat, lamD := lam.den } : PairStrataE)]
    let seg := fun q => (segMap.find? (·.1 == q)).map (·.2) |>.getD Seg.incon
    if (← IO.getEnv "RELCERT_DEBUG").isSome then
      IO.eprintln (s!"  [{mL.name}_L λ={lam} #comps={comps.length}] " ++
        String.intercalate " " (segMap.map (fun p => s!"{p.1}={repr p.2}")))
    -- VERIFIED structural gate (Step 4 + Definition 8 fidelity): CERTIFIED flows through the verified
    -- computable `decideCovered`, not the untrusted `dfsCov3`. For each start, `coverVisit`
    -- runs Definition 8 (certified-aware) to find the visited mode set; we build `decideCovered`'s
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
    -- NODES = modes joint-certified OR dynamic-reposition-certified (pre-j OR post-j). Each node
    -- carries `jointOK`, `dynPre`, `dynPost`; `decideCovered` offers base/joint-step where
    -- `jointOK`, and the zero-budget dynamic reposition step σ-matched (pre-j → `dynPre`, post-j
    -- → `dynPost`). The emitted flag rows are what `--emit-cover` prints — ONE construction,
    -- `buildCoverGraph`, shared by the gate and the kernel replays. The fuel bounds
    -- `decideCovered`'s depth: joint steps decrease budget (≤ `bBudget`), reposition steps keep
    -- budget but recurse only through repo-OK nodes' non-self exits; a budget-decrement can be
    -- interleaved with a zero-budget reposition through EACH node, so the worst-case depth is
    -- `bBudget·(nodeMods+1)`. Fuel only bounds the checker's search depth — larger is always
    -- sound (`decideCovered_sound` is fuel-generic); too-small merely over-declines. A start is
    -- usable iff it is a node; the initial source setting is **preJ** (no joint yet). Empty
    -- `admMods` ⟹ do NOT certify (a possibly-buggy all-drop cannot vacuously certify).
    if scan then scanGrid := scanGrid ++ [lam]
    match gate seg strataMap winLam deltaL with
    | some lc =>
        if scan then
          if scanCover.isNone then scanCover := some lc
        else return (.cov, some lc)
    | none => pure ()
    -- existential mode choice is NOT tried here: it runs only after the whole λ loop and the
    -- per-pairing fallback have failed with the old rule (below), so every cover the old rule
    -- finds is emitted unchanged. Record this λ's segment status for the choice pass.
    if choiceOn then choiceCands := choiceCands ++ [(lam, deltaL, segMap, strataMap)]
    if admMods.any (fun mR => seg mR.name == Seg.incon) then sawIncon := true
  if scan then
    let grid := (scanGrid.toArray.qsort (· < ·)).toList
    let idx := fun (l : ℚ) => grid.findIdx (· == l)
    IO.eprintln s!"  [lambda-scan] {p.name} {mL.name}_L grid={grid.length} points {grid.headD 0}..{grid.getLastD 0}"
    for mR in p.R.modes do
      let ls := ((scanPass.find? (·.1 == mR.name)).map (·.2)).getD []
      let ixs := ((ls.map idx).toArray.qsort (· < ·)).toList
      IO.eprintln s!"  [lambda-scan] {p.name} {mL.name}_L/{mR.name}: pass at {ixs.length} of {grid.length} grid steps {ixs}"
    if let some lc := scanCover then return (.cov, some lc)
  -- the per-pairing fallback (see above): only when the passing stretches are not all equal
  -- (otherwise the common pass at that stretch has already failed with the same nodes)
  let pairOn := (← IO.getEnv "RELCERT_NO_PAIR_STRETCH").isNone && !sync
  if pairOn && !firstPass.isEmpty then
    let lams := firstPass.map (·.2.1)
    let lamMax := lams.foldl max (lams.headD 1)
    let allEq := lams.all (· == lamMax)
    let (winMax, deltaL) := windowOf lamMax epsL epsR
    if !allEq && deltaL > 0 then
      let seg := fun q => if firstPass.any (·.1 == q) then Seg.pass
        else if everIncon.contains q then Seg.incon else Seg.fail
      let strataMap : List PairStrataE := p.R.modes.map (fun mR =>
        let dpair := dpairOf mR.name
        match firstPass.find? (·.1 == mR.name) with
        | some t => { mR := mR.name, order := t.2.2, dynPreOrder := dpair.1,
                      dynPostOrder := dpair.2, lamN := t.2.1.num.toNat, lamD := t.2.1.den }
        | none => { mR := mR.name, order := (lastOrder.find? (·.1 == mR.name)).map (·.2) |>.getD [],
                    dynPreOrder := dpair.1, dynPostOrder := dpair.2,
                    lamN := lamMax.num.toNat, lamD := lamMax.den })
      if (← IO.getEnv "RELCERT_DEBUG").isSome then
        IO.eprintln (s!"  [{mL.name}_L pair-stretch δ=εR/{lamMax}] " ++
          String.intercalate " " (firstPass.map (fun t => s!"{t.1}@λ={t.2.1}")))
      match gate seg strataMap winMax deltaL with
      | some lc => return (.cov, some lc)
      | none => pure ()
  -- existential mode choice (docs/CHOICE-SOUNDNESS.md; mechanized as `theorem3_of_coverX`,
  -- the emitted chosen sets replayed by the generic bridge).
  -- Reached only when no λ and no per-pairing stretch closed the cover with the old rule;
  -- tries the λ candidates in the same order as the old rule.
  if choiceOn && !admMods.isEmpty then
    for (lam, deltaL, segMap, strataMap) in choiceCands do
      let seg := fun q => (segMap.find? (·.1 == q)).map (·.2) |>.getD Seg.incon
      let bBudget := min (epsL / deltaL).ceil.toNat 256
      if singleStep && bBudget > 1 then continue
      let memo ← IO.mkRef ({} : Std.HashMap (String × Nat × Bool × Bool) Bool)
      let log ← IO.mkRef ([] : List String)
      let clog ← IO.mkRef ([] : List Choice.ChoiceEntryE)
      let cx := mkCtx seg
      let mut allOk := true
      for mR in admMods do
        if allOk then
          if !(← choiceCover s cnt maxQ maxSmt deadline coord cx memo log clog [] mR.name bBudget true true) then
            allOk := false
      if allOk then
        IO.eprintln s!"  [choice] {p.name} {mL.name}_L λ={lam} B={bBudget}: certified by choice cover"
        let entries ← clog.get
        choiceLog.modify (· ++ entries.map (fun e => { e with mL := mL.name }))
        let lines ← log.get
        for line in lines do
          IO.eprintln s!"    [choice] {line}"
        let flagRows : List ModeFlagsE := p.R.modes.map (fun m =>
          { name := m.name, jointOK := seg m.name == Seg.pass,
            dynPre := repoDynPreOK m.name, dynPost := repoDynPostOK m.name })
        let lc : LeftCoverE :=
          { mL := mL.name, lamQ := (windowOf lam epsL epsR).1, bBudget := bBudget, flags := flagRows,
            admissible := admMods.map (·.name), strata := strataMap }
        return (.cov, some lc)
  return ((if sawIncon then .incon else .nocov), none)

/-- Core cover, parameterized by a query counter/budget (`throw`s on overrun). -/
def certifyWithData (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (p : PProblem) : IO (Outcome × Option CoverEmitE) := do
  progressLog.set []
  choiceLog.set []
  prelandLog.set []
  -- the joint variable list: the left variables, then any right-only ones (a right-only
  -- variable is held fixed on the left; `Trusted/JointVars.lean`)
  let vars := p.jointVars
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
  -- RELCERT_IMPLIED_CUT=1 widens the candidate set (L1 implied-contraction atoms, L2
  -- closures; `checkedCutX`); off by default, see `impliedCutsOn`.
  let implied ← impliedCutsOn
  let dbg := (← IO.getEnv "RELCERT_DEBUG").isSome
  -- one mode's cut: `(domain narrowing, kept-atom count, extended atoms)`; the
  -- `[cut]` line counts every kept atom (legacy format), `[cut-x]` lists the
  -- extended ones (implied mode only)
  let cutOf (side : Side) (mM : PMode) : IO (IForm n × Nat) := do
    if noCut then pure (IForm.tt, 0)
    else if implied then do
      let (c, xs) ← checkedCutX s cnt maxQ maxSmt deadline vars n coord side mM
      if dbg then
        let sd := match side with | Side.L => "L" | Side.R => "R" | _ => "?"
        for x in xs do
          if x.kind != CutKind.guardConj then
            let gv := if x.given.isEmpty then "" else
              " given=[" ++ String.intercalate "; " (x.given.map ppForm) ++ "]"
            IO.eprintln s!"  [cut-x] {sd}.{mM.name}: {ppForm x.atom} kind={x.kind.tag} entry={x.entry.tag} route={x.route.tag}{gv}"
      pure (c, xs.length)
    else do
      let (c, kept) ← checkedCut s cnt maxQ maxSmt deadline vars n coord side mM
      pure (c, kept.length)
  let mut cutMapL : List (String × IForm n) := []
  for mM in p.L.modes do
    let (c, k) ← cutOf Side.L mM
    if dbg then
      IO.eprintln s!"  [cut] L.{mM.name}: {k} conjunct(s)"
    cutMapL := cutMapL ++ [(mM.name, c)]
  let mut cutMapR : List (String × IForm n) := []
  for mM in p.R.modes do
    let (c, k) ← cutOf Side.R mM
    if dbg then
      IO.eprintln s!"  [cut] R.{mM.name}: {k} conjunct(s)"
    cutMapR := cutMapR ++ [(mM.name, c)]
  let cutOfL := fun (nm : String) => (cutMapL.find? (·.1 == nm)).map (·.2) |>.getD IForm.tt
  let cutOfR := fun (nm : String) => (cutMapR.find? (·.1 == nm)).map (·.2) |>.getD IForm.tt
  -- FIX 3: non-connection pruning (Definition 6). mL- AND λ-independent (right flow + right guards only),
  -- so computed ONCE for the whole problem. Edge `mR → tgt` pruned iff BOTH nonconn checks are
  -- definitive Z3 UNSAT (`nonConnPrune`); any other verdict keeps it. Drop-only-on-UNSAT ⟹ sound.
  -- RELCERT_NO_PRUNE=1 disables non-connection pruning entirely (ablation switch, the
  -- counter-run of the suite_v2 matrix: every declared edge stays in the cover's
  -- all-successors obligation; the two pruning queries are not issued).
  let noPrune := (← IO.getEnv "RELCERT_NO_PRUNE").isSome
  let mut prunedPairs : List (String × String) := []
  if !noPrune then
    for mR in p.R.modes do
      for tgt in mR.next do
        match p.R.modes.find? (·.name == tgt) with
        | none => pure ()
        | some mSuc =>
            if ← nonConnPrune s cnt maxQ maxSmt deadline vars n coord (cutOfR mR.name) mR mSuc then
              prunedPairs := prunedPairs ++ [(mR.name, tgt)]
  -- the pruned edges are part of the certificate (`CoverEmitE.pruned`); say so on every
  -- run, not only under RELCERT_DEBUG, so a reader can see which declared edges the
  -- non-connection certificates removed (or that pruning was switched off)
  -- (stderr, like the other `[...]` diagnostics: the `--emit-*` doors print literals
  -- on stdout)
  if noPrune then
    IO.eprintln s!"  [prune] {p.name}: disabled (RELCERT_NO_PRUNE)"
  else if !prunedPairs.isEmpty then
    IO.eprintln s!"  [prune] {p.name}: {prunedPairs.map (fun e => s!"{e.1}->{e.2}")}"
  else if (← IO.getEnv "RELCERT_DEBUG").isSome then
    IO.eprintln s!"  [prune] {p.name}: []"
  let prunedOf := fun (src tgt : String) => prunedPairs.contains (src, tgt)
  let mut sawIncon := false
  let mut covers : List LeftCoverE := []
  for mL in p.L.modes do
    -- invariant for this left mode (key = mode name, else first)
    -- strict: every left mode must carry its own invariant row (the old head-of-list
    -- fallback silently certified the FIRST row's formula for unmatched modes — an
    -- accept-and-weaken route at key resolution)
    let invF := (p.invariants.find? (·.1 == mL.name)).map Prod.snd
    match invF with
    | none => return (.error s!"no invariant for left mode {mL.name}", none)
    | some f =>
        match invComponents vars n f with
        | none => return (.error s!"unlowerable invariant for mode {mL.name}", none)
        | some comps =>
            -- DIAGNOSTIC `RELCERT_OPREGION=1` (no effect on the verdict): does the invariant row
            -- admit a start with the left in its guard and both sides in their domains, but the
            -- right state in NO right guard? Such starts lie outside the right's operating
            -- region and are excluded by Theorem 3's premise. One query per left mode.
            if (← IO.getEnv "RELCERT_OPREGION").isSome then
              let low := fun (side : Side) (f : PForm) => (lowerF vars n side f).getD IForm.tt
              let inv : IForm n := comps.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) IForm.tt
              let noGuardR : IForm n := p.R.modes.foldl
                (fun d m => IForm.and d (IForm.neg (low Side.R m.guard))) IForm.tt
              let domR : IForm n := (p.R.modes.head?.map (fun m => low Side.R m.evolve)).getD IForm.tt
              let q : IForm n := IForm.and (IForm.and (IForm.and (IForm.and
                (low Side.L mL.guard) (low Side.L mL.evolve)) domR) inv) noGuardR
              let lowersAll := p.R.modes.all (fun m => (lowerF vars n Side.R m.guard).isSome)
                && (lowerF vars n Side.L mL.guard).isSome
              -- an unlowerable guard would default to `tt` and make the query vacuous: report it
              let covered ← if lowersAll then probeUnsat s cnt maxQ maxSmt deadline coord q
                else pure false
              IO.eprintln s!"  [opregion] {p.name} {mL.name}_L: {if covered then "every admitted start in some right guard" else "starts OUTSIDE every right guard (sat or unknown)"}"
            match ← coverMode s cnt maxQ maxSmt deadline p vars n coord comps prunedOf
                (cutOfL mL.name) cutOfR epsL epsR lmin lmax mL
                ((invStrictFlags vars n f).getD []) with
            | (.cov, some lc) => covers := covers ++ [lc]
            | (.cov, none) => pure ()      -- unreachable: .cov always carries data
            | (.incon, _) => sawIncon := true
            | (.nocov, _) => return (.declined, none)   -- definitive uncovered ⟹ sound DECLINE
  if sawIncon then return (.error "inconclusive Z3 verdict on a candidate route", none)
  -- Every left mode must have contributed a cover. Two ways that could silently fail
  -- otherwise, both of which would still have returned `.certified`: an empty
  -- `p.L.modes` never enters the loop (the parser rejects that — `validateSystem`'s
  -- "no modes" — so this is defence in depth, not a live hole), and the `(.cov, none)`
  -- branch above skips the append. Counting is the same discipline the verdict runners
  -- use (`Verdicts/Coverage.lean`): a pass that did less work than it owes must not
  -- look like one that did it all. Strictly conservative — it can only turn a
  -- `CERTIFIED` into an `ERROR`, never the reverse.
  else if covers.length != p.L.modes.length then
    return (.error s!"internal: {covers.length} cover(s) for {p.L.modes.length} left \
mode(s) — a mode was certified without recording one", none)
  -- GUARD (`docs/STUTTER.md`): a stretch-0 pairing (the stutter segment) is backed only for a
  -- problem that opts in with `stutter = true` (`Emitted.timeOK` admits `lamN = 0` exactly
  -- then); a window stretch is always positive. Defence in depth: `lambdaCandidates` never
  -- offers `0` without the key. Strictly conservative (CERTIFIED to ERROR, never the reverse).
  else if covers.any (fun lc => lc.lamQ ≤ 0 || (!p.stutter && lc.strata.any (·.lamN == 0))) then
    return (.error "internal: a stretch-0 pairing (or window) without `stutter = true`", none)
  -- GUARD (`docs/PRELANDING.md`): a pre-landing right-only node is backed only for a problem
  -- that opts in with `prelanding = true` (`Emitted.plOK` admits a nonempty record exactly
  -- then). Defence in depth: `coverMode` finds none without the key. Strictly conservative.
  else if !p.prelanding && !(← prelandLog.get).isEmpty then
    return (.error "internal: a pre-landing right-only node without `prelanding = true`", none)
  else return (.certified, some { name := p.name, pruned := prunedPairs, covers := covers })

/-- Core cover (verdict only). -/
def certifyCore (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (p : PProblem) : IO Outcome :=
  (·.1) <$> certifyWithData s cnt maxQ maxSmt deadline p

/-- **In-process oracle entry.** Certify problem `p` on a warm session `s`. No shelling.
A deterministic query budget (`RELCERT_MAX_QUERIES`, default 20000) bounds every call: a
candidate whose exhaustive search exceeds it ⟹ `error "query budget exceeded"` (never a
verdict, never a hang) — the same input always hits the same count. -/
def certify (s : Z3Session) (p : PProblem) : IO Outcome := do
  let cnt ← IO.mkRef 0
  let maxQ := (← IO.getEnv "RELCERT_MAX_QUERIES").bind String.toNat? |>.getD 20000
  let budgetMs := (← IO.getEnv "RELCERT_TIME_BUDGET_MS").bind String.toNat? |>.getD 300000
  let maxSmt := (← IO.getEnv "RELCERT_MAX_SMT").bind String.toNat? |>.getD 200000
  let deadline := (← IO.monoMsNow) + budgetMs
  try certifyCore s cnt maxQ maxSmt deadline p
  catch e => return .error s!"budget exceeded ({e})"

/-- The `--emit-cover` printer: the successful cover as a Lean literal (EmitIR
pattern — the drift test re-runs the search and compares). Anonymous-constructor
form, consumable against `Checker/CoverEmit.lean`. -/
def emitCoverE (defname : String) (c : CoverEmitE) : String :=
  let fl := fun (f : ModeFlagsE) =>
    s!"⟨\"{f.name}\", {f.jointOK}, {f.dynPre}, {f.dynPost}⟩"
  let ps := fun (x : PairStrataE) =>
    s!"⟨\"{x.mR}\", {repr x.order}, {repr x.dynPreOrder}, {repr x.dynPostOrder}, {x.lamN}, {x.lamD}⟩"
  let lc := fun (l : LeftCoverE) =>
    s!"⟨\"{l.mL}\", ({l.lamQ.num} : ℚ) / {l.lamQ.den}, {l.bBudget}, [" ++
      String.intercalate ", " (l.flags.map fl) ++ "], " ++ reprStr l.admissible ++ ", [" ++
      String.intercalate ", " (l.strata.map ps) ++ "]⟩"
  s!"def {defname} : CoverEmitE :=\n  ⟨\"{c.name}\", {reprStr c.pruned}, [\n    " ++
    String.intercalate ",\n    " (c.covers.map lc) ++ "]⟩"

/-- `--emit-cover` entry: run the search, print the cover literal. -/
def emitCoverFile (cfg : Z3Config) (path defname : String) : IO Unit := do
  let txt ← IO.FS.readFile path
  match parseProblemE txt with
  | .error e => IO.eprintln s!"ERROR: parse: {e}"; IO.Process.exit 1
  | .ok p =>
      match ← Z3Session.start cfg with
      | .error e => IO.eprintln s!"ERROR: z3: {e}"; IO.Process.exit 1
      | .ok s =>
          let cnt ← IO.mkRef 0
          let maxQ := (← IO.getEnv "RELCERT_MAX_QUERIES").bind String.toNat? |>.getD 20000
          let budgetMs := (← IO.getEnv "RELCERT_TIME_BUDGET_MS").bind String.toNat? |>.getD 300000
          let maxSmt := (← IO.getEnv "RELCERT_MAX_SMT").bind String.toNat? |>.getD 200000
          let deadline := (← IO.monoMsNow) + budgetMs
          let r ← try certifyWithData s cnt maxQ maxSmt deadline p
            catch e => pure (.error s!"budget exceeded ({e})", none)
          s.close
          match r with
          | (.certified, some c) =>
              IO.println (emitCoverE defname c)
              match ← IO.getEnv "RELCERT_PROGRESS_OUT" with
              | some out =>
                  let certs ← progressLog.get
                  IO.FS.writeFile out ("import RelCertifier.Trusted.ProgressEmit\n\n" ++
                    "namespace RelCertifier.Progress\n\n" ++
                    Progress.emitProgressE (defname ++ "_progress") ⟨p.name, certs⟩ ++
                    "\n\nend RelCertifier.Progress\n")
              | none => pure ()
              match ← IO.getEnv "RELCERT_PRELANDING_OUT" with
              | some out =>
                  let nodes ← prelandLog.get
                  IO.FS.writeFile out ("import RelCertifier.Trusted.PrelandEmit\n\n" ++
                    "namespace RelCertifier.Preland\n\n" ++
                    Preland.emitPrelandE (defname ++ "_prelanding") ⟨p.name, nodes⟩ ++
                    "\n\nend RelCertifier.Preland\n")
              | none => pure ()
              match ← IO.getEnv "RELCERT_CHOICE_OUT" with
              | some out =>
                  let entries ← choiceLog.get
                  IO.FS.writeFile out ("import RelCertifier.Trusted.ChoiceEmit\n\n" ++
                    "namespace RelCertifier.Choice\n\n" ++
                    Choice.emitChoiceE (defname ++ "_choice") ⟨p.name, entries⟩ ++
                    "\n\nend RelCertifier.Choice\n")
              | none => pure ()
          | (o, _) => IO.eprintln s!"ERROR: not certified: {o.tag}"; IO.Process.exit 1

/-- R-side face terms of an evolve conjunction (safe-side `g ≤ 0` per comparison). -/
def evolveFacesR (vars : List String) (n : ℕ) : PForm → Option (List (ITerm n))
  | .tt => some []
  | .cmp op a b =>
      if op == "<=" || op == "<" then do
        let ea ← lowerE vars n Side.R a
        let eb ← lowerE vars n Side.R b
        some [ITerm.bin .sub ea eb]
      else if op == ">=" || op == ">" then do
        let ea ← lowerE vars n Side.R a
        let eb ← lowerE vars n Side.R b
        some [ITerm.bin .sub eb ea]
      else none
  | .and x y => do
      let lx ← evolveFacesR vars n x
      let ly ← evolveFacesR vars n y
      some (lx ++ ly)
  | _ => none

/-- **R6 viability check**: per right mode, per evolve-box face, the STRICT inward
query — `flowQueryStrict` with the left frozen (`fL = 0`, λ = 1) over the mode's own
evolve box: `UNSAT(evolve ∧ face = 0 ∧ face-Lie ≥ 0)`. All faces UNSAT ⟹ the mode's
flows exist and stay in the box for any duration (`box_viability`). Declines honestly
on equilibrium-on-face and integrator (growth) faces — those take the bounded-time
variant (docs/history/COVER-AUDIT.md R6) or a named per-mode hypothesis. Used only by
`--emit-viability`. -/
def checkViability (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String) (mR : PMode) : IO Bool := do
  -- a strict evolve atom lowers to its closure face: never pass on a vacuous face probe
  if !evolveAllNonstrict mR.evolve then return false
  match evolveFacesR vars n mR.evolve, lowerF vars n Side.R mR.evolve,
      dynOf vars n Side.R mR with
  | some faces, some box, some fR => do
      let mut allUnsat := true
      for g in faces do
        if allUnsat then
          let gdot := ilieDeriv g (fun _ => ITerm.rat 0) fR (.rat 1)
          let q := IForm.and box (IForm.and (IForm.cmp .eq g (.rat 0))
            (IForm.cmp .ge gdot (.rat 0)))
          let script := q.toScript coord
          if script.length > maxSmt then allUnsat := false
          else do
            cnt.modify (· + 1)
            if (← cnt.get) > maxQ then throw (IO.userError "query budget exceeded")
            if (← IO.monoMsNow) > deadline then throw (IO.userError "time budget exceeded")
            match ← s.check script with
            | .ok .unsat => pure ()
            | _ => allUnsat := false
      pure allUnsat
  | _, _, _ => pure false

/-- `--emit-viability`: per right mode, the all-faces-strict verdict, as a Lean literal. -/
def emitViabilityFile (cfg : Z3Config) (path defname : String) : IO Unit := do
  let txt ← IO.FS.readFile path
  match parseProblemE txt with
  | .error e => IO.eprintln s!"ERROR: parse: {e}"; IO.Process.exit 1
  | .ok p =>
      match ← Z3Session.start cfg with
      | .error e => IO.eprintln s!"ERROR: z3: {e}"; IO.Process.exit 1
      | .ok s =>
          let cnt ← IO.mkRef 0
          let vars := p.jointVars
          let n := vars.length
          let coord := fun (i : Fin n) => vars.getD i.val "v"
          let deadline := (← IO.monoMsNow) + 40000
          let mut rows : List String := []
          for mR in p.R.modes do
            let v ← try checkViability s cnt 5000 200000 deadline vars n coord mR
              catch _ => pure false
            rows := rows ++ [s!"(\"{mR.name}\", {v})"]
          s.close
          IO.println (s!"def {defname} : List (String × Bool) := [" ++
            String.intercalate ", " rows ++ "]")

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
