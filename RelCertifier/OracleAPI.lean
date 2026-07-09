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
import RelCertifier.Z3
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

/-- Check one segment `(qL=mL, qR=mR, λ)`: `pass` iff EVERY component's strict flow query
is Z3-`unsat`; `fail` iff some component is definitively `sat`; `incon` on any Z3
error/`unknown` or unbuildable query. -/
def checkSeg (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat)
    (vars : List String) (n : ℕ) (coord : Fin n → String)
    (comps : List (ITerm n)) (mL mR : PMode) (lam : ℚ) : IO Seg := do
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

/-- Cover a single left mode: `cov` if some (start,λ) closes definitively; `incon` if none
close but a route was inconclusive; `nocov` if all routes are definitive fails. -/
def coverMode (s : Z3Session) (cnt : IO.Ref Nat) (maxQ maxSmt deadline : Nat) (p : PProblem)
    (vars : List String) (n : ℕ)
    (coord : Fin n → String) (comps : List (ITerm n))
    (epsL epsR lmin lmax : ℚ) (mL : PMode) : IO Cov3 := do
  let mut sawIncon := false
  for lam in lambdaCandidates lmin lmax epsL epsR do
    let deltaL := if lam == 0 then epsR else epsR / lam
    if deltaL ≤ 0 then continue
    -- precompute per-right-mode segment status at this λ
    let mut segMap : List (String × Seg) := []
    for mR in p.R.modes do
      segMap := segMap ++ [(mR.name, ← checkSeg s cnt maxQ maxSmt deadline vars n coord comps mL mR lam)]
    let seg := fun q => (segMap.find? (·.1 == q)).map (·.2) |>.getD Seg.incon
    if (← IO.getEnv "RELCERT_DEBUG").isSome then
      IO.eprintln (s!"  [{mL.name}_L λ={lam} #comps={comps.length}] " ++
        String.intercalate " " (segMap.map (fun p => s!"{p.1}={repr p.2}")))
    -- fuel = segments to fill εL, capped (a real cover uses few); memoized ⟹ bounded work
    let fuel := min ((epsL / deltaL).ceil.toNat + 2) 128
    let memo ← IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap (String × Nat) Cov3)
    for mR in p.R.modes do
      match ← dfsCov3 memo seg (succOf p) deltaL fuel mR.name epsL with
      | .cov => return .cov
      | .incon => sawIncon := true
      | .nocov => pure ()
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
  let mut sawIncon := false
  for mL in p.L.modes do
    -- invariant for this left mode (key = mode name, else first)
    let invF := (p.invariants.find? (·.1 == mL.name)).map Prod.snd
      |>.orElse (fun _ => (p.invariants.head?).map Prod.snd)
    match invF with
    | none => return .error s!"no invariant for left mode {mL.name}"
    | some f =>
        match invComponents vars n f with
        | none => return .error s!"unlowerable invariant for mode {mL.name}"
        | some comps =>
            match ← coverMode s cnt maxQ maxSmt deadline p vars n coord comps epsL epsR lmin lmax mL with
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
  let budgetMs := (← IO.getEnv "RELCERT_TIME_BUDGET_MS").bind String.toNat? |>.getD 20000
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
      match parseProblem txt with
      | none => return .error "unparsed input"
      | some p =>
          match ← Z3Session.start cfg with
          | .error e => return .error e
          | .ok s => let r ← certify s p; s.close; return r

end RelCertifier.Oracle
