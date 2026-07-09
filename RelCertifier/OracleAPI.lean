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
def checkSeg (s : Z3Session) (vars : List String) (n : ℕ) (coord : Fin n → String)
    (comps : List (ITerm n)) (mL mR : PMode) (lam : ℚ) : IO Seg := do
  let mut allPass := true
  for g in comps do
    match flowQueryIR vars n g mL mR lam with
    | none => return Seg.incon                     -- couldn't build the query
    | some q =>
        match ← s.check (q.toScript coord) with
        | .error _ => return Seg.incon
        | .ok .unknown => return Seg.incon
        | .ok .sat => allPass := false             -- definitive fail on this component
        | .ok .unsat => pure ()
  return (if allPass then Seg.pass else Seg.fail)

/-- The multi-segment all-successors cover, three-valued. `seg qR` is the precomputed
status of residing in `qR`. `nocov` dominates `incon` (a definitely-uncovered successor
fails all-successors regardless of inconclusive siblings). -/
partial def dfsCov3 (seg : String → Seg) (succ : String → List String) (deltaL : ℚ)
    (f : Nat) (qR : String) (B : ℚ) : Cov3 :=
  if B ≤ 0 then .cov
  else if f == 0 then .nocov
  else match seg qR with
    | .fail => .nocov
    | .incon => .incon
    | .pass =>
        let B' := B - deltaL
        if B' ≤ 0 then .cov
        else
          let rs := (qR :: succ qR).map (fun q' => dfsCov3 seg succ deltaL (f-1) q' B')
          if rs.any (· == Cov3.nocov) then .nocov
          else if rs.any (· == Cov3.incon) then .incon
          else .cov

/-- Cover a single left mode: `cov` if some (start,λ) closes definitively; `incon` if none
close but a route was inconclusive; `nocov` if all routes are definitive fails. -/
def coverMode (s : Z3Session) (p : PProblem) (vars : List String) (n : ℕ)
    (coord : Fin n → String) (comps : List (ITerm n))
    (epsL epsR lmin lmax : ℚ) (mL : PMode) : IO Cov3 := do
  let mut sawIncon := false
  for lam in lambdaCandidates lmin lmax epsL epsR do
    let deltaL := if lam == 0 then epsR else epsR / lam
    if deltaL ≤ 0 then continue
    -- precompute per-right-mode segment status at this λ
    let mut segMap : List (String × Seg) := []
    for mR in p.R.modes do
      segMap := segMap ++ [(mR.name, ← checkSeg s vars n coord comps mL mR lam)]
    let seg := fun q => (segMap.find? (·.1 == q)).map (·.2) |>.getD Seg.incon
    let fuel := (epsL / deltaL).ceil.toNat + 2
    for mR in p.R.modes do
      match dfsCov3 seg (succOf p) deltaL fuel mR.name epsL with
      | .cov => return .cov
      | .incon => sawIncon := true
      | .nocov => pure ()
  return (if sawIncon then .incon else .nocov)

/-- **In-process oracle entry.** Certify problem `p` on a warm session `s`. No shelling. -/
def certify (s : Z3Session) (p : PProblem) : IO Outcome := do
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
            match ← coverMode s p vars n coord comps epsL epsR lmin lmax mL with
            | .cov => pure ()
            | .incon => sawIncon := true
            | .nocov => return .declined   -- definitive uncovered ⟹ sound DECLINE
  if sawIncon then return .error "inconclusive Z3 verdict on a candidate route"
  else return .certified

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
