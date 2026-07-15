/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Runnable Stage-1 tool

Builds a relational flow obligation (the `rover_position` benchmark),
computes the verified `lieDeriv` (via the IR mirror, pinned to it by
`ilieDeriv_toHost`), emits SMT-LIB for the flow query `domain ∧ ġ > 0`, calls Z3, and
reports certified / not. `unsat` is the only trusted verdict:
`unsat ⟹ flow_certified ⟹ the invariant component is preserved along the flow`.
-/
import RelCertifier.Smt
import RelCertifier.Oracle
import RelCertifier.Run
import RelCertifier.Z3
import RelCertifier.OracleAPI

open RelCertifier DL

/-- Coordinate names for the 2-D rover state: `px` (position), `vx` (velocity). -/
def coord : Fin 2 → String := fun i => if i = 0 then "px" else "vx"

def iL (i : Fin 2) : ITerm 2 := .var (Lv i)
def iR (i : Fin 2) : ITerm 2 := .var (Rv i)

/-- `L_px − R_px − 2`  (the invariant component `g ≤ 0`, offset `d = 2`). -/
def gRover : ITerm 2 := .bin .sub (.bin .sub (iL 0) (iR 0)) (.rat 2)

/-- Left dynamics `Stop_L`: `px' = L_vx`,  `vx' = −½·L_vx`. -/
def fL_stop : Fin 2 → ITerm 2 :=
  fun i => if i = 0 then iL 1 else .bin .mul (.rat (-1/2)) (iL 1)

/-- Right dynamics `Safe_R`: `px' = R_vx`,  `vx' = 0`. -/
def fR_safe : Fin 2 → ITerm 2 :=
  fun i => if i = 0 then iR 1 else .rat 0

/-- `lo ≤ t ≤ hi`. -/
def between (t : ITerm 2) (lo hi : ℚ) : IForm 2 :=
  .and (.cmp .ge t (.rat lo)) (.cmp .le t (.rat hi))

/-- Domain box: `px ∈ [0,15]` (both sides), `vx ∈ [vlo,vhi]` (both sides). -/
def domainBox (vlo vhi : ℚ) : IForm 2 :=
  .and (between (iL 0) 0 15)
    (.and (between (iR 0) 0 15)
      (.and (between (iL 1) vlo vhi) (between (iR 1) vlo vhi)))

/-- Parse a verdict string from Z3 stdout. -/
def parseVerdict (s : String) : Verdict :=
  let s := s.trim
  if s.startsWith "unsat" then .unsat
  else if s.startsWith "sat" then .sat
  else .unknown

def runObligation (name : String) (g : ITerm 2) (fL fR : Fin 2 → ITerm 2)
    (lam : ITerm 2) (domain : IForm 2) (expect : Verdict) : IO Bool := do
  let q := iflowQuery g fL fR lam domain
  let script := q.toScript coord
  let tmp := s!"/tmp/relcert_flow_{name}.smt2"
  IO.FS.writeFile tmp script
  let out ← IO.Process.output { cmd := "z3", args := #[tmp] }
  let v := parseVerdict out.stdout
  let tag := match v with
    | .unsat => "CERTIFIED  (unsat ⇒ ġ ≤ 0 on domain ⇒ invariant preserved, via flow_certified)"
    | .sat => "not certified (sat: ġ > 0 somewhere on domain)"
    | .unknown => s!"unknown ({out.stdout.trim})"
  IO.println s!"  [{name}]  ġ-query → z3: {repr v}"
  IO.println s!"      {tag}"
  pure (v == expect)

def demoStage1 : IO Unit := do
  IO.println "relCertifier-lean — Stage 1: verified flow certificate"
  IO.println "  invariant component g = L_px − R_px − 2   (g ≤ 0)"
  IO.println "  soundness: flow_certified = z3_unsat_sound + flow_cert_sound (dL-lean DI_nonstrict_domain)"
  IO.println "  UNSAT of  domain ∧ ġ>0  is the only trusted verdict"
  IO.println ""
  IO.println "rover_position  Stop_L / Safe_R :"
  -- λ=4: ġ = L_vx − 4·R_vx, vx∈[0.3,1] ⇒ ġ ≤ −0.2 < 0 ⇒ unsat (PASS)
  let r1 ← runObligation "stop_safe_lam4" gRover fL_stop fR_safe (.rat 4)
              (domainBox (3/10) 1) Verdict.unsat
  -- λ=1: ġ = L_vx − R_vx, vx∈[0,1] ⇒ ġ can be +1 ⇒ sat (FAIL, rate gap)
  let r2 ← runObligation "stop_safe_lam1" gRover fL_stop fR_safe (.rat 1)
              (domainBox 0 1) Verdict.sat
  IO.println ""
  if r1 && r2 then
    IO.println "✓ both verdicts match the expected flow-certificate results"
  else do
    IO.println "✗ verdict mismatch"
    IO.Process.exit 1

open RelCertifier.Oracle in
/-- Run the oracle over `paths` on ONE warm Z3 session; print `path: TAG (Δms)` per file
and an ERROR count. Exits non-zero if any ERROR (a trustworthy run has zero). -/
def runBatch (paths : List String) : IO Unit := do
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 2
  | .ok cfg =>
    IO.println s!"z3 = {cfg.binary}  (warm persistent session)"
    match ← Z3Session.start cfg with
    | .error e => IO.eprintln s!"ERROR: z3 session: {e}"; IO.Process.exit 2
    | .ok s =>
      let mut errs := 0
      for path in paths do
        let t0 ← IO.monoMsNow
        let oc ← try
            match RelCertifier.Parse.parseProblemE (← IO.FS.readFile path) with
            | .error e => pure (Outcome.error s!"parse: {e}")
            | .ok p => certify s p
          catch e => pure (Outcome.error s!"io: {e}")
        let dt := (← IO.monoMsNow) - t0
        let name := (path.splitOn "/").reverse.getD 1 path
        match oc with
        | .certified => IO.println s!"{name}: CERTIFIED ({dt}ms)"
        | .declined  => IO.println s!"{name}: DECLINED ({dt}ms)"
        | .error m   => errs := errs + 1; IO.println s!"{name}: ERROR [{m}] ({dt}ms)"
      s.close
      IO.println s!"errors={errs}"
      if errs > 0 then IO.Process.exit 1

/-- Entry: no args → Stage-1 demo; else run the oracle on each `input.txt` (warm). -/
def main (args : List String) : IO Unit := do
  if args.isEmpty then demoStage1 else runBatch args
