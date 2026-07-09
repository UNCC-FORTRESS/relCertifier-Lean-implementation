/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Runnable Stage-1 tool

Builds a relational flow obligation (from the Python `rover_position` benchmark),
computes the verified `lieDeriv` (via the IR mirror, pinned to it by
`ilieDeriv_toHost`), emits SMT-LIB for the flow query `domain ∧ ġ > 0`, calls Z3, and
reports certified / not. `unsat` is the only trusted verdict:
`unsat ⟹ flow_certified ⟹ the invariant component is preserved along the flow`.
-/
import RelCertifier.Smt
import RelCertifier.Oracle
import RelCertifier.Run

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
  -- λ=4: ġ = L_vx − 4·R_vx, vx∈[0.3,1] ⇒ ġ ≤ −0.2 < 0 ⇒ unsat (Python: PASS)
  let r1 ← runObligation "stop_safe_lam4" gRover fL_stop fR_safe (.rat 4)
              (domainBox (3/10) 1) Verdict.unsat
  -- λ=1: ġ = L_vx − R_vx, vx∈[0,1] ⇒ ġ can be +1 ⇒ sat (Python: FAIL, rate gap)
  let r2 ← runObligation "stop_safe_lam1" gRover fL_stop fR_safe (.rat 1)
              (domainBox 0 1) Verdict.sat
  IO.println ""
  if r1 && r2 then
    IO.println "✓ both verdicts match the Python relCertifier flow-certificate results"
  else do
    IO.println "✗ verdict mismatch"
    IO.Process.exit 1

/-- Stage-4 entry: with `input.txt` path args, run the end-to-end cover on each;
otherwise print the Stage-1 flow-certificate demo. -/
def main (args : List String) : IO Unit := do
  if args.isEmpty then demoStage1 else args.forM RelCertifier.Run.runFile
