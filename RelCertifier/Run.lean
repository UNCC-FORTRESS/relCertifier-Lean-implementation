/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The end-to-end runner (Stage-4)

Parses `input.txt`, lowers each candidate sync pair into the VERIFIED strict flow
query (`flowQueryStrict`, pinned to `lieDeriv` via the `Smt` IR bridge), discharges it
with Z3, and runs a sound single-sync cover: a left mode is covered when some right mode
+ time-stretch λ ∈ [λmin, λmax] both flow-certifies (trusted Z3 UNSAT) and closes the
left residence in one segment (`εR/λ ≥ εL`). This is the `Covered` self-loop witness —
the right resides in one flow-certified mode for the whole left residence, invariant
preserved throughout by `flow_cert_sound_strict` (`BoxLe`, time-unbounded).

Sound and one-sided: only a trusted UNSAT certifies; anything else declines. A benchmark
needing multi-segment covers or edge pruning is reported `declined` (not unsound) — the
verified guarantee is that every reported `certified` is backed by `flow_cert_sound_strict`.
-/
import RelCertifier.Parse
import RelCertifier.Smt
import RelCertifier.FlowCert

namespace RelCertifier.Run

open RelCertifier RelCertifier.Parse DL

/-- Parse a decimal literal to `ℚ` (exact). -/
def parseRat (s : String) : Option ℚ :=
  let s := Parse.tr s
  let neg := s.startsWith "-"
  let s := if neg then Parse.dr s 1 else s
  let mk (v : ℚ) := if neg then -v else v
  match s.splitOn "." with
  | [i] => (if i.isEmpty then some 0 else i.toNat?).map (fun n => mk (n : ℚ))
  | [i, f] =>
      let ip : ℚ := if i.isEmpty then 0 else (i.toNat?.getD 0 : ℚ)
      match f.toNat? with
      | some fp => some (mk (ip + (fp : ℚ) / (10 : ℚ) ^ f.length))
      | none => none
  | _ => none

/-! ## Lowering: PExpr/PForm (string vars) → Smt IR over `Var n` -/

/-- Resolve a variable name to a joint `Var n`. `L_x`/`R_x` fix the side; a bare `x`
uses `defSide` (the current program's side). -/
def resolveVar (vars : List String) (n : ℕ) (defSide : Side) (name : String) : Option (Var n) :=
  let (side, base) :=
    if name.startsWith "L_" then (Side.L, Parse.dr name 2)
    else if name.startsWith "R_" then (Side.R, Parse.dr name 2)
    else (defSide, name)
  match vars.findIdx? (· == base) with
  | some i => if h : i < n then some (side, ⟨i, h⟩) else none
  | none => none

partial def lowerE (vars : List String) (n : ℕ) (defSide : Side) : PExpr → Option (ITerm n)
  | .num s => (parseRat s).map ITerm.rat
  | .var v => (resolveVar vars n defSide v).map ITerm.var
  | .neg a => (lowerE vars n defSide a).map (fun t => ITerm.bin .sub (.rat 0) t)
  | .bin op a b => do
      let ea ← lowerE vars n defSide a
      let eb ← lowerE vars n defSide b
      match op with
      | "+" => some (ITerm.bin .add ea eb)
      | "-" => some (ITerm.bin .sub ea eb)
      | "*" => some (ITerm.bin .mul ea eb)
      | "/" =>
          -- AOp has no division; fold a constant `c₁/c₂` into a rational literal
          match ea, eb with
          | .rat x, .rat y => if y == 0 then none else some (.rat (x / y))
          | _, _ => none
      | _   => none

/-- Lower a formula to the Smt IR (conjunctions only; comparisons kept as-is). -/
partial def lowerF (vars : List String) (n : ℕ) (defSide : Side) : PForm → Option (IForm n)
  | .tt => some IForm.tt
  | .cmp op a b => do
      let ea ← lowerE vars n defSide a
      let eb ← lowerE vars n defSide b
      let c ← match op with
        | "<=" => some CompOp.le | ">=" => some CompOp.ge
        | "<"  => some CompOp.lt | ">"  => some CompOp.gt
        | "="  => some CompOp.eq | _ => none
      some (IForm.cmp c ea eb)
  | .and x y => do let fx ← lowerF vars n defSide x; let fy ← lowerF vars n defSide y
                   some (IForm.and fx fy)
  | .or _ _ => none    -- disjunctive domains out of scope
  | .not _ => none

/-! ## Build the strict flow query IR for a sync pair -/

/-- The invariant's safe-side term `g` (from `L_v ≤ R_v + d` style atoms): the parser
gives the invariant as `lhs ≤ rhs`; `g := lhs − rhs`. Only the first `≤`/`<` atom is used
(the primary offset component). -/
def invToG (vars : List String) (n : ℕ) : PForm → Option (ITerm n)
  | .cmp op a b =>
      if op == "<=" || op == "<" then do
        let ea ← lowerE vars n Side.L a
        let eb ← lowerE vars n Side.L b
        some (ITerm.bin .sub ea eb)
      else if op == ">=" || op == ">" then do
        let ea ← lowerE vars n Side.L a
        let eb ← lowerE vars n Side.L b
        some (ITerm.bin .sub eb ea)
      else none
  | .and x _ => invToG vars n x   -- primary component
  | _ => none

/-- Dynamics of a mode as `Fin n → ITerm n`. **Total-or-fail**: a variable with NO ode
entry has derivative `0` (correct — it is held fixed), but a variable whose ode is PRESENT
yet fails to lower returns `none` — never a silent `0`. A silent zero would build the Lie
derivative of the WRONG field and could falsely certify; propagating `none` makes the
segment inconclusive ⟹ ERROR, never a verdict. -/
def dynOf (vars : List String) (n : ℕ) (side : Side) (m : PMode) : Option (Fin n → ITerm n) := do
  let terms ← (List.finRange n).mapM (fun i =>
    match m.odes.find? (fun p => p.1 == vars.getD i.val "") with
    | some (_, e) => lowerE vars n side e        -- present ode must lower, else fail
    | none => some (ITerm.rat 0))                -- absent ⟹ derivative 0 (held fixed)
  some (fun i => terms.getD i.val (.rat 0))

/-- The strict flow query `domain ∧ g = 0 ∧ ġ ≥ 0` for pair `(mL, mR)` at stretch `lam`. -/
def flowQueryIR (vars : List String) (n : ℕ) (g : ITerm n) (mL mR : PMode) (lam : ℚ) :
    Option (IForm n) := do
  -- SOUND domain = the EVOLUTION domains only (hold throughout the ODE segment). NOT the
  -- mode guards: a guard is the entry/transition condition, which need not hold throughout
  -- the residence, so conjoining it narrows the flow certificate below the reachable flow.
  let domL  ← lowerF vars n Side.L mL.evolve
  let domR  ← lowerF vars n Side.R mR.evolve
  let fL ← dynOf vars n Side.L mL
  let fR ← dynOf vars n Side.R mR
  let gdot := ilieDeriv g fL fR (.rat lam)
  let domain := IForm.and domL domR
  some (IForm.and domain
    (IForm.and (IForm.cmp .eq g (.rat 0)) (IForm.cmp .ge gdot (.rat 0))))

/-- Segment domain (evolves ∧ guards, both sides) and the syntactic `ġ` for component `g`
along `(mL, mR)` at stretch `lam`. Returns `none` if any part fails to lower. -/
def segParts (vars : List String) (n : ℕ) (g : ITerm n) (mL mR : PMode) (lam : ℚ) :
    Option (IForm n × ITerm n) := do
  -- SOUND domain: the EVOLUTION domains (hold throughout the ODE segment), NOT the mode
  -- guards. A guard is the ENTRY/transition condition — it need not hold throughout the
  -- residence (e.g. a Return mode entered at θ≥0.7 flows to θ<0.7), so conjoining it would
  -- narrow the flow certificate below the reachable flow and could FALSELY certify.
  let domL  ← lowerF vars n Side.L mL.evolve
  let domR  ← lowerF vars n Side.R mR.evolve
  let fL ← dynOf vars n Side.L mL
  let fR ← dynOf vars n Side.R mR
  let gdot := ilieDeriv g fL fR (.rat lam)
  some (IForm.and domL domR, gdot)

/-- **FIX 4: right-only segment parts** (`(ρ_L,ρ_R)=(0,1)`). Same domain as `segParts`
(`evolveL ∧ evolveR`), but the Lie derivative freezes the left (`fL = 0`) and leaves the right
unstretched (`λ = 1`): `ġ = Σ ∂g/∂Rᵢ · fRᵢ`. UNSAT of a `routeQueries` certifies that the
invariant is preserved while the left is frozen and only the right evolves. -/
def segPartsRO (vars : List String) (n : ℕ) (g : ITerm n) (mL mR : PMode) :
    Option (IForm n × ITerm n) := do
  let domL  ← lowerF vars n Side.L mL.evolve
  let domR  ← lowerF vars n Side.R mR.evolve
  let fR ← dynOf vars n Side.R mR
  let gdot := ilieDeriv g (fun _ => ITerm.rat 0) fR (.rat 1)
  some (IForm.and domL domR, gdot)

/-- The three **sound** flow queries for `(domain, g, ġ)` — UNSAT of ANY certifies the
segment, each backed by a verified theorem:
* A `domain ∧ ġ>0`        — `flow_cert_sound` (`DI_nonstrict_domain`);
* B `domain ∧ g=0 ∧ ġ≥0`  — `flow_cert_sound_strict` (`DI_strict`);
* C `domain ∧ g≥0 ∧ ġ>0`  — `flow_cert_sound_superlevel` (`DI_nonstrict_superlevel`). -/
def routeQueries {n : ℕ} (domain : IForm n) (g gdot : ITerm n) : List (IForm n) :=
  [ IForm.and domain (IForm.cmp .gt gdot (.rat 0)),
    IForm.and domain (IForm.and (IForm.cmp .eq g (.rat 0)) (IForm.cmp .ge gdot (.rat 0))),
    IForm.and domain (IForm.and (IForm.cmp .ge g (.rat 0)) (IForm.cmp .gt gdot (.rat 0))) ]

/-! ## Z3 -/

def z3Unsat (script : String) : IO Bool := do
  let tmp := s!"/tmp/relcert_run_{script.length}_{script.hash}.smt2"
  IO.FS.writeFile tmp script
  let out ← IO.Process.output { cmd := "z3", args := #["-T:5", tmp] }
  pure ((Parse.tr out.stdout).startsWith "unsat")

/-! ## The cover -/

/-- λ candidates: `λmin` and `εR/εL` (the largest λ that still single-sync-covers),
clamped to `[λmin, λmax]`. -/
def lambdaCandidates (lmin lmax epsL epsR : ℚ) : List ℚ :=
  let cover := if epsL == 0 then lmax else epsR / epsL
  let step := (lmax - lmin) / 20
  -- DENSE deterministic grid (20 steps) to test whether declines are a lambda-search limit.
  (cover :: (List.range 21).map (fun i => lmin + (i : ℚ) * step)).filterMap
    (fun l => if lmin ≤ l ∧ l ≤ lmax then some l else none) |>.eraseDups

/-- Declared right successors of `qR` (mode names). -/
def succOf (p : PProblem) (qR : String) : List String :=
  match p.R.modes.find? (fun m => m.name == qR) with
  | some m => m.next
  | none => []

/-- The multi-segment all-successors cover (the `Covered` relation, run). From `(qR, B)`
with `B` the remaining left-residence budget: the current segment must flow-certify
(`flowOK`); it consumes `δL`; if budget remains, EVERY declared successor (plus the
self-loop `qR`) must recursively cover. Budget strictly decreases (`δL>0`), so `fuel`
bounds the depth. -/
partial def dfsCover (flowOK : String → Bool) (succ : String → List String)
    (deltaL : ℚ) (f : Nat) (qR : String) (B : ℚ) : Bool :=
  if B ≤ 0 then true
  else if f == 0 then false
  else if !flowOK qR then false
  else
    let B' := B - deltaL
    if B' ≤ 0 then true
    else (qR :: succ qR).all (fun q' => dfsCover flowOK succ deltaL (f-1) q' B')

/-- Cover a left mode: try each λ candidate and each admissible start right mode; covered
if some (start, λ) yields a full all-successors cover. Precomputes `flowOK` per right mode
(one Z3 flow query each, cached). -/
def coverLeftMode (p : PProblem) (vars : List String) (n : ℕ)
    (epsL epsR lmin lmax : ℚ) (mL : PMode) : IO (Option (String × ℚ)) := do
  let invF := (p.invariants.find? (fun kv => kv.1 == mL.name)).map Prod.snd
    |>.orElse (fun _ => (p.invariants.head?).map Prod.snd)
  match invF.bind (invToG vars n) with
  | none => pure none
  | some g =>
    for lam in lambdaCandidates lmin lmax epsL epsR do
      let deltaL := if lam == 0 then epsR else epsR / lam
      if deltaL ≤ 0 then continue
      -- cache flow-cert per right mode at this λ
      let mut flowMap : List (String × Bool) := []
      for mR in p.R.modes do
        let ok ← match flowQueryIR vars n g mL mR lam with
          | some q => z3Unsat (q.toScript (fun i => vars.getD i.val "v"))
          | none => pure false
        flowMap := flowMap ++ [(mR.name, ok)]
      let flowOK := fun q => (flowMap.find? (fun p => p.1 == q)).map Prod.snd |>.getD false
      let fuel := (epsL / deltaL).ceil.toNat + 2
      -- try each right mode as an admissible start; the right chooses its response
      match p.R.modes.find? (fun mR => dfsCover flowOK (succOf p) deltaL fuel mR.name epsL) with
      | some mR => return some (mR.name, lam)
      | none => pure ()
    pure none

/-- Run a benchmark: `VERIFIED` iff every left mode is covered by the all-successors cover. -/
def runProblem (p : PProblem) : IO (Bool × List String) := do
  let vars := p.L.stateVars
  let n := vars.length
  let epsL := (parseRat p.L.epsilon).getD 1
  let epsR := (parseRat p.R.epsilon).getD 1
  let lmin := (parseRat p.lambdaMin).getD 1
  let lmax := (parseRat p.lambdaMax).getD 1
  let mut notes : List String := []
  let mut ok := true
  for mL in p.L.modes do
    match ← coverLeftMode p vars n epsL epsR lmin lmax mL with
    | some (qR, lam) => notes := notes ++ [s!"{mL.name}_L ✓ start {qR}_R λ={lam}"]
    | none => notes := notes ++ [s!"{mL.name}_L ✗ uncovered"]; ok := false
  pure (ok, notes)

def runFile (path : String) : IO Unit := do
  let txt ← IO.FS.readFile path
  match parseProblemE txt with
  | .error e => IO.println s!"{path}: UNPARSED [{e}]"
  | .ok p =>
    let (ok, notes) ← runProblem p
    let verdict := if ok then "VERIFIED" else "declined"
    IO.println s!"{p.name}: {verdict}"
    for nt in notes do IO.println s!"    {nt}"

end RelCertifier.Run
