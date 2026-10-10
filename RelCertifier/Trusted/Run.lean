/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The lowering: parsed IR → SMT-IR queries (TRUSTED: its semantics is part of the claim)

`lowerE`/`lowerF` turn the parser's string-variable expressions and formulas into the
SMT-IR over `Var n` (left/right copies of the joint variable list); `dynOf` builds a mode's
field, `invToG` an invariant component, `segParts`/`segPartsRO` the Lie derivative of a
component along a joint (λ-stretched) or right-only pairing, `strataDomIR` the
stratified-cut domain, `routeQueries` the three sound flow queries (routes A, B, C),
`lambdaCandidates` the λ grid, `succOf` the declared right successors. The certifier
(`Trusted/OracleAPI.lean`), the verdict runners and the kernel instances all build their
queries through these same functions; the kernel side quotes them by `rfl`, so a lowering
change is visible as a pin failure, but what the lowering MEANS is trusted (the hypothesis
contract: parser, lowering, printer, Z3, kernel).
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Core.QFrac
import RelCertifier.Trusted.Smt
import RelCertifier.Core.FlowCert

namespace RelCertifier.Run

open RelCertifier RelCertifier.Parse DL

/-- Decimal numeral → ℚ, THROUGH the kernel-fast `parseQ` (raw-fraction parser,
structural recursion): `parseRat s = (parseQ s).map (n/d)`. The old implementation went
through `String.splitOn`/`toNat?` (well-founded recursion) and mathlib ℚ arithmetic,
neither of which kernel-reduces — every downstream lowering fact (`lowerE` on numerals,
`lowerF`, `cutAtomG`) was rfl-opaque. Strictness delta: forms like ".5" (empty integer
part) are now rejected, as is surrounding whitespace (tokenizer output is clean — the
`Faithful` kernel certificates already consume the same payloads untrimmed). -/
def parseRat (s : String) : Option ℚ :=
  (parseQ s).map (fun q => (q.n : ℚ) / (q.d : ℚ))

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

def lowerE (vars : List String) (n : ℕ) (defSide : Side) : PExpr → Option (ITerm n)
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
def lowerF (vars : List String) (n : ℕ) (defSide : Side) : PForm → Option (IForm n)
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

/-! ## Flow queries for a sync pair -/

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

/-- The strict flow query `domain ∧ g = 0 ∧ ġ ≥ 0` for pair `(mL, mR)` at stretch `lam`
(route B alone; `Proofs/Encoding/ToolLevel` states its soundness. The certifier itself
uses `segParts` with all three `routeQueries`). -/
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

/-- Segment domain (the two evolve domains; not the guards, see below) and the syntactic `ġ` for component `g`
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

/-- The stratified-DC domain: the base narrowed by exactly the PROVEN components
(sequential differential cuts — the shared definition `checkSeg`/`checkDynRepo` iterate
and the kernel instances quote; why not mutual narrowing: `docs/history/COVER-AUDIT.md` R4). -/
def strataDomIR {n : ℕ} (comps : List (ITerm n)) (proven : List Nat)
    (base : IForm n) : IForm n :=
  proven.foldl (fun d j =>
    match comps[j]? with
    | some gj => IForm.and d (IForm.cmp .le gj (.rat 0))
    | none => d) base

/-- The three **sound** flow queries for `(domain, g, ġ)` — UNSAT of ANY certifies the
segment, each backed by a verified theorem:
* A `domain ∧ ġ>0`        — `flow_cert_sound` (`DI_nonstrict_domain`);
* B `domain ∧ g=0 ∧ ġ≥0`  — `flow_cert_sound_strict` (`DI_strict`);
* C `domain ∧ g≥0 ∧ ġ>0`  — `flow_cert_sound_superlevel` (`DI_nonstrict_superlevel`). -/
def routeQueries {n : ℕ} (domain : IForm n) (g gdot : ITerm n) : List (IForm n) :=
  [ IForm.and domain (IForm.cmp .gt gdot (.rat 0)),
    IForm.and domain (IForm.and (IForm.cmp .eq g (.rat 0)) (IForm.cmp .ge gdot (.rat 0))),
    IForm.and domain (IForm.and (IForm.cmp .ge g (.rat 0)) (IForm.cmp .gt gdot (.rat 0))) ]

/-! ## The cover search inputs -/

/-- λ candidates: `εR/εL` (the largest λ at which one right segment spans the left
residence) and the 21-point grid `λmin + i·(λmax − λmin)/20`, kept inside
`[λmin, λmax]`, duplicates removed. -/
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

end RelCertifier.Run
