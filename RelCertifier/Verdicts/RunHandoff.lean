/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The handoff check: the cross-mode implication, per declared left transition

`runHandoffBench` builds, for one benchmark and every declared left transition `m' → m`
(self-loops included), the domain-conditioned handoff query of `Trusted/Handoff.lean`,

    UNSAT( φ_inv(m') ∧ evolve_{m'}(x_L) ∧ guard_m(x_L) ∧ evolve_R(x_R) ∧ ¬φ_inv(m) ),

prints it through the tool's own `toScript`, and reports Z3's verdict. The query is the
one the composition theorem's handoff hypothesis denotes (`ModeHandoff.handoff_of_unsat`
takes `z3solve (ihandoffQuery …).toHost = unsat`), so a green line is evidence about that
hypothesis and not about a lookalike.

Two callers: `relcert --handoff <input.txt>…` (per-benchmark report), and the suite_v2
handoff phase `VerdictsV2.runHandoffAllV2` of `--run-verdicts-v2`, which walks all 45
suite_v2 files and checks the total against the declared `expectedHandoffV2` and the
failure set against `expectedHandoffFailuresV2` (empty). A benchmark whose `next` lists do
not all resolve shows up as a per-benchmark count mismatch. A mode-independent invariant
(all rows identical) is reported as `vacuous`, and its queries are still issued and
counted.

On a failing transition the runner also prints a Z3 model of the query (the
countermodel), obtained from a one-shot `z3` process on the same script.
-/
import RelCertifier.Trusted.Handoff
import RelCertifier.Trusted.Z3
import RelCertifier.Verdicts.Coverage

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.Parse RelCertifier.Handoff

/-- What one benchmark's handoff check produced. -/
structure HandoffReport where
  bench       : String
  /-- Transitions the file declares (sum of `next` lengths). -/
  declared    : ℕ
  /-- Transitions actually checked (resolved pairs). -/
  checked     : ℕ
  passed      : ℕ
  /-- `(m', m)` pairs whose query was not `unsat` (with the verdict/detail). -/
  failing     : List ((ℕ × ℕ) × String)
  /-- Every invariant row is syntactically identical: all queries trivially unsat. -/
  vacuous     : Bool
  ms          : ℕ
  deriving Repr

/-- A Z3 model for `script` (which must be satisfiable), from a one-shot process. Used
only to document a failing transition; never consulted for a verdict. -/
def z3Model (cfg : Z3Config) (script : String) : IO String := do
  let tmp := s!"/tmp/relcert_handoff_model_{script.hash}.smt2"
  IO.FS.writeFile tmp (script ++ "(get-model)\n")
  let out ← IO.Process.output { cmd := cfg.binary, args := #[tmp] }
  pure (String.intercalate " "
    (((out.stdout.splitOn "\n").map Parse.tr).filter (· ≠ "")))

/-- Check every declared left transition of one benchmark. -/
def runHandoffBench (s : Z3Session) (cfg : Z3Config) (name : String) (p : PProblem)
    (verbose : Bool := true) : IO HandoffReport := do
  let t0 ← IO.monoMsNow
  let vars := p.L.stateVars
  let n := vars.length
  let coord := fun (i : Fin n) => vars.getD i.val s!"pad{i.val}"
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let trs := transitions p
  let vac := modeIndependent p
  let mut passed := 0
  let mut failing : List ((ℕ × ℕ) × String) := []
  -- the right domain at a switch is one formula only under uniform evolve; a benchmark
  -- that breaks the discipline is reported, never silently given its first mode's domain
  let uniform := uniformEvolveR p
  if !uniform && verbose then
    IO.println s!"  FAIL  {name}  (right modes do not share one evolve domain)"
  for tr in trs do
    let src := (p.L.modes.getD tr.1 dm).name
    let tgt := (p.L.modes.getD tr.2 dm).name
    match queryOf p n tr with
    | none =>
        failing := failing ++ [(tr, "query did not lower")]
        if verbose then IO.println s!"  FAIL  {name} {src} -> {tgt}  (handoff query did not lower)"
    | some q =>
        let script := q.toScript coord
        match ← (if uniform then s.check script else pure (.error "non-uniform right evolve")) with
        | .ok .unsat =>
            passed := passed + 1
            counted
            if verbose then
              IO.println s!"  UNSAT {name} {src} -> {tgt}{if vac then "  (vacuous: identical rows)" else ""}"
        | .ok v =>
            let model ← z3Model cfg script
            failing := failing ++ [(tr, s!"{reprStr v}; model: {model}")]
            if verbose then
              IO.println s!"  FAIL  {name} {src} -> {tgt}  ({reprStr v})"
              IO.println s!"        countermodel: {model}"
        | .error e =>
            failing := failing ++ [(tr, s!"z3 error: {e}")]
            if verbose then IO.println s!"  FAIL  {name} {src} -> {tgt}  (z3 error: {e})"
  let ms := (← IO.monoMsNow) - t0
  pure { bench := name, declared := declaredTransitions p, checked := trs.length,
         passed := passed, failing := failing, vacuous := vac, ms := ms }

/-- One summary line per benchmark (the `docs/HANDOFF.md` table row). -/
def HandoffReport.line (r : HandoffReport) : String :=
  let fails := if r.failing.isEmpty then "-" else
    String.intercalate ", " (r.failing.map (fun f => s!"{f.1.1}->{f.1.2}"))
  s!"  [handoff] {r.bench}: {r.checked}/{r.declared} transitions checked, {r.passed} passed, \
failing: {fails}{if r.vacuous then " (vacuous: mode-independent invariant)" else ""} ({r.ms}ms)"

end RelCertifier.Verdicts
