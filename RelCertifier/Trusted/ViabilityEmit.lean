/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S3 emission door — per-face bounded-viability tags

`--emit-viability2`: per right mode, per evolve-box face, one of
* `strict`  — R6's boundary strict-inflow probe (`UNSAT(box ∧ g = 0 ∧ ġ ≥ 0)`);
* `growth0` — the S3 growth route at `M = 0` (`UNSAT(box ∧ ġ > 0)`): the face value
  never climbs, so any STRICTLY interior anchor keeps it for every bounded duration
  (`anchor_budget_from_verdict` with `M·dt = 0`);
* `growth<M>` — the positive-bound growth route (`UNSAT(box ∧ ġ > M)`, doubling sweep
  `M ∈ {1,…,32}`): anchors within budget `g₀ + M·dt < 0` keep the face for `dt`
  (e.g. watertank `Mid`'s equilibrium face `x ≤ 25`, `ġ = 3(1−0.04x)`);
* `fail`    — no probe closes (model-margin fix — the tool-improvement loop).

Lean consumers: `face_strict_from_verdict` / `face_growth_from_verdict` →
`HExistSegB_of_viability` → `segment_faModalB_from_certB`.

A NEW FILE by design (rebuild hygiene): `OracleAPI` is untouched, so the instance
batteries (which import `CoverInstance` → `OracleAPI`) are not invalidated.
-/
import RelCertifier.Trusted.OracleAPI

namespace RelCertifier.Oracle

open RelCertifier.Parse

/-- Per-face bounded-viability tags for one right mode. -/
def checkViabilityFacesB (s : Z3Session) (cnt : IO.Ref Nat)
    (maxQ maxSmt deadline : Nat) (vars : List String) (n : ℕ)
    (coord : Fin n → String) (mR : PMode) : IO (List (Nat × String)) := do
  match evolveFacesR vars n mR.evolve, Run.lowerF vars n Side.R mR.evolve,
      Run.dynOf vars n Side.R mR with
  | some faces, some box, some fR => do
      let mut out : List (Nat × String) := []
      let mut idx := 0
      for g in faces do
        let gdot := ilieDeriv g (fun _ => ITerm.rat 0) fR (.rat 1)
        let qs := IForm.and box (IForm.and (IForm.cmp .eq g (.rat 0))
          (IForm.cmp .ge gdot (.rat 0)))
        if ← probeUnsat s cnt maxQ maxSmt deadline coord qs then
          out := out ++ [(idx, "strict")]
        else
          let qg := IForm.and box (IForm.cmp .gt gdot (.rat 0))
          if ← probeUnsat s cnt maxQ maxSmt deadline coord qg then
            out := out ++ [(idx, "growth0")]
          else
            -- positive growth bounds, doubling sweep (budget: g₀ + M·dt < 0)
            let mut tagged := false
            for m in [1, 2, 4, 8, 16, 32] do
              if !tagged then
                let qm := IForm.and box (IForm.cmp .gt gdot (.rat m))
                if ← probeUnsat s cnt maxQ maxSmt deadline coord qm then
                  out := out ++ [(idx, s!"growth{m}")]
                  tagged := true
            if !tagged then
              out := out ++ [(idx, "fail")]
        idx := idx + 1
      pure out
  | _, _, _ => pure []

/-- `--emit-viability2`: the per-benchmark face-tag table as a Lean literal. -/
def emitViabilityFileB (cfg : Z3Config) (path defname : String) : IO Unit := do
  let txt ← IO.FS.readFile path
  match parseProblemE txt with
  | .error e => IO.eprintln s!"ERROR: parse: {e}"; IO.Process.exit 1
  | .ok p =>
      match ← Z3Session.start cfg with
      | .error e => IO.eprintln s!"ERROR: z3: {e}"; IO.Process.exit 1
      | .ok s =>
          let cnt ← IO.mkRef 0
          let vars := p.L.stateVars
          let n := vars.length
          let coord := fun (i : Fin n) => vars.getD i.val "v"
          let deadline := (← IO.monoMsNow) + 40000
          let mut rows : List String := []
          for mR in p.R.modes do
            let v ← try checkViabilityFacesB s cnt 5000 200000 deadline vars n coord mR
              catch _ => pure []
            let cells := v.map (fun c => s!"({c.1}, \"{c.2}\")")
            rows := rows ++ [s!"(\"{mR.name}\", [" ++ String.intercalate ", " cells ++ "])"]
          s.close
          IO.println (s!"def {defname} : List (String × List (Nat × String)) := [" ++
            String.intercalate ", " rows ++ "]")

end RelCertifier.Oracle
