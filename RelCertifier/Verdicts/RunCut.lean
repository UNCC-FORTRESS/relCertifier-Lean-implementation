/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The cut-probe runner — per-atom O2 hypotheses of the 11 cut benchmarks

The cut instances (`Instances/CutThroughout/`) hypothesize, per cut atom, one route
probe over the atom's safe-side term with the own-side field (other side frozen):
route A/B for the tool-tagged `diNonstrict`/`diStrict` atoms, A for `frozen`, C
(superlevel) for `shape`. This runner rebuilds each probe at runtime from the emitted
IR (`benchIRTable`) and cut certificates (`EvolStrengthenings`) — the generic pins
(`GenericPins.lean`) prove the printed queries are exactly the hypothesized ones —
prints them through the tool's own `toScript`, and reports Z3's verdict per probe.

The instances' strata/region/dyn hypotheses are the tool's own cover-certification
queries (kernel-replayed flags, `BenchCoverReplay`); their empirical record is the
certification run itself, re-runnable via `relcert <benchmark dirs>`.
-/
import RelCertifier.Verdicts.GenericPins
import RelCertifier.Instances.BenchIR
import RelCertifier.Instances.EvolStrengthenings
import RelCertifier.Trusted.Z3
import RelCertifier.Verdicts.Coverage

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.Parse RelCertifier.Oracle

/-- Build the tagged-route probe for one atom of one mode (own side; other frozen). -/
def atomProbe {n : ℕ} (side : Side) (vars : List String) (m : PMode)
    (a : PForm) (route : CutRoute) : Option (IForm n) := do
  let fI ← Run.dynOf vars n side m
  let evI ← Run.lowerF vars n side m.evolve
  let gI ← cutAtomG vars n side a
  let zero : Fin n → ITerm n := fun _ => .rat 0
  let (fL, fR) := match side with
    | Side.L => (fI, zero)
    | _ => (zero, fI)
  pure <| match route with
    | .diStrict => iflowQueryStrict gI fL fR (.rat 1) evI
    | .shape => iflowQuerySuperlevel gI fL fR (.rat 1) evI
    | _ => iflowQuery gI fL fR (.rat 1) evI

def routeTag : CutRoute → String
  | .diStrict => "B(strict)"
  | .diNonstrict => "A(nonstrict)"
  | .frozen => "A(frozen)"
  | .shape => "C(superlevel)"

def modeAtoms (side : Side) (rows : List (String × List (PForm × CutRoute)))
    (modes : List PMode) : List (PMode × PForm × CutRoute) :=
  rows.flatMap (fun r =>
    match modes.find? (fun m => m.name == r.1) with
    | some m => r.2.map (fun ac => (m, ac.1, ac.2))
    | none => [])

def runBenchProbes (s : Z3Session) (name : String) (p : PProblem)
    (cuts : Oracle.EvolStrengthening) : IO Bool := do
  let vars := p.L.stateVars
  let n := vars.length
  let coord := fun (i : Fin n) => vars.getD i.val s!"pad{i.val}"
  let work := (modeAtoms Side.L cuts.L p.L.modes).map (fun w => (Side.L, w))
    ++ (modeAtoms Side.R cuts.R p.R.modes).map (fun w => (Side.R, w))
  -- An empty `work` would run no query and still return success, which is how
  -- `rover_drag` went unchecked in the modal runner (`docs/VERDICT-EVIDENCE-AUDIT.md`).
  -- All 11 cut benchmarks currently yield probes; this makes a future empty one loud.
  if work.isEmpty then
    IO.println s!"  SKIP  {name}  (no cut atoms to probe)"
    return false
  let mut ok := true
  for (side, m, a, route) in work do
    let sideTag := if side == Side.L then "L" else "R"
    match (atomProbe (n := n) side vars m a route : Option (IForm n)) with
    | none =>
        IO.println s!"  LOWERING FAILED  {name} {sideTag}/{m.name} [{routeTag route}]"
        ok := false
    | some q =>
        match ← s.check (q.toScript coord) with
        | .ok .unsat =>
            IO.println s!"  UNSAT [{routeTag route}]  {name} {sideTag}/{m.name}"
            counted
        | v =>
            IO.println s!"  FAIL  {name} {sideTag}/{m.name} [{routeTag route}] → {reprStr (match v with | .ok r => reprStr r | .error e => e)}"
            ok := false
  pure ok

def cutBenchmarks : List (String × Oracle.EvolStrengthening) :=
  [("arm_chain_rung3", Oracle.arm_chain_rung3_cuts),
   ("refinement_ladder_rover_rung1_2to3", Oracle.refinement_ladder_rover_rung1_2to3_cuts),
   ("refinement_ladder_rover_rung3_6to8", Oracle.refinement_ladder_rover_rung3_6to8_cuts),
   ("refinement_ladder_rover_rung4_8to12", Oracle.refinement_ladder_rover_rung4_8to12_cuts),
   ("rover_attitude_cone_12dof", Oracle.rover_attitude_cone_12dof_cuts),
   ("rover_dof_terrain_rung1", Oracle.rover_dof_terrain_rung1_cuts),
   ("rover_dof_terrain_rung2", Oracle.rover_dof_terrain_rung2_cuts),
   ("rover_dof_terrain_rung3_8d", Oracle.rover_dof_terrain_rung3_8d_cuts),
   ("rover_dof_terrain_rung3", Oracle.rover_dof_terrain_rung3_cuts),
   ("story3_rollover_base_12dof", Oracle.story3_rollover_base_12dof_cuts),
   ("story3_rollover_ladder_rung_a", Oracle.story3_rollover_ladder_rung_a_cuts)]

def runCutProbes (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println "== cut instances : per-atom O2 route probes =="
      let mut ok := true
      for (nm, cuts) in cutBenchmarks do
        match benchIRTable.find? (fun r => r.1 == nm) with
        | some (_, p) => ok := (← runBenchProbes s nm p cuts) && ok
        | none =>
            IO.println s!"  NO IR  {nm}"
            ok := false
      s.close
      pure ok

end RelCertifier.Verdicts
