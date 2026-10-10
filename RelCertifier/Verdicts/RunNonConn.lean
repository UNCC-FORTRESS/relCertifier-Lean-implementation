/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The non-connection runner — the two pruning queries of every pruned edge

Phase 5 of `--run-verdicts`. For every emitted benchmark and every pruned edge the
emitted cover records (`CoverEmitE.pruned` — the Def-3 non-connection certificates the
certifier applied, paper Section 4.3), this runner rebuilds the two queries the
certifier sent Z3 to prune it — `Trusted/NonConnQuery.lean`, the SAME function the
tool's `nonConnPrune` calls, over the emitted IR and the source mode's emitted checked
cut (`EvolStrengthenings`, folded exactly as `checkedCut` folds its kept atoms) — prints
them through the tool's own `toScript`, and reports Z3's verdict on each:

    sourceCheck  = guard_src ∧ evolve_src ∧ cut_src ∧ g > 0
    barrierCheck = evolve_src ∧ cut_src ∧ g = 0 ∧ Lie_R g ≥ 0

`Proofs/Encoding/NonConnBridge.lean` (`nonconn_of_unsat`) takes `z3solve (q).toHost =
unsat` for exactly these two `IForm`s and yields Theorem 2's conclusion for the edge, so
a green line here is evidence about the kernel-stated certificate
(`Instances/<Name>Pruned.lean`) and not about a lookalike.

Coverage is declared, not inferred (`Verdicts/Coverage.lean`): the phase owes
`expected.nonconn` queries — two per pruned edge, `expected.prunedEdges` edges — and
`CoveragePins` proves both constants equal what the emitted covers declare. A table whose
pruned pairs cannot be rebuilt (no IR, no such mode, a guard that is not a strict scalar
threshold) is reported as a failure, never skipped.
-/
import RelCertifier.Trusted.NonConnQuery
import RelCertifier.Trusted.JointVars
import RelCertifier.Trusted.Z3
import RelCertifier.Instances.BenchIR
import RelCertifier.Instances.BenchCovers
import RelCertifier.Instances.EvolStrengthenings
import RelCertifier.Verdicts.Coverage

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.Parse RelCertifier.NonConn

/-- Every emitted cover, in `certifiedIRTable` order (`CoveragePins` checks the names agree):
the declined benchmarks (`Parse.declinedIR`) have none. -/
def benchCoverTable : List (String × CoverEmitE) := [
   ("arm_chain_rung3", arm_chain_rung3_cover),
   ("arm_fidelity_mid", arm_fidelity_mid_cover),
   ("attitude_rate", attitude_rate_cover),
   ("endurance_gain_M1", endurance_gain_M1_cover),
   ("endurance_orderlift_1to2", endurance_orderlift_1to2_cover),
   ("endurance_orderlift_2to3", endurance_orderlift_2to3_cover),
   ("match_multi_rate", match_multi_rate_cover),
   ("refinement_ladder_rover_rung1_2to3", refinement_ladder_rover_rung1_2to3_cover),
   ("refinement_ladder_rover_rung2_3to6", refinement_ladder_rover_rung2_3to6_cover),
   ("refinement_ladder_rover_rung2_6dof", refinement_ladder_rover_rung2_6dof_cover),
   ("refinement_ladder_rover_rung2b_6dof", refinement_ladder_rover_rung2b_6dof_cover),
   ("refinement_ladder_rover_rung2c_6dof", refinement_ladder_rover_rung2c_6dof_cover),
   ("refinement_ladder_rover_rung3_6to8", refinement_ladder_rover_rung3_6to8_cover),
   ("refinement_ladder_rover_rung4_8to12", refinement_ladder_rover_rung4_8to12_cover),
   ("rover3_M1", rover3_M1_cover),
   ("rover3tier_rung12", rover3tier_rung12_cover),
   ("rover_4d_box", rover_4d_box_cover),
   ("rover_attitude_cone_12dof", rover_attitude_cone_12dof_cover),
   ("rover_coupled", rover_coupled_cover),
   ("rover_dof_terrain_rung1", rover_dof_terrain_rung1_cover),
   ("rover_dof_terrain_rung2", rover_dof_terrain_rung2_cover),
   ("rover_dof_terrain_rung3_8d", rover_dof_terrain_rung3_8d_cover),
   ("rover_dof_terrain_rung3", rover_dof_terrain_rung3_cover),
   ("rover_drag", rover_drag_cover),
   ("rover_position", rover_position_cover),
   ("rover_terrain_M1", rover_terrain_M1_cover),
   ("rover_tier_r1", rover_tier_r1_cover),
   ("story1_attdist_rung_a_6to8", story1_attdist_rung_a_6to8_cover),
   ("story1_attdist_rung_b_12dof", story1_attdist_rung_b_12dof_cover),
   ("story2_lateral_rung_a_8dof", story2_lateral_rung_a_8dof_cover),
   ("story2_lateral_rung_b_12dof", story2_lateral_rung_b_12dof_cover),
   ("story3_rollover_base_12dof", story3_rollover_base_12dof_cover),
   ("story3_rollover_ladder_rung_a", story3_rollover_ladder_rung_a_cover),
   ("story3_rollover_ladder_rung_b", story3_rollover_ladder_rung_b_cover) ]

/-- Every emitted checked-cut certificate, in `benchIRTable` order. -/
def benchCutsTable : List (String × Oracle.EvolStrengthening) := [
   ("arm_chain_rung1", Oracle.arm_chain_rung1_cuts),
   ("arm_chain_rung2", Oracle.arm_chain_rung2_cuts),
   ("arm_chain_rung3", Oracle.arm_chain_rung3_cuts),
   ("arm_fidelity_low", Oracle.arm_fidelity_low_cuts),
   ("arm_fidelity_mid", Oracle.arm_fidelity_mid_cuts),
   ("attitude_rate", Oracle.attitude_rate_cuts),
   ("endurance_gain_M1", Oracle.endurance_gain_M1_cuts),
   ("endurance_orderlift_1to2", Oracle.endurance_orderlift_1to2_cuts),
   ("endurance_orderlift_2to3", Oracle.endurance_orderlift_2to3_cuts),
   ("match_multi_rate", Oracle.match_multi_rate_cuts),
   ("refinement_ladder_rover_rung1_2to3", Oracle.refinement_ladder_rover_rung1_2to3_cuts),
   ("refinement_ladder_rover_rung2_3to6", Oracle.refinement_ladder_rover_rung2_3to6_cuts),
   ("refinement_ladder_rover_rung2_6dof", Oracle.refinement_ladder_rover_rung2_6dof_cuts),
   ("refinement_ladder_rover_rung2b_6dof", Oracle.refinement_ladder_rover_rung2b_6dof_cuts),
   ("refinement_ladder_rover_rung2c_6dof", Oracle.refinement_ladder_rover_rung2c_6dof_cuts),
   ("refinement_ladder_rover_rung3_6to8", Oracle.refinement_ladder_rover_rung3_6to8_cuts),
   ("refinement_ladder_rover_rung4_8to12", Oracle.refinement_ladder_rover_rung4_8to12_cuts),
   ("robot_braking", Oracle.robot_braking_cuts),
   ("rover3_M1", Oracle.rover3_M1_cuts),
   ("rover3tier_M1", Oracle.rover3tier_M1_cuts),
   ("rover3tier_rung12", Oracle.rover3tier_rung12_cuts),
   ("rover_4d_box", Oracle.rover_4d_box_cuts),
   ("rover_attitude_cone_12dof", Oracle.rover_attitude_cone_12dof_cuts),
   ("rover_coupled", Oracle.rover_coupled_cuts),
   ("rover_dof_terrain_rung1", Oracle.rover_dof_terrain_rung1_cuts),
   ("rover_dof_terrain_rung2", Oracle.rover_dof_terrain_rung2_cuts),
   ("rover_dof_terrain_rung3_8d", Oracle.rover_dof_terrain_rung3_8d_cuts),
   ("rover_dof_terrain_rung3", Oracle.rover_dof_terrain_rung3_cuts),
   ("rover_drag", Oracle.rover_drag_cuts),
   ("rover_position", Oracle.rover_position_cuts),
   ("rover_terrain_M1", Oracle.rover_terrain_M1_cuts),
   ("rover_tier_r1", Oracle.rover_tier_r1_cuts),
   ("story1_attdist_rung_a_6to8", Oracle.story1_attdist_rung_a_6to8_cuts),
   ("story1_attdist_rung_b_12dof", Oracle.story1_attdist_rung_b_12dof_cuts),
   ("story2_lateral_rung_a_8dof", Oracle.story2_lateral_rung_a_8dof_cuts),
   ("story2_lateral_rung_b_12dof", Oracle.story2_lateral_rung_b_12dof_cuts),
   ("story3_rollover_base_12dof", Oracle.story3_rollover_base_12dof_cuts),
   ("story3_rollover_ladder_rung_a", Oracle.story3_rollover_ladder_rung_a_cuts),
   ("story3_rollover_ladder_rung_b", Oracle.story3_rollover_ladder_rung_b_cuts),
   ("watertank", Oracle.watertank_cuts) ]

/-- The pruned edges of every emitted cover, as `(benchmark, source, target)`. -/
def prunedEdges : List (String × String × String) :=
  benchCoverTable.flatMap (fun c => c.2.pruned.map (fun e => (c.1, e.1, e.2)))

/-- Rebuild the two queries of one pruned edge from the emitted data. -/
def nonConnQueriesOf (p : PProblem) (cuts : Oracle.EvolStrengthening) (src tgt : String) :
    Option ((n : ℕ) × (Fin n → String) × IForm n × IForm n) := do
  let vars := p.jointVars
  let n := vars.length
  let mR ← p.R.modes.find? (·.name == src)
  let mSuc ← p.R.modes.find? (·.name == tgt)
  let cutR ← cutOfAtoms vars n (rightCutAtoms cuts src)
  let (q1, q2) ← queries vars n cutR mR mSuc
  pure ⟨n, fun i => vars.getD i.val s!"pad{i.val}", q1, q2⟩

/-- One pruned edge: both queries must come back `unsat`. -/
def runPrunedEdge (s : Z3Session) (bench src tgt : String) : IO Bool := do
  let some (_, p) := benchIRTable.find? (fun r => r.1 == bench)
    | IO.println s!"  FAIL  {bench} {src} -> {tgt}  (no emitted IR)"; return false
  let some (_, cuts) := benchCutsTable.find? (fun r => r.1 == bench)
    | IO.println s!"  FAIL  {bench} {src} -> {tgt}  (no emitted cut certificate)"; return false
  match nonConnQueriesOf p cuts src tgt with
  | none =>
      IO.println s!"  FAIL  {bench} {src} -> {tgt}  (pruning queries did not rebuild)"
      return false
  | some ⟨_, coord, q1, q2⟩ =>
      let mut ok := true
      for (tag, q) in [("source", q1), ("barrier", q2)] do
        match ← s.check (q.toScript coord) with
        | .ok .unsat =>
            IO.println s!"  UNSAT [{tag}]  {bench} {src} -> {tgt}"
            counted
        | v =>
            IO.println s!"  FAIL  {bench} {src} -> {tgt} [{tag}] → {reprStr (match v with | .ok r => reprStr r | .error e => e)}"
            ok := false
      pure ok

/-- The non-connection phase over the whole emitted suite. Green iff every pruned edge's
two queries are `unsat`; the caller checks the count against `expected.nonconn`. -/
def runNonConnAll (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== non-connection : {prunedEdges.length} pruned edge(s), two queries each =="
      -- an empty list would issue no query and look green; the declared count
      -- (`expected.prunedEdges`) is what makes that visible, but say it here too
      if prunedEdges.isEmpty then
        IO.println "  (no pruned edge in any emitted cover)"
      let mut ok := true
      for (bench, src, tgt) in prunedEdges do
        ok := (← runPrunedEdge s bench src tgt) && ok
      s.close
      if ok then IO.println s!"NON-CONNECTION PHASE COMPLETE ({prunedEdges.length} edge(s))"
      else IO.println "NON-CONNECTION PHASE INCOMPLETE (see above)"
      pure ok

end RelCertifier.Verdicts
