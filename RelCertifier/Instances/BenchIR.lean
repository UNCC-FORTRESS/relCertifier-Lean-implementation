/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The carried-over IR literals + `benchIRTable` (the 19 copied benchmarks)

The legacy instances re-exported by `InstancesV2/BatteryV2` quote these parser-emitted
literals (one leaf per benchmark under `BenchIR/`). Each is the literal of a
`benchmarks/suite_v2` file that was copied byte-for-byte from the retired legacy suite:
`InstancesV2/SameIR.lean` proves it equal to the suite_v2 literal (`rfl`), and
`relcert-test`'s `[ir-drift-v2]` re-parses the suite_v2 file. `benchIRTable` is what the
legacy-pack runner (`Verdicts/RunModal.runSpec`) rebuilds its queries from.

One more leaf lives under `BenchIR/` without a table row:
`story3_rollover_ladder_rung_b` (the legacy literal, which differs from the suite_v2 file on
the left only). It is imported by `Instances/Story3RolloverRungBModal`, whose right-side
facts the suite_v2 instance `InstancesV2/Modal/Story3RolloverRungB` reuses through `rfl`
identities of the right system and the invariant rows; no theorem about it is claimed.
-/
import RelCertifier.Instances.BenchIR.match_multi_rate
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung1_2to3
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2_3to6
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2_6dof
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2b_6dof
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2c_6dof
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung3_6to8
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung4_8to12
import RelCertifier.Instances.BenchIR.rover3tier_rung12
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung1
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung2
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung3
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung3_8d
import RelCertifier.Instances.BenchIR.story1_attdist_rung_a_6to8
import RelCertifier.Instances.BenchIR.story1_attdist_rung_b_12dof
import RelCertifier.Instances.BenchIR.story2_lateral_rung_a_8dof
import RelCertifier.Instances.BenchIR.story2_lateral_rung_b_12dof
import RelCertifier.Instances.BenchIR.story3_rollover_base_12dof
import RelCertifier.Instances.BenchIR.story3_rollover_ladder_rung_a

namespace RelCertifier.Parse

/-- The 19 carried-over literals, by benchmark name. -/
def benchIRTable : List (String × PProblem) := [
  ("match_multi_rate", match_multi_rate_IR),
  ("refinement_ladder_rover_rung1_2to3", refinement_ladder_rover_rung1_2to3_IR),
  ("refinement_ladder_rover_rung2_3to6", refinement_ladder_rover_rung2_3to6_IR),
  ("refinement_ladder_rover_rung2_6dof", refinement_ladder_rover_rung2_6dof_IR),
  ("refinement_ladder_rover_rung2b_6dof", refinement_ladder_rover_rung2b_6dof_IR),
  ("refinement_ladder_rover_rung2c_6dof", refinement_ladder_rover_rung2c_6dof_IR),
  ("refinement_ladder_rover_rung3_6to8", refinement_ladder_rover_rung3_6to8_IR),
  ("refinement_ladder_rover_rung4_8to12", refinement_ladder_rover_rung4_8to12_IR),
  ("rover3tier_rung12", rover3tier_rung12_IR),
  ("rover_dof_terrain_rung1", rover_dof_terrain_rung1_IR),
  ("rover_dof_terrain_rung2", rover_dof_terrain_rung2_IR),
  ("rover_dof_terrain_rung3", rover_dof_terrain_rung3_IR),
  ("rover_dof_terrain_rung3_8d", rover_dof_terrain_rung3_8d_IR),
  ("story1_attdist_rung_a_6to8", story1_attdist_rung_a_6to8_IR),
  ("story1_attdist_rung_b_12dof", story1_attdist_rung_b_12dof_IR),
  ("story2_lateral_rung_a_8dof", story2_lateral_rung_a_8dof_IR),
  ("story2_lateral_rung_b_12dof", story2_lateral_rung_b_12dof_IR),
  ("story3_rollover_base_12dof", story3_rollover_base_12dof_IR),
  ("story3_rollover_ladder_rung_a", story3_rollover_ladder_rung_a_IR) ]

end RelCertifier.Parse
