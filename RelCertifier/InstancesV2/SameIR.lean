/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The 19 suite_v2 benchmarks carried over from the retired legacy suite (GENERATED)

Each of these suite_v2 files is a byte-identical copy of a file of the retired legacy suite
(`suite_uniform`, removed from the tree; git history keeps it). Its parser-emitted literal
IS the literal the carried-over legacy instance quotes (`rfl` below), so the legacy
theorems (`Instances/`, re-exported by `InstancesV2/BatteryV2`) are theorems about the
suite_v2 file; the file-to-literal tie is `relcert-test`'s `[ir-drift-v2]`.
-/
import RelCertifier.InstancesV2.BenchIR.match_multi_rate
import RelCertifier.Instances.BenchIR.match_multi_rate
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung1_2to3
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung1_2to3
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung2_3to6
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2_3to6
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung2_6dof
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2_6dof
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung2b_6dof
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2b_6dof
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung2c_6dof
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung2c_6dof
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung3_6to8
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung3_6to8
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung4_8to12
import RelCertifier.Instances.BenchIR.refinement_ladder_rover_rung4_8to12
import RelCertifier.InstancesV2.BenchIR.rover3tier_rung12
import RelCertifier.Instances.BenchIR.rover3tier_rung12
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung1
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung1
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung2
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung2
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung3
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung3
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung3_8d
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung3_8d
import RelCertifier.InstancesV2.BenchIR.story1_attdist_rung_a_6to8
import RelCertifier.Instances.BenchIR.story1_attdist_rung_a_6to8
import RelCertifier.InstancesV2.BenchIR.story1_attdist_rung_b_12dof
import RelCertifier.Instances.BenchIR.story1_attdist_rung_b_12dof
import RelCertifier.InstancesV2.BenchIR.story2_lateral_rung_a_8dof
import RelCertifier.Instances.BenchIR.story2_lateral_rung_a_8dof
import RelCertifier.InstancesV2.BenchIR.story2_lateral_rung_b_12dof
import RelCertifier.Instances.BenchIR.story2_lateral_rung_b_12dof
import RelCertifier.InstancesV2.BenchIR.story3_rollover_base_12dof
import RelCertifier.Instances.BenchIR.story3_rollover_base_12dof
import RelCertifier.InstancesV2.BenchIR.story3_rollover_ladder_rung_a
import RelCertifier.Instances.BenchIR.story3_rollover_ladder_rung_a

namespace RelCertifier.Parse

theorem match_multi_rate_IRv2_eq : match_multi_rate_IRv2 = match_multi_rate_IR := rfl
theorem refinement_ladder_rover_rung1_2to3_IRv2_eq : refinement_ladder_rover_rung1_2to3_IRv2 = refinement_ladder_rover_rung1_2to3_IR := rfl
theorem refinement_ladder_rover_rung2_3to6_IRv2_eq : refinement_ladder_rover_rung2_3to6_IRv2 = refinement_ladder_rover_rung2_3to6_IR := rfl
theorem refinement_ladder_rover_rung2_6dof_IRv2_eq : refinement_ladder_rover_rung2_6dof_IRv2 = refinement_ladder_rover_rung2_6dof_IR := rfl
theorem refinement_ladder_rover_rung2b_6dof_IRv2_eq : refinement_ladder_rover_rung2b_6dof_IRv2 = refinement_ladder_rover_rung2b_6dof_IR := rfl
theorem refinement_ladder_rover_rung2c_6dof_IRv2_eq : refinement_ladder_rover_rung2c_6dof_IRv2 = refinement_ladder_rover_rung2c_6dof_IR := rfl
theorem refinement_ladder_rover_rung3_6to8_IRv2_eq : refinement_ladder_rover_rung3_6to8_IRv2 = refinement_ladder_rover_rung3_6to8_IR := rfl
theorem refinement_ladder_rover_rung4_8to12_IRv2_eq : refinement_ladder_rover_rung4_8to12_IRv2 = refinement_ladder_rover_rung4_8to12_IR := rfl
theorem rover3tier_rung12_IRv2_eq : rover3tier_rung12_IRv2 = rover3tier_rung12_IR := rfl
theorem rover_dof_terrain_rung1_IRv2_eq : rover_dof_terrain_rung1_IRv2 = rover_dof_terrain_rung1_IR := rfl
theorem rover_dof_terrain_rung2_IRv2_eq : rover_dof_terrain_rung2_IRv2 = rover_dof_terrain_rung2_IR := rfl
theorem rover_dof_terrain_rung3_IRv2_eq : rover_dof_terrain_rung3_IRv2 = rover_dof_terrain_rung3_IR := rfl
theorem rover_dof_terrain_rung3_8d_IRv2_eq : rover_dof_terrain_rung3_8d_IRv2 = rover_dof_terrain_rung3_8d_IR := rfl
theorem story1_attdist_rung_a_6to8_IRv2_eq : story1_attdist_rung_a_6to8_IRv2 = story1_attdist_rung_a_6to8_IR := rfl
theorem story1_attdist_rung_b_12dof_IRv2_eq : story1_attdist_rung_b_12dof_IRv2 = story1_attdist_rung_b_12dof_IR := rfl
theorem story2_lateral_rung_a_8dof_IRv2_eq : story2_lateral_rung_a_8dof_IRv2 = story2_lateral_rung_a_8dof_IR := rfl
theorem story2_lateral_rung_b_12dof_IRv2_eq : story2_lateral_rung_b_12dof_IRv2 = story2_lateral_rung_b_12dof_IR := rfl
theorem story3_rollover_base_12dof_IRv2_eq : story3_rollover_base_12dof_IRv2 = story3_rollover_base_12dof_IR := rfl
theorem story3_rollover_ladder_rung_a_IRv2_eq : story3_rollover_ladder_rung_a_IRv2 = story3_rollover_ladder_rung_a_IR := rfl

end RelCertifier.Parse
