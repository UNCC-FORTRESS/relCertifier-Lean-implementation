#!/bin/zsh
# Overnight battery rebuild after the Parse strict-fix (b67a02a).
# Serial-heavies discipline (rebuild hygiene): elaborate the 12-dof instance
# files one at a time before the parallel world build.
set -e
cd "$(dirname "$0")/.."
HEAVIES=(
  RelCertifier.Instances.Throughout.story1_attdist_rung_a_6to8
  RelCertifier.Instances.Throughout.story1_attdist_rung_b_12dof
  RelCertifier.Instances.Throughout.story2_lateral_rung_a_8dof
  RelCertifier.Instances.Throughout.story2_lateral_rung_b_12dof
  RelCertifier.Instances.Throughout.story3_rollover_ladder_rung_b
  RelCertifier.Instances.CutThroughout.rover_attitude_cone_12dof
  RelCertifier.Instances.CutThroughout.story3_rollover_base_12dof
  RelCertifier.Instances.CutThroughout.story3_rollover_ladder_rung_a
  RelCertifier.Instances.CutThroughout.refinement_ladder_rover_rung3_6to8
  RelCertifier.Instances.CutThroughout.refinement_ladder_rover_rung4_8to12
  RelCertifier.Instances.CutThroughout.rover_dof_terrain_rung3
  RelCertifier.Instances.CutThroughout.rover_dof_terrain_rung3_8d
)
echo "REBUILD START $(date +%T)"
for h in $HEAVIES; do
  echo "-- $h $(date +%T)"
  lake build $h
done
echo "-- world $(date +%T)"
lake build
lake build relcert
echo "REBUILD DONE $(date +%T)"
