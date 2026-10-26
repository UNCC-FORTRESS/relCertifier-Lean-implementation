#!/usr/bin/env python3
"""The benchmark rename map (branch rename-benchmarks, 2026-10-25) and its application.

PAIRS: suite_v2 benchmark directory names old -> new (story3_rollover_base_12dof is NOT
renamed: its header describes the right side as a coarse 6-DOF plan, contradicting 8to12).
HAND: hand-written CamelCase stems of the WellFormed leaves (suffixes Guarded/Modal/Pins/...).
apply(s): one left-to-right pass of a single alternation, longest key first at each position.
"""
import re

PAIRS = [
    ("refinement_ladder_rover_rung1_2to3", "rover_ladder_2to3"),
    ("refinement_ladder_rover_rung2_3to6", "rover_ladder_3to6"),
    ("refinement_ladder_rover_rung3_6to8", "rover_ladder_6to8"),
    ("refinement_ladder_rover_rung4_8to12", "rover_ladder_8to12"),
    ("refinement_ladder_rover_rung2_6dof", "rover_ladder_2to4"),
    ("refinement_ladder_rover_rung2b_6dof", "rover_ladder_4to6_kin"),
    ("refinement_ladder_rover_rung2c_6dof", "rover_ladder_4to6"),
    ("rover_dof_terrain_rung1", "rover_terrain_2to3"),
    ("rover_dof_terrain_rung2", "rover_terrain_3to6"),
    ("rover_dof_terrain_rung3", "rover_terrain_6to12"),
    ("rover_dof_terrain_rung3_8d", "rover_terrain_6to8"),
    ("story1_attdist_rung_a_6to8", "rover_attitude_6to8"),
    ("story1_attdist_rung_b_12dof", "rover_attitude_8to12"),
    ("story2_lateral_rung_a_8dof", "rover_lateral_6to8"),
    ("story2_lateral_rung_b_12dof", "rover_lateral_8to12"),
    ("story3_rollover_ladder_rung_a", "rover_rollover_split_a"),
    ("story3_rollover_ladder_rung_b", "rover_rollover_split_b"),
]

def camel(b):
    # the generators' camel (scripts/gen_bridge.py `camel`)
    return "".join(w.capitalize() for w in b.split("_"))

HAND = [
    ("RoverLadderRung1", "RoverLadder2to3"),
    ("RoverLadderRung2", "RoverLadder3to6"),
    ("RoverLadderRung3", "RoverLadder6to8"),
    ("RoverLadderRung4", "RoverLadder8to12"),
    ("RoverRung26dof", "RoverLadder2to4"),
    ("RoverRung2b6dof", "RoverLadder4to6Kin"),
    ("RoverRung2c", "RoverLadder4to6"),
    ("Story1AttdistRungA", "RoverAttitude6to8"),
    ("Story1AttdistRungB", "RoverAttitude8to12"),
    ("Story2LateralA", "RoverLateral6to8"),
    ("Story2LateralB", "RoverLateral8to12"),
    ("Story3RolloverRungA", "RoverRolloverSplitA"),
    ("Story3RolloverRungB", "RoverRolloverSplitB"),
]

MAP = dict(PAIRS)
MAP.update({camel(o): camel(n) for o, n in PAIRS})
MAP.update(dict(HAND))
assert len(MAP) == len(PAIRS) * 2 + len(HAND)

_KEYS = sorted(MAP, key=len, reverse=True)
# left boundary: not preceded by a letter/digit (snake) -- camel keys may follow "V2"/"." etc.
_RX = re.compile("|".join(re.escape(k) for k in _KEYS))

def apply(s):
    return _RX.sub(lambda m: MAP[m.group(0)], s)

def matches(s):
    return [m.group(0) for m in _RX.finditer(s)]

NEW_KEYS = sorted(set(MAP.values()), key=len, reverse=True)

if __name__ == "__main__":
    for o, n in PAIRS:
        print(o, "->", n, "|", camel(o), "->", camel(n))
