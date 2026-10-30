# rover_patrol_lag: skipped 2026-10-30 (batch 10, `docs/BATCH10-2026-10-30.md`)

Scored 2 / RETHINK in review round 6 (`docs/BENCHMARK-REVIEW-2026-10-30-r6.md`): the stated requirement is
real-time (a 1 m waypoint radius), but the certified claim is a re-timed one-sided order, so the letters
(S M R B at removal, batch-10 rules) rest on a claim weaker than the requirement the header motivates.
Replaced by `autoclave_liquid_steambank` (a sterilizer with a burnt-out steam-generator element; the
heat-up is re-timed by the generator output ratio 3/4, which the validation does not constrain; letters
S R D). The Assumption 1 proof (`RelCertifier/InstancesV2/WellFormed/RoverPatrolLag.lean`), pack rows and
generated layers are in git history (last at the commit before this removal).
