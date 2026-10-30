# zone_lightmass_schedule: skipped 2026-10-29 (literature migration)

Removed to keep the suite at 50 while three literature benchmarks came in (`lit_gpt10_boost_converter`,
`lit_csf25_salt_tank_hold`, and `rampmeter_poll_2to1` back from the reserve in place of
`insulin_basal_cgmloss`; `lit_drl_car_stop` went out).

Reason (review round 5, overall 2, RETHINK; the objection is structural): the 0.5 K row clears the
inductive bound set by the evolve domain by only 0.015 K, so the file certifies because the domain is
5..30 degC (0..30 or 5..33 DECLINE): the claim holds by a domain artifact. The row is about nine times the
reachable gap, and its letters B and X come from the claim's form, not from the lighter construction the
scenario is about.

Selection among the designed files scored 2 in round 5: no P or D carrier was removed (P total 4, D
total 10). Of the two candidates without P, D or R letters whose objection is structural
(`acc_spoof_limp`: M B I X; `zone_lightmass_schedule`: S M B X), this one loses S (the most plentiful
letter, 20) instead of I (17).

The input is kept unchanged in this directory for reference; its Assumption 1 proof
(`RelCertifier/InstancesV2/WellFormed/ZoneLightmassSchedule.lean`), pack rows and generated layers are
in git history (last at the commit before this removal).

Stutter (2026-10-30, `docs/OVERNIGHT2-2026-10-30.md`, phase 3): tried `stutter = true` (stretch 0, the
witness waits): with the key the verdict and the tight 0.49 are unchanged and the domain artifact stays (0..30 or 5..33 at 0.5 DECLINE with the key too); at 0.49 every stretch-0 pairing fails; the claim is a re-timed trace, not a time-abstract one. Stays skipped.
