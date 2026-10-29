# insulin_basal_cgmloss: skipped 2026-10-29 (literature migration, reserve swap)

Replaced by `rampmeter_poll_2to1` (back from `benchmarks/reserve/`, requirement re-derived from the
HCM 6th ed. Exhibit 12-15 level-of-service bands: |k_L - k_R| <= 8 veh/mi/ln, tightest 7.00).

Reason. Both files are the chain-depth template of `tank_dos_3to1` (one held deployed decision
against two reference decisions, letters M B); the suite keeps one of the two. Review round 5 scored
insulin 3 with a false header claim ("glucose can go either way from every level"), and its 9-level
table carries start-only ends; the reframed ramp meter scores 4/4/4/4 in the reserve scoping
(2026-10-29), with a requirement taken from a standard and a sharper dependence on the cause (the
requirement holds up to 40 s polling and fails at 50 s). Letters are unchanged by the swap (M B for M B).

The input is kept unchanged in this directory for reference; its Assumption 1 proof
(`RelCertifier/InstancesV2/WellFormed/InsulinBasalCgmloss.lean`), pack rows and generated layers are
in git history (last at the commit before this removal).
