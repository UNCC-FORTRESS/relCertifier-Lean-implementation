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

Stutter (2026-10-30, `docs/OVERNIGHT2-2026-10-30.md`, phase 3): tried `stutter = true` (stretch 0, the
witness waits): with the key the verdict and the tight values (G 25.0, X 0.40) are unchanged and no stretch-0 pairing passes; two patients are compared at equal times, so a waiting reference has no meaning here. Stays skipped.
