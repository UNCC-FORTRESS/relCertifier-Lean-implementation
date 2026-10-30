# charger_fast_tapers: skipped 2026-10-30 (review round 6)

Findings of review round 6 (`docs/BENCHMARK-REVIEW-2026-10-30-r6.md`), verified by tool runs
(`docs/OVERNIGHT2-2026-10-30.md`, phase 4):

* The claim does not depend on its cause. A deployed constant-current rate of 1.0 %/s (8 times the
  reference profile's, simulated re-timed lead 51 % SoC) CERTIFIES at c = 1, also at lambda 1; with the
  cause removed (BULK 0.1) it CERTIFIES; a deployed ABSORB of 1.0 CERTIFIES. Right-only repositioning
  lets the reference profile run ahead alone (NO_REPO declines the 8x file), so the certified lead is
  time-abstract on the profile side and says nothing about the deployed charger's rates.
* The tolerance c = 1 is the tool's over-approximation (the profile parked at FULL against the deployed
  cell), not a physical lead (simulated re-timed lead at most 0.006 % SoC); the unit is needed in BULK,
  ABSORB and FULL alike, so the header's "charging pairings hold at any positive c" was wrong, and the
  D letter (rows 0 vs 1) rests on that unit.
* S was not forced: the file at lambda = 1 CERTIFIES (it parks the profile at FULL); the SYNC decline is
  R's. It was the only S file whose lambda = 1 variant certifies.
* The header's rates 8.5 / 2.1 %/min are the reference profile's; the deployed's are 10.6 / 2.6.

No fix keeps a non-trivial claim (every form tried certifies for any deployed rate, or declines). Letters
lost: S M R B D I. Refill: `molding_pack_checkring` (reserve, reframed; D). The Assumption 1 proof
(`RelCertifier/InstancesV2/WellFormed/ChargerFastTapers.lean`), pack rows and generated layers are in git
history (last at the commit before this removal).
