# fuelcell_chp_dos: skipped 2026-10-30 (batch 11, `docs/BATCH11-2026-10-30.md`)

Scored 2 / RETHINK in review round 7 (`docs/BENCHMARK-REVIEW-2026-10-30-r6.md` and the rounds after it), the
only suite file at overall 2 after batch 10. The DoS hold (the stack's current permission held for a longer
period under a denial of service on the supervisory link) has no physical effect on the claim: the
temperature band follows from the current-permission levels and the design range of the heating return,
not from the hold. Its letters at removal (batch-10 rules) were M B P I X. Replaced by a faithful
literature benchmark, `lit_nahs25_engine_cooling` (NAHS 2025 engine cooling under a bounded sensor attack,
the source's forward distance 0.3; letter R, with the opt-in pre-landing right-only certificate,
`docs/PRELANDING.md`). The P slot is kept by `extruder_pe100_manualstart` (installed in the same batch).
The Assumption 1 proof (`RelCertifier/InstancesV2/WellFormed/FuelcellChpDos.lean`), pack rows and
generated layers are in git history (last at the commit before this removal).
