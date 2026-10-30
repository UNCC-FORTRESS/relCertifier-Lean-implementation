# lit_drl_car_stop: skipped 2026-10-29 (literature migration, after review round 5)

Replaced by `lit_gpt10_boost_converter` (Girard, Pola, Tabuada, IEEE TAC 2010, Sec. 5.1).

Reason. The file reproduces the car-stop refinement example of differential refinement logic
(Loos, Platzer, LICS 2016, Sec. 6) only as Goal 1 (Safe_eps implies Safe) between two sampled
controllers. The source's theorem rests on Goal 3 (Safe_eps keeps the event domain for eps time), a
bounded-time fact that the format's clock-free joint-segment certificates cannot state; every faithful
reading tried (finer right period, the event domain as a claim conjunct, a nondeterministic envelope)
DECLINED or reduced to the same guard inclusion (literature fidelity round, 2026-10-29: fidelity
WEAK/FAIL/FAIL). The right copies the left (copy witness, tight value 0). Review round 5 scored it 2
(RETHINK). It repeats the structure of `lit_drl_lane_control`, which stays in the suite (with the same
disclosure) as the dRL case study; the replacement has a non-copy witness and a tight value equal to
the source's precision.

The input is kept unchanged in this directory for reference; its Assumption 1 proof
(`RelCertifier/InstancesV2/WellFormed/LitDrlCarStop.lean`) and generated layers are in git history
(last at the commit before this removal).

Stutter (2026-10-30, `docs/OVERNIGHT2-2026-10-30.md`, phase 3): tried `stutter = true` (stretch 0, the
witness waits): the file and its 23 variants (finer right period, E as a claim conjunct, no guard, ...) give the same verdicts with and without the key and no stretch-0 pairing passes; the dRL refinement is final-state inclusion at the identity relation (a shared clock, equal durations), so a frozen witness breaks it; the real gap stays Goal 3 (a bounded-time fact). Stays skipped.
