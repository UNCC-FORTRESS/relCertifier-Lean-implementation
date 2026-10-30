# lit_hypercert_vehicle: skipped 2026-10-28

The source's claim is false as formalized: under HyperCertificates' own Sec. 2.2 semantics
(runs confined to X = [0, 8] x [0, 0.6]), the secret run from (s, v) = (0, 0.6) that cruises 5
steps and brakes 15 steps rests at s = 7.5, and every partner within delta = 0.01 in velocity at
every step covers at least 7.3 m and so starts at or below 0.70, inside the secret set Xs = [0, 1];
no non-secret partner exists. What this file certified is a claim about a different system (the
position bound dropped, the road unbounded), not a weakening of the source's, so under the
literature rule (skip a literature example whose source claim is false as formalized, do not
repair it) the benchmark leaves the suite (50 -> 49); its copy-witness content is carried by
`lit_lz21_vehicle_position`, whose source claim survives and whose offset is a source constant.

The file is kept here unchanged (no Lean integration). The Assumption 1 negative exhibit
`benchmarks/negative_wellformed/lit_hypercert_vehicle_s8` is self-contained and stays.

Stutter (2026-10-30, `docs/OVERNIGHT2-2026-10-30.md`, phase 3): tried `stutter = true` (stretch 0, the
witness waits): with the key every stretch-0 pairing fails (the offset row breaks when the partner is frozen; the literal bounded reading fails at Am4 because v_L moves) and every verdict is unchanged; the source is synchronous HyperLTL (a lock-step game: the existential player selects the next state of the counter-trace), so a waiting partner would be an asynchronous opacity notion, not the source's. Stays skipped.
