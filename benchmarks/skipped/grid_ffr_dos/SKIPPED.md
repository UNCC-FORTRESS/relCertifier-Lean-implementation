# grid_ffr_dos: skipped 2026-10-29 (fix round 4, after review round 4)

Finding (review round 4, verified): the claim did not depend on the attack. The 0.24 a_R band on
the frequency gap is the whole fast-frequency-response (FFR) contribution (0.625 / 2.625 = 0.238),
and with the left FFR switched off (`a' = 0`, an FFR that never fires) the file still CERTIFIED at
0.24 (measured on a scratch variant, review round 4). It also certified for a 1 s decision hold. So the certified
band separates the two grids by "FFR or no FFR", not by the DoS hold the scenario is about.

Why no claim-side fix keeps it meaningful (measured 2026-10-29 on scratch variants):

* Under a sampled decision hold (left control interval 0.3 s against the reference's 0.1 s) the
  cover must certify a segment that pairs the reference's FFR mode with the attacked unit still
  idle, and a segment certificate is time-free: it holds for that pairing as if it lasted for
  ever. That segment's flow is exactly the flow of an FFR that never fires, so every row that
  certifies under a hold admits the dead-FFR steady state (gap 0.238 at a_R = 1, a_L = 0). The
  stated rows, `0.24 a_R` with `a_L >= 0.4 a_R`, and `0.15 a_R` alone all DECLINE at left interval
  0.3 s; only the no-FFR band `0.24 a_R` with `a_L >= 0` certifies. A tight value that moves with
  the hold length, or an FFR-off counter-test that declines, is not reachable in this form.
* A claim that does depend on the attack exists only for a different attack effect: a DoS on the
  battery's set-point link with a rate-limited local fallback (`a' = 2 (1 - a)`, 0.5 s, at the
  same 0.1 s cycle). There the band `x_R <= x_L + 0.15 a_R` is tight (0.14 declines), the FFR-off
  counter-test DECLINES, and the band moves with the fallback ramp (0.20 at 1 s). But the decision
  hold is gone, and with it both letters: M needs the asynchronous cycles and P was load-bearing
  only inside the asynchronous window (letters M P -> none; every ablation CERTIFIES).
* The reviewer's second point, instantaneous droop with no frequency nadir for FFR to arrest,
  needs a governor lag on the reference (a new state and a new Assumption 1 proof), which makes
  the frequency gap oscillatory; linear rows such as `x_L <= x_R` are then not expected to be
  differential invariants.

The file is kept here unchanged (its last suite version, commit 46c3fb3; the instance, cover,
bridge, Assumption 1 proof and refutation instances left with it). Its letters were M P. The
refill is `canal_gate_notches` (from the reserve: round-1 reserve score P 4, R 4, C 5, overall 4,
letter X; one physical domain, the bank crest; every ablation and the 20 % widening as its header
states, measured 2026-10-29; its Assumption 1 proof of commit 10e5cd9~1 restored). The other
overall-4 candidate with a letter, `molding_pack_checkring` (D), was not taken: its pressure domain
`x, y <= 500` bar is the hold set point, and at the machine's pressure limit (2000 bar) the file
DECLINES (measured 2026-10-29), so its claim stands on a set-point domain. The suite's M and P
counts drop by one each (reported, not silent: the only reserve candidate with M or P scored above
3 is `quad_light_airframe_20`, whose claim stands on a domain bound and fails the widening test).

Stutter (2026-10-30, `docs/OVERNIGHT2-2026-10-30.md`, phase 3): tried `stutter = true` (stretch 0, the
witness waits): with the key the verdict and the tight 0.24 are unchanged (0.23 declines), no stretch-0 pairing passes, and the cause test (left FFR switched off) still certifies at 0.24; frequency support is a same-time claim, so a waiting grid is not a reference. Stays skipped.
