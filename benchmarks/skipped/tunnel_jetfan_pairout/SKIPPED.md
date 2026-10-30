# tunnel_jetfan_pairout: skipped 2026-10-29 (domain audit)

Rule: an evolve domain states a physical constraint of the plant (a hardware limit, a sensor
range, a saturation, a trip); it must not be a closed-loop target, a set point, an asymptote
or a reachable-set cap chosen so that the claim certifies.

The file's velocity floor `u >= 2.6` m/s was the ventilation controller's minimum duty (a policy:
"while the tunnel is open to traffic the controller never stops all fans"), not a limit of the
tunnel, and the claim stood on it: the domain scan of 2026-10-29 found the file DECLINED with
every bound widened by 5 % of its range, and the floor alone widened by 20 % DECLINED (the
header itself placed the floor's load-bearing value at 2.54 m/s). The physical floor of the air
velocity is 0 (the fans have no hardware minimum; a tunnel with its fans off is a state of the
plant).

At the floor 0 the file DECLINES (NORMAL_L: both the NORMAL and the FIRE segment fail), and no
claim-side fix keeps the benchmark meaningful:

* The reference's NORMAL mode is not well formed on the physical domain: its guard carries the
  PIARC normal-operation fact `c <= 100` ppm, which the flow keeps only for `u >= 2.533` m/s; at
  a lower airflow CO rises through 100 ppm with no successor mode (FIRE needs `t >= 600`). The
  tool's Assumption 1 check reports the mode UNKNOWN at floor 0, and the kernel proof
  (`WellFormed/TunnelJetfanPairout.lean`) cannot be written for it. A model with a successor
  for `c > 100` (a boost mode, every fan at full speed, as a CO-driven ventilation controller
  would do) is a new design, not a fix.
* The mode fact `c_R <= 100` is what makes the CO row `c_L <= c_R + 30` inductive (the CO gap
  grows with `(u_R - u_L) c_R / L`); it is a single-sided cut and is lost at floor 0 (the cut is
  checked on the right automaton alone, where `u >= 3` is not available). Stating it as a row
  (`c_R <= 100`, inductive under the rows `u_L >= 3`, `u_L <= u_R`) would carry the CO row but
  drop the letter I, and would not repair the ill-formed mode.
* In any boost mode the CO gap of the two tunnels is not bounded by an affine row from every
  admitted start: with `c_R` up to the CO domain and a velocity gap of 1.42 m/s the gap grows at
  up to 0.8 ppm/s, and the bounded quantity is the ratio `c_L / c_R` (the two flush rates), which
  the claim language cannot state. The CO cap `c <= 900` ppm is not forward invariant at floor 0
  either (`c' = 0.1583 > 0` at `u = 0`).

The file is kept here unchanged (its last suite version, commit b1827f4; no Lean integration:
the instance, cover, bridge, Assumption 1 proof and the two kernel refutations `_m024`, `_m027`
left with it). Its letters were D I; D is carried by the refill `antenna_track_kvretune` (from
the reserve, round-1 reserve score 4) and, since the same audit, by `turbine_startup_gearratio`
(mode-dependent rows at the overspeed trip); the suite's I count drops from 18 to 17 (reported,
not silent: no reserve candidate with I scored above 3).

Stutter (2026-10-30, `docs/OVERNIGHT2-2026-10-30.md`, phase 3): tried `stutter = true` (stretch 0, the
witness waits): with the key the file's verdict and tight values are unchanged (u-band 0.41) and no stretch-0 pairing passes (the rows tie the two clocks); at the physical floor u >= 0 the right model fails Assumption 1 (NORMAL UNKNOWN, FIRE BLOCKING) with or without the key, which stutter cannot repair. Stays skipped.
