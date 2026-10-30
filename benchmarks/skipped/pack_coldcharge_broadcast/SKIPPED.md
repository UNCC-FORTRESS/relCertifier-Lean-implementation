# pack_coldcharge_broadcast: designed in batch 10 (2026-10-30), not kept (review round 10)

A new design for a P slot (`docs/BATCH10-2026-10-30.md`): a 3S2P notebook pack (Panasonic NCR18650B)
charging in an unheated cabin under the TI bq40z50-R2 temperature ranges (TRM SLUUBK0B 4.2, 4.4, 4.11;
UT/LT/STL/RT), deployed gauge broadcasting every 60 s against the 30 s design; claim |T_L - T_R| <= 7;
letters M B P (four protection edges pruned, each needed; the UT trip live in the right model).
It was installed in place of `fuelcell_chp_dos` and withdrawn after review round 10 verified:

* the cabin range p in [-5, 14] (a design range of the file, in every guard and the domain) does the
  claim's work and is tuned to the letter: P needs p_lo in (-7, -3.5) and p_hi in (13, 14.5); with
  p_lo = -10 the file DECLINES at 7 (measured);
* the header's kinetics argument for 7 K was wrong at the cited upper activation energy (70 kJ/mol gives a
  factor 2.16 per 7 K near 0 degC, not "below 2"), and its RELCERT_SINGLE_STEP verdict was wrong
  (measured DECLINED);
* the LT current is raised from the TRM default to equalize the heat steps; the certified 7 K is about 30
  times the simulated worst gap (0.22 K), and the certifying set is not an interval ([7, 8], then 10.5).

Not clearly better than the file it would replace, so `fuelcell_chp_dos` stays. Not verified: the
reviewer's claim that P comes from the chosen STL / RT currents (with the TRM defaults for STL and RT the
file certifies at 8 and RELCERT_NO_PRUNE=1 still DECLINES). An Assumption 1 proof was drafted (all four
ranges by exit; three standard axioms) and not committed.
