# Non-vacuity and mutation checks (branch `mutation`)

Run 2026-10-19 on `benchmarks/suite_v2` (50 benchmarks), `RELCERT_IMPLIED_CUT=1`.

## Non-vacuity (`scripts/nonvacuity.py`)

Every left mode has a satisfiable start: Z3 `sat` for guard_L and evolve_L and the
mode's invariant row and some right mode's guard and evolve. **135 / 135 left modes sat**
over the 50 benchmarks (`nonvacuity.json`). Negative control: a contradictory water-tank
row is reported `unsat`.

## Mutation (`scripts/mutation.py --frac 0.1`)

Each invariant atom with nonzero constant slack c is tightened by 0.1·|c|, one atom at a
time; sanity (unmutated `smt2:` rewrite) is CERTIFIED for all 50.

| | count |
|---|---|
| atoms tightened (mutants) | 99, in 41 benchmarks |
| declined | 32, in 12 benchmarks |
| still certified | 66 |
| tool error | 1 (story1_attdist_rung_a, quadratic atom) |
| atoms skipped (zero constant slack, e.g. `v_l <= v_r`, equalities) | 65 |

Reading: a still-certified mutant means the hand-written bound has more than 10% slack;
a declined one is false or beyond the certifier. This profiles tightness, not falsity.

## Sweep over the tightening fraction

| fraction of slack removed | declined | still certified | error/timeout | benchmarks with a decline |
|---|---|---|---|---|
| 0.1 | 32 | 66 | 1 | 12 |
| 0.25 | 36 | 57 | 6 | 15 |
| 0.5 | 42 | 56 | 1 | 20 |
| 1.0 (constant removed) | 54 | 36 | 9 | 26 |

The profile is bimodal: about a third of the atoms are tight (declined already at 0.1),
about a third certify even with their constant removed (the constant is not needed, often
one side of a two-sided band), and the rest decline only under large tightening.

## Black-Okun-Yesha operators with an independent refuter (`scripts/black_mutation.py`, 2026-10-19)

Verdict = `relcert --handoff` AND `relcert <file>` (the default command alone omits the
handoff premise of Theorem 3). Operators restricted to the non-strict language: relcert
lowers `<`/`>` in invariant rows as their closure (`Trusted/InvComponents.lean`), so strict
mutants are not tested. Refuter: sound-by-argument SMT falsifier (not mechanized), see the
script docstring; only Z3 `sat` counts as a refutation. 50 benchmarks, 776 mutants:

| operator | certified | refuted (all declined) | declined, unrefuted | budget exceeded |
|---|---|---|---|---|
| RRO/SNO (<= <-> >=) | 21 | 21 | 117 | 5 |
| MCO (delete conjunct) | 85 | 2 | 66 | 0 |
| ORO (L_x <-> R_x) | 197 | 49 | 188 | 25 |
| total | 303 | 72 | 371 | 30 |

Refuted and certified: 0. Controls: 50/50 unmutated rows certified with the full verdict;
none refuted (40 unrefuted, 10 unknown). "Budget exceeded" = relcert's 40 s search budget
(reported as ERROR), retried at low parallelism with the same outcome.
