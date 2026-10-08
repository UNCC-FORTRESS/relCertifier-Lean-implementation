# Cross-mode handoff — the static implication at every declared left transition

Status: measured 2026-10-08 on branch `mode-handoff` (domain-conditioned query; the
`rover3tier_rung12` rows repaired), Z3 4.15.1, `relcert --handoff
benchmarks/suite_uniform/*/input.txt` (warm persistent session). The 2026-10-07 run with
the domain-FREE query and the original rows is kept below as the record of the failure
that motivated both changes.

**Pruning suite (2026-10-08, branch `pruning-suite`).** `match_multi_rate` gained a
right mode (`STALL`) and the edge `DRIVE → STALL` (`docs/PRUNING.md`); its handoff phase
is untouched (left transitions only: 8/8, vacuous). `shield_unreachable` now lowers for
the certifier (`Trusted/JointVars.lean`) but this runner still reads `p.L.stateVars`
(`Trusted/Handoff.lean` is upstream of the mode-keyed proofs and was not edited), so its
self-loop still reports `handoff query did not lower`, as recorded below.

**Suite deduplication (2026-10-08, branch `dedupe-suite`).** Six duplicate benchmarks
were removed afterwards (`arm_fidelity_high`, `plant_fan_high`, `arm_refinement`,
`plant_fan_low`, `match_multi_eps`, `plant_fan_mid`; `docs/SUITE-DEDUPE.md`), each with
4 declared left transitions, all of them vacuous (rows identical). The handoff phase now
owes **191** queries over the 40 emitted benchmarks (`Coverage.expected.handoff = 191`,
`CoveragePins.derivedHandoff_eq_expected`), 192 over the 41 input files with
`shield_unreachable`'s self-loop; the results table below has been pruned to the current
suite, and the superseded 2026-10-07 table is kept as it was measured. None of the seven
mode-dependent benchmarks was affected.

## What is checked, and why

Seven benchmarks declare a MODE-DEPENDENT relational invariant: a `[relational_invariant]`
block with a different formula per LEFT mode. The tool certifies each left mode's residence
against that mode's own row. A run of the full left program also switches mode, and at a
declared transition `m' → m` (`m ∈ next(m')`) the state is unchanged while the left mode
variable changes. The mode-keyed global invariant

    Φ ≡ ⋀_m (u_L = m → φ_inv(m))

therefore survives the switch exactly when the row implication holds at every state a
switch can occur in. At such a state the left is at the end of an `m'` residence, so it
satisfies `m'`'s evolve domain, and it satisfies `m`'s guard (the switch condition); the
right state satisfies its current mode's evolve domain. The DOMAIN-CONDITIONED implication
is therefore the sound form:

    φ_inv(m') ∧ evolve_{m'}(x_L) ∧ guard_m(x_L) ∧ evolve_R(x_R) → φ_inv(m)

Without it, Φ is not established as a ∀∃ invariant of `L*`, which is what the paper's
Theorem 3 claims for the declared invariant.

`Trusted/Handoff.lean` defines the query once, at the SMT-IR level, as

    UNSAT( φ_inv(m') ∧ evolve_{m'}(x_L) ∧ guard_m(x_L) ∧ evolve_R(x_R) ∧ ¬φ_inv(m) )

over the joint left+right variables (the rows lower through `invComponents`, the certifier's
own invariant lowering; the guard and the domains through `lowerF` on their side, as in
`admissible` and the flow queries). `evolve_R` is the right side's evolve domain under the
suite's uniform-evol discipline — every right mode declares the same evolve, which is what
makes `⋁_q evolve_q` one formula and what the mechanized `hostEvolve … (mR 0)` relies on;
the runner checks that uniformity per benchmark and reports a violation as a failure rather
than picking a mode. The same IR term is what `Verdicts/RunHandoff.lean` prints to Z3 and
what the composition theorem's handoff hypothesis denotes (`ModeHandoff.handoff_of_unsat`
consumes `z3solve (ihandoffQuery …).toHost = unsat` and yields the conditioned implication
that `hstep_modeKeyed` takes: the loop invariant carries `env = domL ∧ domR` and the edge's
test supplies the guard), so the runner and the theorem cannot drift.

Self-loops are checked too (trivially unsat) and counted. A mode-INDEPENDENT invariant (every
row syntactically identical) makes every query vacuous; such benchmarks are still run and
reported as `vacuous`, never skipped.

**Coverage is declared.** `Verdicts/Coverage.expected.handoff = 191` is the suite total (one
query per declared left transition over the 40 emitted benchmarks; 215 over 46 before the
deduplication),
`CoveragePins.derivedHandoff_eq_expected` proves by `decide` that this equals what the emitted
IR declares, and `expectedHandoffFailures` lists the transitions known to fail — now EMPTY;
`CoveragePins.expectedHandoffFailures_declared` proves each entry names a real transition.
The handoff phase of `--run-verdicts` / `--check-quick` is green iff the failure set is
exactly the declared one and all 191 queries came back `unsat`.

## Results — the whole suite (41 inputs; `shield_unreachable` is the documented 41st)

| benchmark | left transitions (checked/declared) | passed | failing transitions | invariant | wall time |
|---|---|---|---|---|---|
| `arm_chain_rung1` | 6/6 | 6 | - | vacuous (rows identical) | 102 ms |
| `arm_chain_rung2` | 7/7 | 7 | - | vacuous (rows identical) | 5 ms |
| `arm_chain_rung3` | 4/4 | 4 | - | vacuous (rows identical) | 3 ms |
| `arm_fidelity_low` | 4/4 | 4 | - | vacuous (rows identical) | 3 ms |
| `arm_fidelity_mid` | 4/4 | 4 | - | vacuous (rows identical) | 2 ms |
| `attitude_rate` | 1/1 | 1 | - | vacuous (rows identical) | 0 ms |
| `endurance_gain_M1` | 7/7 | 7 | - | vacuous (rows identical) | 4 ms |
| `endurance_orderlift_1to2` | 8/8 | 8 | - | vacuous (rows identical) | 6 ms |
| `endurance_orderlift_2to3` | 7/7 | 7 | - | vacuous (rows identical) | 5 ms |
| `match_multi_rate` | 8/8 | 8 | - | vacuous (rows identical) | 4 ms |
| `refinement_ladder_rover_rung1_2to3` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung2_3to6` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung2_6dof` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung2b_6dof` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung2c_6dof` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung3_6to8` | 5/5 | 5 | - | vacuous (rows identical) | 4 ms |
| `refinement_ladder_rover_rung4_8to12` | 5/5 | 5 | - | vacuous (rows identical) | 5 ms |
| `robot_braking` | 1/1 | 1 | - | vacuous (rows identical) | 1 ms |
| `rover3_M1` | 5/5 | 5 | - | mode-dependent | 8 ms |
| `rover3tier_M1` | 4/4 | 4 | - | vacuous (rows identical) | 2 ms |
| `rover3tier_rung12` | 4/4 | 4 | - | mode-dependent | 4 ms |
| `rover_4d_box` | 1/1 | 1 | - | vacuous (rows identical) | 1 ms |
| `rover_attitude_cone_12dof` | 5/5 | 5 | - | vacuous (rows identical) | 5 ms |
| `rover_coupled` | 5/5 | 5 | - | mode-dependent | 6 ms |
| `rover_dof_terrain_rung1` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `rover_dof_terrain_rung2` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `rover_dof_terrain_rung3` | 5/5 | 5 | - | vacuous (rows identical) | 5 ms |
| `rover_dof_terrain_rung3_8d` | 5/5 | 5 | - | vacuous (rows identical) | 4 ms |
| `rover_drag` | 1/1 | 1 | - | vacuous (rows identical) | 1 ms |
| `rover_position` | 5/5 | 5 | - | mode-dependent | 6 ms |
| `rover_terrain_M1` | 7/7 | 7 | - | vacuous (rows identical) | 4 ms |
| `rover_tier_r1` | 1/1 | 1 | - | vacuous (rows identical) | 0 ms |
| `shield_unreachable` | 1/1 | 0 | 0->0 | vacuous (rows identical) | 0 ms |
| `story1_attdist_rung_a_6to8` | 5/5 | 5 | - | mode-dependent | 4 ms |
| `story1_attdist_rung_b_12dof` | 5/5 | 5 | - | mode-dependent | 5 ms |
| `story2_lateral_rung_a_8dof` | 5/5 | 5 | - | vacuous (rows identical) | 4 ms |
| `story2_lateral_rung_b_12dof` | 5/5 | 5 | - | vacuous (rows identical) | 4 ms |
| `story3_rollover_base_12dof` | 5/5 | 5 | - | vacuous (rows identical) | 4 ms |
| `story3_rollover_ladder_rung_a` | 5/5 | 5 | - | vacuous (rows identical) | 5 ms |
| `story3_rollover_ladder_rung_b` | 5/5 | 5 | - | mode-dependent | 5 ms |
| `watertank` | 6/6 | 6 | - | vacuous (rows identical) | 3 ms |

Totals (as measured on the 46-benchmark suite): 216 transitions checked over the 47 input
files (215 over the 46 emitted benchmarks plus `shield_unreachable`'s single self-loop),
215 unsat; after the deduplication, 192 over 41 input files, 191 over the 40 emitted
benchmarks, 191 unsat (re-run 2026-10-08, branch `dedupe-suite`). The one FAIL is
`shield_unreachable`'s self-loop: its right side declares a state variable (`w`) the left
does not, so the right evolve domain does not lower against the left's variable list and the
query cannot be built — reported, never skipped. It is the 47th benchmark, outside the
emitted suite (`benchIRTable`), so the `--run-verdicts` phase (40 benchmarks, 191 queries) is
unaffected; `--handoff` over all 47 input files exits 1 on it by design (the raw check fails
on anything that is not `unsat`).

The seven mode-dependent benchmarks under the domain-conditioned query:

| benchmark | per-mode rows | handoff | how the Lean side discharges it |
|---|---|---|---|
| `rover3_M1` | Drive 0.5 ⊂ Drift 1.0 ⊂ Stop 2.0 (nested offsets) | 5/5 pass | in-kernel (`linarith` on the lowered offsets) |
| `rover_coupled` | same three rows | 5/5 pass | in-kernel |
| `rover_position` | same three rows | 5/5 pass | in-kernel |
| `story1_attdist_rung_a_6to8` | STEEP = common ∧ `v[l] ≤ v[r]`; MODER = FLAT = common | 5/5 pass | in-kernel (`FM_mono`) |
| `story1_attdist_rung_b_12dof` | same nesting | 5/5 pass | in-kernel |
| `story3_rollover_ladder_rung_b` | same nesting | 5/5 pass | in-kernel |
| `rover3tier_rung12` (rows repaired, see below) | ACCEL = `v[l] ≤ v[r]+0.5 ∧ 3v[l]+a[l] ≤ 3v[r]+1.2`; COAST = `3v[l]+a[l] ≤ 3v[r]+1.2` | **4/4 pass** | in-kernel: ACCEL → COAST drops a conjunct; COAST → ACCEL uses the evolve floor `a[l] ≥ −0.3` (`linarith`) — the domain-conditioned form is what makes this direction hold |

## The `rover3tier_rung12` repair (2026-10-08) — rows only

Constraint set by the task: the only permitted change is the `[relational_invariant]` block;
dynamics, guards and evolve domains are untouched (the file's `diff` is the two ACCEL-row
lines plus a comment).

**Why the original rows cannot compose.** ACCEL = `v[l] ≤ v[r] + 0.5 ∧ a[l] ≤ a[r] + 0.8`
leaves `3·0.5 + 0.8 = 2.3` of slack on the functional `3v + a`, but COAST bounds that
functional by `1.2`. Inside the evolve domains the gap is still `≥ 0.15` (witness
`L_v = 5/4, L_a = 0, R_v = 13/16, R_a = 3/4`), so `ACCEL → COAST` fails under the
domain-conditioned query too. `COAST → ACCEL` held already once conditioned (`a[l] ≥ −0.3`
gives the `v` bound; `a[l] ≤ 0.95 ≤ a[r] + 0.8` from `a[r] ≥ 0.5`).

**Candidates tried** (rows only; each run through `relcert` for the per-mode covers and
through Z3 for both conditioned handoffs):

| candidate | ACCEL row | ACCEL → COAST | COAST → ACCEL | per-mode covers | λ (ACCEL / COAST) |
|---|---|---|---|---|---|
| A1 (adopted) | `v[l] ≤ v[r] + 0.5 ∧ 3v[l] + a[l] ≤ 3v[r] + 1.2` (COAST row unchanged) | unsat | unsat | CERTIFIED (both windows) | 7/4 (budget 6) / 1 (budget 4) — the search's first grid point; the Lean instance keeps λ = 2 (budget 7), at which both components' route-A queries are unsat |
| A2 (rejected) | `v[l] ≤ v[r] + 0.2 ∧ a[l] ≤ a[r] + 0.6` (slacks tightened so `3·δv + δa = 1.2`) | **sat** | **sat** (`L_v = 1/2, L_a = 0, R_v = 1/4, R_a = 3/4`) | CERTIFIED | 2 / 1 |

A2 shows why no per-variable slack form can work: the COAST functional subtracts `a_R`
(`3v_L + a_L ≤ 3v_R + 1.2` has no `a_R` on the right), so `a_L ≤ a_R + δa` gives
`3v_L + a_L ≤ 3v_R + 3δv + a_R + δa` — the `a_R ≥ 0.5` term is never absorbed, whatever
the constants. The only row-only repair is to bound the same functional in ACCEL, which A1
does with COAST's own constant (no new number is introduced). The modelling story is kept:
the patrol cycle `ACCEL ↔ COAST`, safety on `s` (never part of the rows), and the velocity
envelope `v[l] ≤ v[r] + d` in ACCEL; what changes is that ACCEL's second conjunct is the
lifted-M1 functional bound rather than a separate acceleration offset.

**Per-mode certification at the new row** (ACCEL window, λ = 2 as in the Lean instance):
`Lie(v_L − v_R − 0.5) = a_L − 2a_R ≤ 0.95 − 1 < 0` and
`Lie(3v_L + a_L − 3v_R − 1.2) = 3a_L + 3(0.8 − a_L) − 6a_R = 2.4 − 6a_R ≤ −0.6 < 0` on the
evolve domains — route A, both right modes (both have `a' = 0`, `a_R ∈ [0.5, 1]`). The runner
re-checks `VerdQA 0/1` at the new row (rows 18/19 of `RunModal.modalTable`, unchanged
shape: two components, λ = 2 / λ = 1).

**What was regenerated from the new file** (all GENERATED leaves, re-emitted by the tool):
`Instances/BenchIR/rover3tier_rung12.lean` (`--emit-ir`), `Instances/BenchCovers/` and
`BenchCoversNC/rover3tier_rung12.lean` (`--emit-cover`, with/without cuts: ACCEL now at
λ = 7/4, budget 6, strata order `[1, 0]`, COAST's pre-reposition flag off),
`Instances/Throughout/rover3tier_rung12.lean` (`scripts/gen_throughout.py` repointed at the
per-benchmark leaves, whose strata-order regex was fixed on the way — the non-identity order
`[1, 0]` now goes through `mem_equiv_of_index_perm`, with one hand-added length lemma the
`decide` side condition needs). `BenchCoverReplay` re-replays the new cover by `decide`,
`FaithfulCerts` re-checks the IR by `rfl`, `relcert-test`'s `[ir-drift]` compares the literal
to the file. The two per-left-mode modal theorems (`Instances/Rover3tierRung12Modal.lean`)
are atom-agnostic and re-elaborate unchanged; the composed theorem is
`Rover3tierRung12Handoff.rover3tier_rung12_modeKeyed`.

## Re-running

    ./.lake/build/bin/relcert --handoff benchmarks/suite_uniform/*/input.txt   # per benchmark, exit 1 on any non-unsat (incl. shield_unreachable)
    ./.lake/build/bin/relcert --run-verdicts                                    # phase 4 = handoff over the 40 emitted benchmarks, 191/191 owed

## Record: the 2026-10-07 run — domain-FREE query, original `rover3tier_rung12` rows (superseded)

> Kept as the record of the failure that motivated the conditioned query and the row
> repair. Numbers and the rung12 analysis below describe the ORIGINAL file and query.


| benchmark | left transitions (checked/declared) | passed | failing transitions | invariant | wall time |
|---|---|---|---|---|---|
| `arm_chain_rung1` | 6/6 | 6 | - | vacuous (rows identical) | 91 ms |
| `arm_chain_rung2` | 7/7 | 7 | - | vacuous (rows identical) | 5 ms |
| `arm_chain_rung3` | 4/4 | 4 | - | vacuous (rows identical) | 4 ms |
| `arm_fidelity_high` | 4/4 | 4 | - | vacuous (rows identical) | 2 ms |
| `arm_fidelity_low` | 4/4 | 4 | - | vacuous (rows identical) | 3 ms |
| `arm_fidelity_mid` | 4/4 | 4 | - | vacuous (rows identical) | 3 ms |
| `arm_refinement` | 4/4 | 4 | - | vacuous (rows identical) | 3 ms |
| `attitude_rate` | 1/1 | 1 | - | vacuous (rows identical) | 1 ms |
| `endurance_gain_M1` | 7/7 | 7 | - | vacuous (rows identical) | 4 ms |
| `endurance_orderlift_1to2` | 8/8 | 8 | - | vacuous (rows identical) | 5 ms |
| `endurance_orderlift_2to3` | 7/7 | 7 | - | vacuous (rows identical) | 5 ms |
| `match_multi_eps` | 4/4 | 4 | - | vacuous (rows identical) | 3 ms |
| `match_multi_rate` | 8/8 | 8 | - | vacuous (rows identical) | 4 ms |
| `plant_fan_high` | 4/4 | 4 | - | vacuous (rows identical) | 2 ms |
| `plant_fan_low` | 4/4 | 4 | - | vacuous (rows identical) | 2 ms |
| `plant_fan_mid` | 4/4 | 4 | - | vacuous (rows identical) | 2 ms |
| `refinement_ladder_rover_rung1_2to3` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung2_3to6` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung2_6dof` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung2b_6dof` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung2c_6dof` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung3_6to8` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `refinement_ladder_rover_rung4_8to12` | 5/5 | 5 | - | vacuous (rows identical) | 4 ms |
| `robot_braking` | 1/1 | 1 | - | vacuous (rows identical) | 1 ms |
| `rover3_M1` | 5/5 | 5 | - | mode-dependent | 5 ms |
| `rover3tier_M1` | 4/4 | 4 | - | vacuous (rows identical) | 2 ms |
| `rover3tier_rung12` | 4/4 | 2 | 0->1, 1->0 | mode-dependent | 175 ms |
| `rover_4d_box` | 1/1 | 1 | - | vacuous (rows identical) | 1 ms |
| `rover_attitude_cone_12dof` | 5/5 | 5 | - | vacuous (rows identical) | 5 ms |
| `rover_coupled` | 5/5 | 5 | - | mode-dependent | 6 ms |
| `rover_dof_terrain_rung1` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `rover_dof_terrain_rung2` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `rover_dof_terrain_rung3` | 5/5 | 5 | - | vacuous (rows identical) | 4 ms |
| `rover_dof_terrain_rung3_8d` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `rover_drag` | 1/1 | 1 | - | vacuous (rows identical) | 0 ms |
| `rover_position` | 5/5 | 5 | - | mode-dependent | 5 ms |
| `rover_terrain_M1` | 7/7 | 7 | - | vacuous (rows identical) | 5 ms |
| `rover_tier_r1` | 1/1 | 1 | - | vacuous (rows identical) | 1 ms |
| `shield_unreachable` | 1/1 | 1 | - | vacuous (rows identical) | 1 ms |
| `story1_attdist_rung_a_6to8` | 5/5 | 5 | - | mode-dependent | 4 ms |
| `story1_attdist_rung_b_12dof` | 5/5 | 5 | - | mode-dependent | 4 ms |
| `story2_lateral_rung_a_8dof` | 5/5 | 5 | - | vacuous (rows identical) | 4 ms |
| `story2_lateral_rung_b_12dof` | 5/5 | 5 | - | vacuous (rows identical) | 4 ms |
| `story3_rollover_base_12dof` | 5/5 | 5 | - | vacuous (rows identical) | 4 ms |
| `story3_rollover_ladder_rung_a` | 5/5 | 5 | - | vacuous (rows identical) | 3 ms |
| `story3_rollover_ladder_rung_b` | 5/5 | 5 | - | mode-dependent | 3 ms |
| `watertank` | 6/6 | 6 | - | vacuous (rows identical) | 3 ms |

Totals: 216 transitions checked over the 47 input files (215 over the 46 emitted benchmarks
plus `shield_unreachable`'s single self-loop), 214 unsat, 2 sat — both in
`rover3tier_rung12`. Whole run 1.97 s wall.

The seven mode-dependent benchmarks:

| benchmark | per-mode rows | handoff | how the Lean side discharges it |
|---|---|---|---|
| `rover3_M1` | Drive 0.5 ⊂ Drift 1.0 ⊂ Stop 2.0 (nested offsets) | 5/5 pass | in-kernel (`linarith` on the lowered offsets) |
| `rover_coupled` | same three rows | 5/5 pass | in-kernel |
| `rover_position` | same three rows | 5/5 pass | in-kernel |
| `story1_attdist_rung_a_6to8` | STEEP = common ∧ `v[l] ≤ v[r]`; MODER = FLAT = common | 5/5 pass | in-kernel (STEEP → MODER drops a conjunct; MODER → FLAT identical rows) |
| `story1_attdist_rung_b_12dof` | same nesting | 5/5 pass | in-kernel |
| `story3_rollover_ladder_rung_b` | same nesting | 5/5 pass | in-kernel |
| `rover3tier_rung12` | ACCEL = `v[l] ≤ v[r]+0.5 ∧ a[l] ≤ a[r]+0.8`; COAST = `3v[l]+a[l] ≤ 3v[r]+1.2` (incomparable) | **2/4 pass** — both cross transitions FAIL | not composable; per-left-mode theorems stand (see below) |

For the six that pass, every declared transition is either a self-loop, a step to an
identical row, or a step that drops a conjunct / widens a constant offset — so the Lean
handoff facts need no Z3 verdict at all and the composed theorems add no hypothesis beyond
the per-mode packs (the rover trio stays entirely Z3-free).

### `rover3tier_rung12` under the original rows and the domain-free query — the failing implications, with countermodels

Declared left transitions: ACCEL → {COAST, ACCEL}, COAST → {ACCEL, COAST}. The two
self-loops pass. The two cross transitions fail:

**ACCEL → COAST** (`0 → 1`). Query: `v_L ≤ v_R + 0.5 ∧ a_L ≤ a_R + 0.8 ∧ (1.0 ≤ v_L < 1.3)
∧ ¬(3v_L + a_L ≤ 3v_R + 1.2)`. Z3: `sat`. Countermodel (from the runner):

    L_v = 5/4, L_a = 7/10, R_v = 3/4, R_a = -1/10, L_s = R_s = 0

Check: `5/4 ≤ 3/4 + 1/2` ✓, `7/10 ≤ -1/10 + 8/10` ✓, guard `1 ≤ 5/4 < 1.3` ✓, but
`3·5/4 + 7/10 = 4.45 > 3·3/4 + 1.2 = 3.45`. The ACCEL row allows a `0.5` velocity gap and a
`0.8` acceleration gap; the COAST functional allows only `1.2` on `3v + a`, i.e. the ACCEL
row's slack (`3·0.5 + 0.8 = 2.3`) exceeds it by `1.1`. This failure is robust: conjoining
both sides' evolve domains (`a_R ∈ [0.5, 1]`, `a_L ∈ [-0.3, 0.95]`, …) still gives `sat`
(witness `L_v = 5/4, L_a = 0, R_v = 13/16, R_a = 3/4`: `3·5/4 + 0 = 3.75 > 3·13/16 + 1.2 =
3.6375`). It is a genuine gap between the two declared rows, not an artefact of the
domain-free query.

**COAST → ACCEL** (`1 → 0`). Query: `3v_L + a_L ≤ 3v_R + 1.2 ∧ (0.3 ≤ v_L < 1.0)
∧ ¬(v_L ≤ v_R + 0.5 ∧ a_L ≤ a_R + 0.8)`. Z3: `sat`. Countermodel:

    L_v = 1/2, L_a = -33/10, R_v = -1, R_a = -41/10, L_s = R_s = 0

Here the witness sits outside the evolve domains (`a_L = -3.3 < -0.3`, `R_v = -1 < 0`). With
both evolve domains conjoined the implication IS valid (`unsat`): from `3v_L + a_L ≤ 3v_R +
1.2` and `a_L ≥ -0.3` follows `v_L ≤ v_R + 0.5`, and `a_L ≤ 0.95 ≤ 0.5 + 0.8 ≤ a_R + 0.8`.
So this direction fails only the domain-free form; a domain-conditioned handoff hypothesis
would discharge it. Recorded for completeness — it does not rescue the benchmark, because
`ACCEL → COAST` fails either way.

**Consequence.** The mode-keyed invariant `(u_L = ACCEL → row_ACCEL) ∧ (u_L = COAST →
row_COAST)` is NOT a ∀∃ invariant of the full `rover3tier_rung12` left program as declared:
after an `ACCEL → COAST` switch the COAST row need not hold. Per the task rules the benchmark
is left as is (model and invariant untouched). Its Lean statement stays the pair of
per-left-mode theorems `rover3tier_rung12_modal_ACCEL` / `rover3tier_rung12_modal_COAST`
(`Instances/Rover3tierRung12Modal.lean`), each a within-residence claim at its own row, and
the composition theorem is not instantiated for it. A repair would have to widen the COAST
row to at least `3v[l] + a[l] ≤ 3v[r] + 2.3` (or tighten ACCEL's), which is a modelling
decision for the benchmark's author.

### Re-running (unchanged commands)

    ./.lake/build/bin/relcert --handoff benchmarks/suite_uniform/*/input.txt   # per benchmark, exit 1 on any failure
    ./.lake/build/bin/relcert --run-verdicts                                    # phase 4 = handoff, declared failures tolerated

`--handoff` exits non-zero whenever any transition fails (it is the raw check);
`--run-verdicts` / `--check-quick` accept exactly the declared failure set and nothing else.
