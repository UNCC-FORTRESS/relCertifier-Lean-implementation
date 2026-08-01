# How to check the benchmarks are certified — end to end

This is the reproduction recipe. It answers one question: *starting from the
benchmark input files, what exactly do you run, and what should you see, to
confirm that every benchmark carries a machine-checked relational-refinement
theorem?*

Read `README.md` first for what the theorems say. This document is only about
**checking** them.

> **Last full run: 2026-07-31, on `d40788d`. All four checks green.**
> `lake build` 8979 jobs, exit 0 · `relcert-test` ALL PASS ·
> `--run-verdicts` ALL HYPOTHESES DISCHARGED (111/111 `unsat`) ·
> axiom audit 47 theorems: 42 with `z3_unsat_sound`, 5 with the standard three
> alone, **no `sorryAx`, no `native_decide`, no other axioms**.
> Wall clock 12h18m — see *Cost* below before you start it.

---

## 0. The chain being checked

```
benchmarks/suite_uniform/<name>/input.txt        the benchmark, as text
        │  strict parser (Trusted/Parse.lean — IN the trust base)
        ▼
RelCertifier/Instances/BenchIR/<name>.lean       emitted IR literal (`<name>_IR`)
        │  ▲ re-parse + compare: `relcert-test` [ir-drift]   ← check 4
        │
        │  every instance file quotes `<name>_IR` — nothing is re-typed by hand
        ▼
RelCertifier/Instances/<Bench>Modal.lean         the benchmark's Theorem 3 instance
        │  Lean kernel                                        ← check 1
        ▼
`rvalid (theorem3Form …)`                        the ∀∃ refinement statement
        │  #print axioms                                      ← check 2
        ▼
[propext, Classical.choice, Quot.sound] (+ z3_unsat_sound at verdict leaves)
                                                              ← check 3 discharges
                                                                 the verdict leaves
```

Two things are trusted and are **not** discharged by any of the checks below:
the **parser** (text → IR) and the **Z3 leaf** (`z3_unsat_sound`: a printed
query answered `unsat` really is unsatisfiable, which also trusts the SMT
printer). Everything between them is kernel-checked. This is the frozen
hypothesis contract; see `README.md` § *The end-to-end guarantee*.

---

## What you need

A Lean toolchain matching `lean-toolchain` (elan will fetch it), and **Z3 on `PATH`**
for checks 3 and 5 — the Lean-side checks 1, 2 and 4's kernel certificates need no
solver. Nothing else is required: the emitted certificates the theorems consume are
already in the repository.

### Cost — read this before starting check 1

A full `lake build` of this development is **10–14 hours** and peaks near **30 GB**
across ~12 Lean workers. Measured 2026-07-31: 12h18m wall clock, 29.6 GB peak,
8979 jobs. From cold it is longer still, since mathlib compiles first.

The shape of the run matters if you are watching it. Most files clear steadily, then
the last five — the 12-dof instances `refinement_ladder_rover_rung4_8to12`,
`rover_attitude_cone_12dof`, `story3_rollover_base_12dof`,
`story1_attdist_rung_b_12dof`, `story3_rollover_ladder_rung_b` — run 1–3 hours each
and finish roughly one per hour at the very end. A long quiet stretch near the end is
normal, not a hang.

Practical notes:

* Run it detached and log to a file. If you pipe a step through `tail`, nothing
  appears until that step *exits* — use `tee` if you want to watch progress.
* This `lake` version has **no `-j`/`--jobs` flag**; you cannot throttle worker count
  from the command line.
* **Killing `lake build` orphans its Lean workers**, which keep running and holding
  their memory. Always follow up:
  ```bash
  pkill -f "lake build"; pkill -9 -f "leanprover--lean4"
  ```
* To check a single file against already-built dependencies, skip `lake build`
  entirely: `lake env lean <file>` runs one process and reuses the existing oleans.
* Editing a docstring in `Proofs/Encoding/` or `Trusted/` invalidates everything
  downstream and costs a full rebuild. Batch such edits into one sweep.

## Check 1 — the kernel checks every instance proof

```bash
lake build
```

`RelCertifier.lean` imports `RelCertifier/Instances/ModalBattery.lean`, which
imports the modal instance of **every** benchmark. So a clean `lake build`
elaborates and kernel-checks all 47 modal theorems (plus the settling and
throughout families, the proof calculus, and the checker). A green build is the
primary result: no `sorry`, no `admit`, no `native_decide` anywhere in the
development.

The definitive check that nothing is stubbed is the axiom audit below: a
`sorry` anywhere in a proof's dependency graph makes `sorryAx` appear in
`#print axioms`, and it does not appear for any theorem. A grep is available as
a secondary look —

```bash
grep -rn 'sorry\|admit\b\|native_decide' --include='*.lean' RelCertifier/ | grep -v Archive
```

— but read its output carefully: the only current hits are *docstring prose*
("no `native_decide` anywhere", "compose sorry-free"), not tactic uses.

## Check 2 — the axiom audit

`ModalBattery.lean` ends with a `#print axioms` line per benchmark theorem, so
the audit re-emits on every build and cannot drift from the theorems:

```bash
lake build RelCertifier.Instances.ModalBattery 2>&1 | grep -A2 "depends on axioms"
```

Expected, for all 47 theorems (46 benchmarks; `rover3tier_rung12` has two, one
per left mode):

* `[propext, Classical.choice, Quot.sound]` — the three standard Lean axioms;
* plus `RelCertifier.z3_unsat_sound` for the 42 theorems whose flow certificates
  are built from a Z3 verdict.

Five benchmarks are **entirely Z3-free** — the standard three alone, and no
verdict hypotheses in the statement either: `rover3_M1`, `rover_coupled`,
`rover_position`, `refinement_ladder_rover_rung2_6dof`,
`refinement_ladder_rover_rung2b_6dof`. Their responses are pure right-side
flows with the invariant re-established by endpoint arithmetic, so no joint
flow certificate is involved (see `docs/VERDICTS.md` § *FULL SUITE*).

The chain-level audit (`Instances/AxiomCheck.lean`) shows the same for the
generic lemmas: the Z3 leaf enters at `flow_certified` / `segPres_from_flowCert`
and nowhere else.

## Check 3 — discharge the verdict hypotheses

Instances that are not Z3-free carry named `Verd…` hypotheses. Each is a
`Prop` of the form `z3solve (flowQuery …) = Verdict.unsat ∨ …` over the *same*
Lean-side terms the theorem uses — so discharging one means running Z3 on that
query.

```bash
./.lake/build/bin/relcert --run-verdicts      # → "ALL HYPOTHESES DISCHARGED"
```

Measured 2026-07-31 after the runner's table was pinned: **594 queries, 594 `unsat`,
0 failures** — 6 watertank + 105 cut probes + **483 modal**, in three passes of one
command. Every modal instance's verdict pack is now re-run per hypothesis, so the
earlier split (some hypotheses discharged by the runner, the rest deferred to the
tool's coarse `CERTIFIED` line) is gone. Anything the runner cannot rebuild prints
`SKIP` and makes the run exit non-zero; it never silently falls back.

The queries the runner rebuilds are not merely plausible ones: `Verdicts/ModalPinTable`
proves by `rfl`, for each of the 42 verdict packs, that the instance's own `Verd…` **is**
the query the runner's table names. A wrong entry does not compile, so a green line here
is evidence about the theorem's own hypothesis rather than about a lookalike. (The
earlier count of 567 was taken before that pin existed; three of its entries were in
fact rebuilding the wrong query, and a fourth benchmark was not being checked at all —
see `docs/VERDICT-EVIDENCE-AUDIT.md`.)

**What this covers today, precisely:**

* the six `VerdW` hypotheses of `watertank_modal_certified`, each tied to the
  runner's printed query by a *kernel identity theorem* in
  `RelCertifier/Verdicts/Watertank.lean` (`hgW_id`, `hfLW_id`, `hfRW_id`,
  `hdomLW_id`, …) — this is the drift-free form: the query Z3 answers is
  provably the query the theorem names;
* the per-atom O2 route probes for the 13 cut-lifted benchmarks
  (`Verdicts/RunCut.lean`).

**Superseded (kept for context).** Until 2026-07-31 the verdict packs of the other
41 modal instances were NOT in the runner: Each was measured by running its mirror query through the
same printer and Z3 (all `unsat`; results recorded per instance in
`docs/VERDICTS.md`), but they do not yet have kernel identity pins, so a
reviewer re-checking them is re-running a *mirror* of the query rather than a
query provably identical to the theorem's. Folding these into the
`--run-verdicts` battery is routine work, and is the one open hygiene item in
the checking story — it is not a soundness gap in the theorems (the hypotheses
are explicit in the statements). An exhaustive audit of exactly this link —
that every asserted hypothesis is entailed, via domain containment, by queries
the tool demonstrably ran — was performed on 2026-07-31 and is recorded, with
its method, results (210/210), pitfalls, and expiry conditions, in
[`VERDICT-EVIDENCE-AUDIT.md`](VERDICT-EVIDENCE-AUDIT.md).

## Check 4 — the benchmark files match the IR the theorems quote

```bash
lake build relcert-test
./.lake/build/bin/relcert-test               # → "[ir-drift] ... ALL PASS"
```

This re-parses every `benchmarks/suite_uniform/<name>/input.txt` and compares
it to the embedded `<name>_IR` literal that the instances quote. It also
exercises the Z3 layer, the parser's rejection behaviour, and the SMT printer.

Additionally, `Instances/FaithfulCerts.lean` carries kernel `rfl` certificates
tying each IR literal to its transcribed instance data (λ and per-coordinate
scales as explicit metadata) — these are checked by `lake build`, not by a
separate command.

## Check 5 — re-run the tool itself

```bash
lake build relcert
./.lake/build/bin/relcert benchmarks/suite_uniform/watertank/input.txt   # one
./.lake/build/bin/relcert benchmarks/suite_uniform/*/input.txt           # all
```

This is the *search* side: the tool re-derives covers and certificates from the
inputs. It is not needed to believe the theorems (the certificates the theorems
consume are emitted data, checked by `decideCovered` and the kernel), but it
confirms the emitted data in `Instances/Bench*.lean` is what the current tool
produces. 46 of 47 benchmarks certify; `shield_unreachable` reports an
inconclusive Z3 verdict and is therefore outside the certified suite.

---

## Per-benchmark inventory

46 benchmarks, 47 modal theorems. "std 3" = `[propext, Classical.choice,
Quot.sound]`. Hypotheses are exactly the binders of the theorem: `dt` is the
window duration, `Verd…` are the Z3 verdict packs, `ESW` are existence
obligations (watertank's are *proven*, in `WatertankViability.lean`).

| benchmark | instance file | theorem | hypotheses | axioms |
|---|---|---|---|---|
| `arm_chain_rung1` | `ArmChainRung1Modal.lean` | `arm_chain_rung1_modal` | `0 ≤ dt`; `dt ≤ 1/5`; 3×`VerdC` | std 3 + `z3_unsat_sound` |
| `arm_chain_rung2` | `ArmChainRung2Modal.lean` | `arm_chain_rung2_modal` | `0 ≤ dt`; `dt ≤ 1/5`; 4×`VerdD` | std 3 + `z3_unsat_sound` |
| `arm_chain_rung3` | `ArmChainRung3Modal.lean` | `arm_chain_rung3_modal` | `0 ≤ dt`; 2×`Verd3` | std 3 + `z3_unsat_sound` |
| `arm_fidelity_high` | `ArmFidelityHighModal.lean` | `arm_fidelity_high_modal` | `0 ≤ dt`; 2×`Verd3` | std 3 + `z3_unsat_sound` |
| `arm_fidelity_low` | `ArmFidelityLowModal.lean` | `arm_fidelity_low_modal` | `0 ≤ dt`; `dt ≤ 1/5`; 2×`VerdF` | std 3 + `z3_unsat_sound` |
| `arm_fidelity_mid` | `ArmFidelityMidModal.lean` | `arm_fidelity_mid_modal` | `0 ≤ dt`; 2×`Verd3` | std 3 + `z3_unsat_sound` |
| `arm_refinement` | `ArmRefinementModal.lean` | `arm_refinement_modal` | `0 ≤ dt`; `dt ≤ 1/5`; 2×`VerdF` | std 3 + `z3_unsat_sound` |
| `attitude_rate` | `AttitudeRateModal.lean` | `attitude_rate_modal` | `0 ≤ dt`; 2×`VerdW` | std 3 + `z3_unsat_sound` |
| `endurance_gain_M1` | `EnduranceGainM1Modal.lean` | `endurance_gain_M1_modal` | `0 ≤ dt`; 6×`VerdG` | std 3 + `z3_unsat_sound` |
| `endurance_orderlift_1to2` | `EnduranceOrderlift1to2Modal.lean` | `endurance_orderlift_1to2_modal` | `0 ≤ dt`; 1×`VerdO` | std 3 + `z3_unsat_sound` |
| `endurance_orderlift_2to3` | `EnduranceOrderlift2to3Modal.lean` | `endurance_orderlift_2to3_modal` | `0 ≤ dt`; 6×`VerdJ` | std 3 + `z3_unsat_sound` |
| `match_multi_eps` | `MatchMultiEpsModal.lean` | `match_multi_eps_modal` | `0 ≤ dt`; 2×`Verd3` | std 3 + `z3_unsat_sound` |
| `match_multi_rate` | `MatchMultiRateModal.lean` | `match_multi_rate_modal` | `0 ≤ dt`; 4×`VerdM` | std 3 + `z3_unsat_sound` |
| `plant_fan_high` | `PlantFanHighModal.lean` | `plant_fan_high_modal` | `0 ≤ dt`; 2×`Verd3` | std 3 + `z3_unsat_sound` |
| `plant_fan_low` | `PlantFanLowModal.lean` | `plant_fan_low_modal` | `0 ≤ dt`; `dt ≤ 1/5`; 2×`VerdF` | std 3 + `z3_unsat_sound` |
| `plant_fan_mid` | `PlantFanMidModal.lean` | `plant_fan_mid_modal` | `0 ≤ dt`; 2×`Verd3` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung1_2to3` | `RoverLadderRung1Modal.lean` | `rover_ladder_rung1_modal` | `0 ≤ dt`; 6×`VerdE` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung2_3to6` | `RoverLadderRung2Modal.lean` | `rover_ladder_rung2_3to6_modal` | `0 ≤ dt`; 6×`Verd36` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung2_6dof` | `RoverRung26dofModal.lean` | `rung2_6dof_modal` | `0 ≤ dt` | **std 3 only** |
| `refinement_ladder_rover_rung2b_6dof` | `RoverRung2b6dofModal.lean` | `rung2b_6dof_modal` | `0 ≤ dt` | **std 3 only** |
| `refinement_ladder_rover_rung2c_6dof` | `RoverRung2cModal.lean` | `rover_rung2c_modal` | `0 ≤ dt`; 3×`VerdR6` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung3_6to8` | `RoverLadderRung3Modal.lean` | `rover_ladder_rung3_6to8_modal` | `0 ≤ dt`; 6×`VerdR` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung4_8to12` | `RoverLadderRung4Modal.lean` | `rover_ladder_rung4_8to12_modal` | `0 ≤ dt`; 6×`VerdF` | std 3 + `z3_unsat_sound` |
| `robot_braking` | `RobotBrakingModal.lean` | `robot_braking_modal` | `0 ≤ dt`; 1×`Verd3` | std 3 + `z3_unsat_sound` |
| `rover3_M1` | `Rover3M1Modal.lean` | `rover3_M1_modal` | `0 ≤ dt` | **std 3 only** |
| `rover3tier_M1` | `Rover3tierM1Modal.lean` | `rover3tier_M1_modal` | `0 ≤ dt`; 2×`Verd3` | std 3 + `z3_unsat_sound` |
| `rover3tier_rung12` | `Rover3tierRung12Modal.lean` | `rover3tier_rung12_modal_ACCEL` | `0 ≤ dt`; 2×`VerdQA` | std 3 + `z3_unsat_sound` |
| `rover3tier_rung12` | `Rover3tierRung12Modal.lean` | `rover3tier_rung12_modal_COAST` | `0 ≤ dt`; 2×`VerdQC` | std 3 + `z3_unsat_sound` |
| `rover_4d_box` | `Rover4dBoxModal.lean` | `rover_4d_box_modal` | `0 ≤ dt`; 1×`Verd3` | std 3 + `z3_unsat_sound` |
| `rover_attitude_cone_12dof` | `RoverAttitudeConeModal.lean` | `rover_attitude_cone_modal` | `0 ≤ dt`; 6×`VerdC` | std 3 + `z3_unsat_sound` |
| `rover_coupled` | `RoverCoupledModal.lean` | `rover_coupled_modal` | `0 ≤ dt` | **std 3 only** |
| `rover_dof_terrain_rung1` | `RoverDofTerrainRung1Modal.lean` | `rover_dof_terrain_rung1_modal` | `0 ≤ dt`; 6×`VerdE` | std 3 + `z3_unsat_sound` |
| `rover_dof_terrain_rung2` | `RoverDofTerrainRung2Modal.lean` | `rover_dof_terrain_rung2_modal` | `0 ≤ dt`; 6×`VerdT` | std 3 + `z3_unsat_sound` |
| `rover_dof_terrain_rung3` | `RoverDofTerrainRung3Modal.lean` | `rover_dof_terrain_rung3_modal` | `0 ≤ dt`; 6×`VerdW` | std 3 + `z3_unsat_sound` |
| `rover_dof_terrain_rung3_8d` | `RoverDofTerrainRung38dModal.lean` | `rover_dof_terrain_rung3_8d_modal` | `0 ≤ dt`; 6×`VerdU` | std 3 + `z3_unsat_sound` |
| `rover_drag` | `RoverDragModal.lean` | `rover_drag_modal` | `0 ≤ dt`; 1×`VerdRD` | std 3 + `z3_unsat_sound` |
| `rover_position` | `RoverPositionModal.lean` | `rover_position_modal` | `0 ≤ dt` | **std 3 only** |
| `rover_terrain_M1` | `RoverTerrainM1Modal.lean` | `rover_terrain_M1_modal` | `0 ≤ dt`; 6×`VerdT` | std 3 + `z3_unsat_sound` |
| `rover_tier_r1` | `RoverTierR1Modal.lean` | `rover_tier_r1_modal` | `0 ≤ dt`; 1×`VerdX` | std 3 + `z3_unsat_sound` |
| `story1_attdist_rung_a_6to8` | `Story1AttdistRungAModal.lean` | `story1_attdist_rung_a_modal` | `0 ≤ dt`; 9×`VerdD` | std 3 + `z3_unsat_sound` |
| `story1_attdist_rung_b_12dof` | `Story1AttdistRungBModal.lean` | `story1_attdist_rung_b_modal` | `0 ≤ dt`; 6×`VerdF` | std 3 + `z3_unsat_sound` |
| `story2_lateral_rung_a_8dof` | `Story2LateralAModal.lean` | `story2_lateral_rung_a_modal` | `0 ≤ dt`; 6×`VerdY` | std 3 + `z3_unsat_sound` |
| `story2_lateral_rung_b_12dof` | `Story2LateralBModal.lean` | `story2_lateral_rung_b_modal` | `0 ≤ dt`; 6×`VerdZ` | std 3 + `z3_unsat_sound` |
| `story3_rollover_base_12dof` | `Story3RolloverBaseModal.lean` | `story3_rollover_base_modal` | `0 ≤ dt`; 6×`VerdB` | std 3 + `z3_unsat_sound` |
| `story3_rollover_ladder_rung_a` | `Story3RolloverRungAModal.lean` | `story3_rollover_rung_a_modal` | `0 ≤ dt`; 6×`VerdA` | std 3 + `z3_unsat_sound` |
| `story3_rollover_ladder_rung_b` | `Story3RolloverRungBModal.lean` | `story3_rollover_rung_b_modal` | `0 ≤ dt`; 9×`VerdV` | std 3 + `z3_unsat_sound` |
| `watertank` | `WatertankViability.lean` | `watertank_modal_certified` | `dt : ℝ` (unconstrained); 6×`VerdW` — the six pinned to the runner. Existence (`ESW`) is **proven**, not hypothesised | std 3 + `z3_unsat_sound` |

Two rows deserve a note:

* **`rover3tier_rung12`** carries one theorem per left mode (`…_ACCEL`,
  `…_COAST`). Its modes declare *different-shaped* invariants with no
  implication either way, so a single-invariant statement would have to
  weaken one of them; the per-mode form states exactly what the tool certifies.
  Cross-mode handoff is not claimed.
* **`watertank`** is the flagship: existence is proven (not hypothesised) and
  its verdicts are the ones wired into `--run-verdicts` with kernel identity
  pins.

---

## One-shot script

```bash
lake build \
  && lake build relcert relcert-test \
  && ./.lake/build/bin/relcert-test \
  && ./.lake/build/bin/relcert --run-verdicts \
  && lake build RelCertifier.Instances.ModalBattery 2>&1 | grep -A2 "depends on axioms"
```

Green build + `ALL PASS` + `ALL HYPOTHESES DISCHARGED` + an axiom listing with
nothing beyond the standard three and `z3_unsat_sound` = the suite is certified
end to end, modulo the parser and the Z3 leaf.
