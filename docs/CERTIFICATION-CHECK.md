# How to check the benchmarks are certified — end to end

This is the reproduction recipe. It answers one question: *starting from the
benchmark input files, what exactly do you run, and what should you see, to
confirm that every benchmark carries a machine-checked relational-refinement
theorem?*

Read `README.md` first for what the theorems say. This document is only about
**checking** them.

> **Last full run: 2026-08-02, on `920f79c`, from a cold tree. All four checks green.**
> `lake build` 8988 jobs, exit 0, **12h59m from cold** · `relcert-test` ALL PASS (with
> `BENCH_PATHS` set, so the two Z3-determinism checks ran rather than skipping) ·
> `--run-verdicts` ALL HYPOTHESES DISCHARGED (594/594 `unsat`, coverage 6/105/483) ·
> axiom audit 47 theorems: 42 with `z3_unsat_sound`, 5 with the standard three
> alone, **no `sorryAx`, no `native_decide`, no other axioms** ·
> full suite 46 CERTIFIED, 0 DECLINED, `shield_unreachable` inconclusive as documented.
> See *Cost* below before you start one. **This cold run and the two branch runs below
> predate the 2026-10-08 suite deduplication** (46 benchmarks then; 40 now —
> `docs/SUITE-DEDUPE.md`). The current numbers are in the `dedupe-suite` entry.
>
> **Branch `mode-handoff` (2026-10-08):** `lake build` exit 0 (warm; only new leaves and
> the `rover3tier_rung12` column) · `relcert-test` ALL PASS · `--run-verdicts` 848/848
> `unsat`, coverage 6/105/522/215, no declared handoff failure · axiom audit **54**
> theorems: 46 with `z3_unsat_sound`, 8 standard-three · `--check-quick` PASSED. The
> domain-conditioned handoff phase, seven composed theorems and the `rover3tier_rung12`
> row repair: `docs/HANDOFF.md`, `docs/PAPER-MAPPING.md` §2b.
>
> **Branch `cut-composition` (2026-10-08):** `lake build` 9007 jobs, exit 0 (warm; the
> new leaves and `ModalBattery` only) · `--check-quick` 46 CERTIFIED, 0 DECLINED, 1
> documented error, 6/105/522/215, QUICK CHECKS PASSED · `relcert-test` ALL PASS (with
> `BENCH_PATHS`) · `--run-verdicts` 848/848 `unsat` · axiom audit **59** theorems: 46 with
> `z3_unsat_sound`, 13 standard-three (the five `…_declared` theorems among them), no
> `sorryAx`, no other axiom. The five checked-cut benchmarks at their declared invariant:
> `docs/CUT-COMPOSITION.md`, `docs/PAPER-MAPPING.md` §2c.
>
> **Branch `pruning-suite` (2026-10-08):** `match_multi_rate` declares a pruned
> stall fallback (`docs/PRUNING.md`). `lake build` 8976 jobs, exit 0 (warm) ·
> `--check-quick` **40 CERTIFIED, 1 DECLINED (`shield_unreachable`, now lowering and
> declared as declined), 0 errors — matches the declared suite**, coverage
> 6/97/504/191/**2** (+ 1 pruned edge), QUICK CHECKS PASSED · `relcert-test` ALL PASS
> (with `BENCH_PATHS`; 40 IR literals match their files) · `--run-verdicts` 800/800
> `unsat`, ALL HYPOTHESES DISCHARGED · axiom audit **52** theorems: 42 with
> `z3_unsat_sound`, 10 standard-three, no `sorryAx`, no other axiom · `--handoff` 192
> transitions over 41 inputs, 191 unsat, the documented `shield_unreachable` FAIL ·
> `RELCERT_NO_PRUNE=1 relcert …/match_multi_rate/input.txt` DECLINED.
>
> **Branch `suite-redesign` (2026-10-09) — current: the static reposition removed**
> (`docs/COVER-AUDIT.md`, note of 2026-10-09). `lake build` exit 0, `Build completed
> successfully (8948 jobs)` (warm; the throughout batteries rebuilt, heavy files serially),
> no `sorry` · `lake build relcert relcert-test` 17661 jobs · `--check-quick` **34
> CERTIFIED, 7 DECLINED (`shield_unreachable` and the six declined after static-reposition
> removal), 0 errors — matches the declared suite**, coverage 97/486/163/2 (+ 1 pruned
> edge), QUICK CHECKS PASSED · `relcert-test` ALL PASS (with `BENCH_PATHS`; 40 IR
> literals match their files) · axiom audit **46** theorems: 36 with `z3_unsat_sound`, 10
> standard-three, no `sorryAx`, no other axiom.
>
> **Branch `dedupe-suite` (2026-10-08):** six duplicate benchmarks removed
> (`docs/SUITE-DEDUPE.md`). `lake build` 8969 jobs, exit 0 (warm) · `--check-quick`
> **40 CERTIFIED, 0 DECLINED, 1 documented error — matches the declared suite**,
> coverage 6/97/504/191, QUICK CHECKS PASSED · `relcert-test` ALL PASS (with
> `BENCH_PATHS`; 40 IR literals match their files) · `--run-verdicts` 798/798 `unsat`,
> ALL HYPOTHESES DISCHARGED · axiom audit **50** theorems: 40 with `z3_unsat_sound`, 10
> standard-three, no `sorryAx`, no other axiom · `--handoff` 192 transitions over 41
> inputs, 191 unsat, the documented `shield_unreachable` FAIL.

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

A full `lake build` of this development is **13–14 hours** and peaks near **30 GB**
across ~12 Lean workers. Two measurements:

* **From cold** (2026-08-02, `920f79c`): **12h59m**, 8988 jobs, exit 0. "Cold" means
  `lake clean` had wiped this package *and* its dependencies, so the run recompiles
  dL-rel and the Mathlib subset this development imports before it reaches
  `RelCertifier/` — roughly the first 8000 of those jobs. Peak memory was not
  instrumented on this run.
* **Warm dependencies** (2026-07-31): 12h18m, 29.6 GB peak, at 8979 jobs.

The two are closer than you might expect. The Mathlib subset pulled in here is small
next to the 12-dof instances, which dominate the wall clock either way.

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

## The four checks at a glance

| # | what it establishes | command |
|---|---|---|
| 1 | the Lean proofs kernel-check | `lake build` (~13 h) |
| 2 | no hidden axioms | `lake build RelCertifier.Instances.ModalBattery` |
| 3 | the Z3 hypotheses hold (incl. the cross-mode handoff phase) | `./.lake/build/bin/relcert --run-verdicts` |
| 4 | parser/printer/IR-drift/determinism | `BENCH_PATHS=<manifest> ./.lake/build/bin/relcert-test` |
| — | the benchmarks still certify | `./.lake/build/bin/relcert benchmarks/suite_uniform/*/input.txt` |

Checks 3 and the certification run are bundled by

```bash
./.lake/build/bin/relcert --check-quick benchmarks/suite_uniform/*/input.txt
```

which certifies the suite, compares the tally against `Verdicts/Coverage.expectedSuite`
(34 certified, 7 declined — the documented `shield_unreachable` and the six declined
after the static-reposition removal of 2026-10-09 — 0 errors), then
discharges every hypothesis with its coverage counts, and exits non-zero if either half
fails. It deliberately does
*not* run check 1 — a 13-hour build does not belong behind a flag named "quick" — and
does not run check 4, which lives in a separate binary. `relcert --help` says so.

`relcert` rejects unknown options rather than treating them as benchmark paths: a
mistyped `--run-verdict` reports `unknown option` and exits 2, instead of complaining
that a *file* by that name is missing.

## Check 1 — the kernel checks every instance proof

```bash
lake build
```

`RelCertifier.lean` imports `RelCertifier/Instances/ModalBattery.lean`, which
imports the modal instance of **every** benchmark. So a clean `lake build`
elaborates and kernel-checks all 41 base modal theorems, the 7 mode-keyed, the 2
cut-composed ones, the pruning-suite theorem of `match_multi_rate` and its Theorem 2
instance (plus the settling and throughout families, the proof calculus, and the
checker). A green build is the
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
lake build RelCertifier.Instances.ModalBattery 2>&1 | grep -A3 "depends on axioms"
```

(`-A3`, not `-A2`: Lean prints a four-axiom list over four lines, and `-A2` drops the
last one — the line that says `z3_unsat_sound`. With `-A2` every theorem reads as
standard-three. Found 2026-10-08; the earlier recipe said `-A2`.)

Expected, for all 52 theorems (40 benchmarks; `rover3tier_rung12` has two, one
per left mode; seven benchmarks have a mode-keyed theorem as well; the two
checked-cut benchmarks have a declared-invariant theorem as well; `match_multi_rate`
has the pruning-suite theorem over its two-mode automaton and the Theorem 2 instance
of its pruned edge as well):

* `[propext, Classical.choice, Quot.sound]` — the three standard Lean axioms;
* plus `RelCertifier.z3_unsat_sound` for the 42 theorems whose flow certificates
  are built from a Z3 verdict (36 base theorems, 4 mode-keyed ones, and the two
  `match_multi_rate` pruning-suite theorems).

Five benchmarks are **entirely Z3-free** — the standard three alone, and no
verdict hypotheses in the statement either: `rover3_M1`, `rover_coupled`,
`rover_position`, `refinement_ladder_rover_rung2_6dof`,
`refinement_ladder_rover_rung2b_6dof`. The three composed rover theorems and the
two `…_declared` theorems are Z3-free as well (10 standard-three lines in all). Their responses are pure right-side
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

**Coverage is declared, not inferred.** A runner that issues *fewer* queries than it
owes looks identical to one that issued them all — every line it does print says
`UNSAT`. That is how three defects passed green on 2026-07-31: `rover_drag` issued no
query at all, `rover_rung2c` issued 3 where 27 were owed, and `rover3tier_rung12`'s
Accel row issued 1 per pair instead of 2. So `Verdicts/Coverage.lean` declares the
per-phase totals and `--run-verdicts` checks them:

```
  [coverage] cut probes: 97/97 hypotheses discharged
  [coverage] modal: 486/486 hypotheses discharged
  [coverage] handoff: 163/163 hypotheses discharged
  [coverage] non-connection: 2/2 hypotheses discharged
  [coverage] pruned edges: 1/1 hypotheses discharged
```

(The fifth phase, **non-connection** (2026-10-08, `docs/PRUNING.md`), re-runs the two
pruning queries of every pruned edge the emitted covers record — one edge, `DRIVE →
STALL` of `match_multi_rate`; `Verdicts/RunNonConn.lean`, counts derived from the cover
table by `CoveragePins`, the rebuilt pair pinned to the instance's `VerdNC` by
`Verdicts/NonConnPins.lean`. The modal count moved from 483 to 522 on 2026-10-07 with the five packs of the
mode-keyed instances, runner rows 42–46 — rows 36–40 since the deduplication. The fourth
phase is the cross-mode **handoff** check: one domain-conditioned query per declared left
transition of every emitted benchmark, 215 in all before the deduplication; it is green
only on exactly the declared failure set, which is empty since the `rover3tier_rung12`
row repair of 2026-10-08. `docs/HANDOFF.md`. The 2026-10-08 deduplication removed six
benchmarks and with them 18 modal queries, 8 cut probes and 24 handoff transitions:
6 / 97 / 504 / 191, re-derived by `CoveragePins`. `docs/SUITE-DEDUPE.md`. The 2026-10-09
static-reposition removal made six benchmarks DECLINED and removed their packs: the
`watertank` phase (6) is gone, modal 504 → 486, handoff 191 → 163; cut probes, pruned
edges and non-connection unchanged. `docs/COVER-AUDIT.md`, note of 2026-10-09.)

A mismatch either way fails the run. And the declared totals are themselves checked:
`Verdicts/CoveragePins.lean` derives each from the table that generates the work —
mode pairs × components for the modal phase, tagged atoms per side for the cut probes —
and proves the derived value equals the declared one. So `Coverage.expected` cannot be
quietly re-pointed at whatever a run happened to produce; changing it without changing
the suite fails the build, and vice versa.

The queries the runner rebuilds are not merely plausible ones: `Verdicts/ModalPinTable`
proves by `rfl`, for each verdict pack (36 base packs and 5 mode-keyed), that the instance's own `Verd…` **is**
the query the runner's table names. A wrong entry does not compile, so a green line here
is evidence about the theorem's own hypothesis rather than about a lookalike; the pins
quote `dim`/`invRow`/`order` from the runner's table row, and `Verdicts/ModalTablePins`
pins the rest of the row, so corrupting a field fails the build. (The
earlier count of 567 was taken before that pin existed; three of its entries were in
fact rebuilding the wrong query, and a fourth benchmark was not being checked at all —
see `docs/VERDICT-EVIDENCE-AUDIT.md`.)

**What this covers today, precisely:**

* (until 2026-10-09: the six `VerdW` hypotheses of `watertank_modal_certified`, tied to
  the runner's printed query by kernel identity theorems in `Verdicts/Watertank.lean`;
  both files were deleted when `suite_uniform/watertank` became DECLINED after the
  static-reposition removal);
* the per-atom O2 route probes for the 11 cut-lifted benchmarks
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
# BENCH_PATHS is a TSV of  <benchmark name><TAB><absolute path to input.txt>
for d in benchmarks/suite_uniform/*/; do
  printf '%s\t%s\n' "$(basename "$d")" "$PWD/$d/input.txt"
done > /tmp/bench-paths.tsv
BENCH_PATHS=/tmp/bench-paths.tsv ./.lake/build/bin/relcert-test   # → "ALL PASS"
```

This re-parses every `benchmarks/suite_uniform/<name>/input.txt` and compares
it to the embedded `<name>_IR` literal that the instances quote. It also
exercises the Z3 layer, the parser's rejection behaviour, and the SMT printer.

**Set `BENCH_PATHS`.** Without it the two Z3-determinism checks (the same query
answered identically 8× on a warm session, for one CERTIFIED and one DECLINED
benchmark) cannot find their inputs and do not run. A complete run prints a bare
`ALL PASS`; a run that skipped them says `ALL PASS (2 SKIPPED — set BENCH_PATHS
to run them)`. Read the final line, not just the words "ALL PASS".

Additionally, `Instances/FaithfulCerts.lean` carries kernel `rfl` certificates
tying each IR literal to its transcribed instance data (λ and per-coordinate
scales as explicit metadata) — these are checked by `lake build`, not by a
separate command.

## Check 5 — re-run the tool itself

```bash
lake build relcert
./.lake/build/bin/relcert benchmarks/suite_uniform/match_multi_rate/input.txt   # one
./.lake/build/bin/relcert benchmarks/suite_uniform/*/input.txt           # all
```

This is the *search* side: the tool re-derives covers and certificates from the
inputs. It is not needed to believe the theorems (the certificates the theorems
consume are emitted data, checked by `decideCovered` and the kernel), but it
confirms the emitted data in `Instances/Bench*.lean` is what the current tool
produces. 34 of 41 benchmarks certify. Six are DECLINED since the static (zero-duration)
reposition was removed on 2026-10-09 (`arm_chain_rung1`, `arm_chain_rung2`,
`arm_fidelity_low`, `robot_braking`, `rover3tier_M1`, `watertank`;
`docs/COVER-AUDIT.md`), and `shield_unreachable` is DECLINED (since
2026-10-08 it lowers — right-only variables are accepted — but its `Shield` guard is a
closed compound band the non-connection certificate does not prune, and `Shield` is an
admissible initial mode) and is therefore outside the certified suite. The pruned edge
of `match_multi_rate` is printed on every run (`[prune] match_multi_rate:
[DRIVE->STALL]`, stderr); `RELCERT_NO_PRUNE=1` makes that benchmark DECLINE
(`docs/PRUNING.md`).

---

## Per-benchmark inventory

34 benchmarks, 35 base modal theorems (44 rows with the mode-keyed and declared
theorems; the six benchmarks declined after the static-reposition removal of 2026-10-09
lost their rows). "std 3" = `[propext, Classical.choice, Quot.sound]`. Hypotheses are exactly the binders of the theorem: `dt` is the
window duration, `Verd…` are the Z3 verdict packs, `ESW` are existence
obligations.

| benchmark | instance file | theorem | hypotheses | axioms |
|---|---|---|---|---|
| `arm_chain_rung3` | `ArmChainRung3Modal.lean` | `arm_chain_rung3_modal` | `0 ≤ dt`; 2×`Verd3` | std 3 + `z3_unsat_sound` |
| `arm_chain_rung3` (declared invariant, `Hold` cut as mode region) | `ArmChainRung3Declared.lean` | `arm_chain_rung3_declared` | `0 ≤ dt` | **std 3 only** |
| `arm_fidelity_mid` | `ArmFidelityMidModal.lean` | `arm_fidelity_mid_modal` | `0 ≤ dt`; 2×`Verd3` | std 3 + `z3_unsat_sound` |
| `arm_fidelity_mid` (declared invariant, `Hold` cut as mode region) | `ArmFidelityMidDeclared.lean` | `arm_fidelity_mid_declared` | `0 ≤ dt` | **std 3 only** |
| `attitude_rate` | `AttitudeRateModal.lean` | `attitude_rate_modal` | `0 ≤ dt`; 2×`VerdW` | std 3 + `z3_unsat_sound` |
| `endurance_gain_M1` | `EnduranceGainM1Modal.lean` | `endurance_gain_M1_modal` | `0 ≤ dt`; 6×`VerdG` | std 3 + `z3_unsat_sound` |
| `endurance_orderlift_1to2` | `EnduranceOrderlift1to2Modal.lean` | `endurance_orderlift_1to2_modal` | `0 ≤ dt`; 1×`VerdO` | std 3 + `z3_unsat_sound` |
| `endurance_orderlift_2to3` | `EnduranceOrderlift2to3Modal.lean` | `endurance_orderlift_2to3_modal` | `0 ≤ dt`; 6×`VerdJ` | std 3 + `z3_unsat_sound` |
| `match_multi_rate` | `MatchMultiRateModal.lean` | `match_multi_rate_modal` | `0 ≤ dt`; 4×`VerdM` | std 3 + `z3_unsat_sound` |
| `match_multi_rate` (two-mode automaton with the pruned `STALL` sink; right never in `STALL`) | `MatchMultiRatePruned.lean` | `match_multi_rate_pruned` | `0 ≤ dt`; 4×`VerdM` | std 3 + `z3_unsat_sound` |
| `match_multi_rate` (the pruned edge `DRIVE → STALL`, Theorem 2) | `MatchMultiRatePruned.lean` | `match_multi_rate_nonconn` | `VerdNC` (source + barrier `unsat`) | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung1_2to3` | `RoverLadderRung1Modal.lean` | `rover_ladder_rung1_modal` | `0 ≤ dt`; 6×`VerdE` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung2_3to6` | `RoverLadderRung2Modal.lean` | `rover_ladder_rung2_3to6_modal` | `0 ≤ dt`; 6×`Verd36` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung2_6dof` | `RoverRung26dofModal.lean` | `rung2_6dof_modal` | `0 ≤ dt` | **std 3 only** |
| `refinement_ladder_rover_rung2b_6dof` | `RoverRung2b6dofModal.lean` | `rung2b_6dof_modal` | `0 ≤ dt` | **std 3 only** |
| `refinement_ladder_rover_rung2c_6dof` | `RoverRung2cModal.lean` | `rover_rung2c_modal` | `0 ≤ dt`; 3×`VerdR6` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung3_6to8` | `RoverLadderRung3Modal.lean` | `rover_ladder_rung3_6to8_modal` | `0 ≤ dt`; 6×`VerdR` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung4_8to12` | `RoverLadderRung4Modal.lean` | `rover_ladder_rung4_8to12_modal` | `0 ≤ dt`; 6×`VerdF` | std 3 + `z3_unsat_sound` |
| `rover3_M1` | `Rover3M1Modal.lean` | `rover3_M1_modal` | `0 ≤ dt` | **std 3 only** |
| `rover3_M1` (declared per-mode rows, composed) | `Rover3M1Handoff.lean` | `rover3_M1_modeKeyed` | `0 ≤ dt` | **std 3 only** |
| `rover3tier_rung12` | `Rover3tierRung12Modal.lean` | `rover3tier_rung12_modal_ACCEL` | `0 ≤ dt`; 2×`VerdQA` | std 3 + `z3_unsat_sound` |
| `rover3tier_rung12` | `Rover3tierRung12Modal.lean` | `rover3tier_rung12_modal_COAST` | `0 ≤ dt`; 2×`VerdQC` | std 3 + `z3_unsat_sound` |
| `rover3tier_rung12` (declared per-mode rows, composed; ACCEL row repaired 2026-10-08) | `Rover3tierRung12Handoff.lean` | `rover3tier_rung12_modeKeyed` | `0 ≤ dt`; 2×`VerdQA` + 2×`VerdQC` | std 3 + `z3_unsat_sound` |
| `rover_4d_box` | `Rover4dBoxModal.lean` | `rover_4d_box_modal` | `0 ≤ dt`; 1×`Verd3` | std 3 + `z3_unsat_sound` |
| `rover_attitude_cone_12dof` | `RoverAttitudeConeModal.lean` | `rover_attitude_cone_modal` | `0 ≤ dt`; 6×`VerdC` | std 3 + `z3_unsat_sound` |
| `rover_coupled` | `RoverCoupledModal.lean` | `rover_coupled_modal` | `0 ≤ dt` | **std 3 only** |
| `rover_coupled` (declared per-mode rows, composed) | `RoverCoupledHandoff.lean` | `rover_coupled_modeKeyed` | `0 ≤ dt` | **std 3 only** |
| `rover_dof_terrain_rung1` | `RoverDofTerrainRung1Modal.lean` | `rover_dof_terrain_rung1_modal` | `0 ≤ dt`; 6×`VerdE` | std 3 + `z3_unsat_sound` |
| `rover_dof_terrain_rung2` | `RoverDofTerrainRung2Modal.lean` | `rover_dof_terrain_rung2_modal` | `0 ≤ dt`; 6×`VerdT` | std 3 + `z3_unsat_sound` |
| `rover_dof_terrain_rung3` | `RoverDofTerrainRung3Modal.lean` | `rover_dof_terrain_rung3_modal` | `0 ≤ dt`; 6×`VerdW` | std 3 + `z3_unsat_sound` |
| `rover_dof_terrain_rung3_8d` | `RoverDofTerrainRung38dModal.lean` | `rover_dof_terrain_rung3_8d_modal` | `0 ≤ dt`; 6×`VerdU` | std 3 + `z3_unsat_sound` |
| `rover_drag` | `RoverDragModal.lean` | `rover_drag_modal` | `0 ≤ dt`; 1×`VerdRD` | std 3 + `z3_unsat_sound` |
| `rover_position` | `RoverPositionModal.lean` | `rover_position_modal` | `0 ≤ dt` | **std 3 only** |
| `rover_position` (declared per-mode rows, composed) | `RoverPositionHandoff.lean` | `rover_position_modeKeyed` | `0 ≤ dt` | **std 3 only** |
| `rover_terrain_M1` | `RoverTerrainM1Modal.lean` | `rover_terrain_M1_modal` | `0 ≤ dt`; 6×`VerdT` | std 3 + `z3_unsat_sound` |
| `rover_tier_r1` | `RoverTierR1Modal.lean` | `rover_tier_r1_modal` | `0 ≤ dt`; 1×`VerdX` | std 3 + `z3_unsat_sound` |
| `story1_attdist_rung_a_6to8` | `Story1AttdistRungAModal.lean` | `story1_attdist_rung_a_modal` | `0 ≤ dt`; 9×`VerdD` | std 3 + `z3_unsat_sound` |
| `story1_attdist_rung_a_6to8` (declared per-mode rows, composed) | `Story1AttdistRungAHandoff.lean` | `story1_attdist_rung_a_modeKeyed` | `0 ≤ dt`; 3×`VerdS` (STEEP, 3 components) + 6×`VerdD` | std 3 + `z3_unsat_sound` |
| `story1_attdist_rung_b_12dof` | `Story1AttdistRungBModal.lean` | `story1_attdist_rung_b_modal` | `0 ≤ dt`; 6×`VerdF` | std 3 + `z3_unsat_sound` |
| `story1_attdist_rung_b_12dof` (declared per-mode rows, composed) | `Story1AttdistRungBHandoff.lean` | `story1_attdist_rung_b_modeKeyed` | `0 ≤ dt`; 6×`VerdR r m` (`r ≤ m`; 4 components for STEEP, 3 otherwise) | std 3 + `z3_unsat_sound` |
| `story2_lateral_rung_a_8dof` | `Story2LateralAModal.lean` | `story2_lateral_rung_a_modal` | `0 ≤ dt`; 6×`VerdY` | std 3 + `z3_unsat_sound` |
| `story2_lateral_rung_b_12dof` | `Story2LateralBModal.lean` | `story2_lateral_rung_b_modal` | `0 ≤ dt`; 6×`VerdZ` | std 3 + `z3_unsat_sound` |
| `story3_rollover_base_12dof` | `Story3RolloverBaseModal.lean` | `story3_rollover_base_modal` | `0 ≤ dt`; 6×`VerdB` | std 3 + `z3_unsat_sound` |
| `story3_rollover_ladder_rung_a` | `Story3RolloverRungAModal.lean` | `story3_rollover_rung_a_modal` | `0 ≤ dt`; 6×`VerdA` | std 3 + `z3_unsat_sound` |
| `story3_rollover_ladder_rung_b` | `Story3RolloverRungBModal.lean` | `story3_rollover_rung_b_modal` | `0 ≤ dt`; 9×`VerdV` | std 3 + `z3_unsat_sound` |
| `story3_rollover_ladder_rung_b` (declared per-mode rows, composed) | `Story3RolloverRungBHandoff.lean` | `story3_rollover_rung_b_modeKeyed` | `0 ≤ dt`; 3×`VerdS` + 6×`VerdV` | std 3 + `z3_unsat_sound` |

Two rows deserve a note:

* **`rover3tier_rung12`** carries one theorem per left mode (`…_ACCEL`,
  `…_COAST`). Its modes declare *different-shaped* invariants with no
  implication either way, so a single-invariant statement would have to
  weaken one of them; the per-mode form states exactly what the tool certifies.
  With the rows as first declared the cross-mode handoff `ACCEL → COAST` was
  satisfiable (`docs/HANDOFF.md`, countermodel), so the mode-keyed invariant was
  not an invariant of that model. On 2026-10-08 the ACCEL row was re-stated —
  rows only, dynamics/guards/evolves untouched — as the velocity envelope plus
  COAST's own functional bound; both handoffs now hold under the
  domain-conditioned query and the composed theorem `rover3tier_rung12_modeKeyed`
  (`Rover3tierRung12Handoff.lean`) states the declared mode-keyed invariant.
* **The six other mode-dependent benchmarks** (`rover3_M1`, `rover_coupled`,
  `rover_position`, `story1_attdist_rung_a_6to8`, `story1_attdist_rung_b_12dof`,
  `story3_rollover_ladder_rung_b`) carry, beside their base theorem (which states
  a single weakest or common row for every window), a second theorem
  `…_modeKeyed` at the DECLARED per-left-mode invariant, composed across left
  switches by `Proofs/Encoding/ModeHandoff.lean` (`docs/PAPER-MAPPING.md` §2b).
  Their handoffs pass (5/5 each) and are discharged in-kernel, so the composed
  theorems add no verdict beyond the per-mode packs; `rover3_M1` is padded to
  `n = 3` for the left mode variable. Seven more `#print axioms` lines in
  `ModalBattery.lean`.
* **The two checked-cut benchmarks** (`arm_chain_rung3`, `arm_fidelity_mid`; three
  more — `arm_fidelity_high`, `plant_fan_high`, `plant_fan_mid` — were duplicates
  removed on 2026-10-08) carry, beside their base
  theorem (the `Hold` cut `θ_R ≥ 0.6` conjoined to the invariant at every right mode),
  a second theorem `…_declared` at the DECLARED row with the cut carried as `Hold`'s
  mode region only (`mvRegionR`, `⊤` at the approach modes) — the composition of the
  cut's entry (O1) and invariance (O2) obligations. Their responses are Z3-free
  right-only catch-ups (`Proofs/Encoding/CutComposition.lean`), so they add no
  verdict, no runner row and no pin; two more `#print axioms` lines in
  `ModalBattery.lean`: **46 theorems in all** since 2026-10-09 (with the two pruning-suite theorems of `match_multi_rate`; 52 before the static-reposition removal). The declared row with no region
  anywhere is false for these automata (`docs/CUT-COMPOSITION.md` §3).
* (`watertank`, the former flagship with proven existence and kernel identity pins, is
  DECLINED since the static-reposition removal of 2026-10-09; its files are in the git
  history, commit `3494c49`.)

---

## One-shot script

```bash
lake build \
  && lake build relcert relcert-test \
  && ./.lake/build/bin/relcert-test \
  && ./.lake/build/bin/relcert --run-verdicts \
  && lake build RelCertifier.Instances.ModalBattery 2>&1 | grep -A3 "depends on axioms"
```

Green build + `ALL PASS` + `ALL HYPOTHESES DISCHARGED` + an axiom listing with
nothing beyond the standard three and `z3_unsat_sound` = the suite is certified
end to end, modulo the parser and the Z3 leaf.
