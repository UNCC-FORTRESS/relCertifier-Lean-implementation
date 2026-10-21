# Cleanup scope: `main` = the paper's route; everything else to `archive/legacy-2026-10`

Scoped 2026-10-21 against `main` = `3d64743` (clean tree, 1001 tracked files). Read-only
analysis; the import closure was computed from the `import RelCertifier.*` lines of all 811
Lean modules (803 under `RelCertifier/`, `RelCertifier.lean`, 7 exe roots; 182,426 lines).

## 0. Headline

| | files | lines |
|---|---|---|
| all Lean modules | 811 | 182,426 |
| KEEP (paper route + tool + proof chain), after the prerequisite refactor of §2.1 | ~675 | ~88,800 |
| ARCHIVE | ~136 | ~93,600 |

Today the closure of the paper's roots is 787 files / 175,776 lines, because every
`WellFormed/<B>.lean` imports its standalone `Modal/<B>.lean` (or `Instances/<B>Guarded.lean`)
for the right model's definitions, and `VerdictsV2/RunV2` imports the legacy-pack runner.
Only 24 files (6,650 lines) are removable with no code change. The ~136-file archive needs
the three severing steps of §2.1 first.

Lake targets (`lakefile.toml`): lib `RelCertifier` (default target; root `RelCertifier.lean`,
132 direct imports, root closure 672 modules); exes `relcert` (`Main`), `relcert-test` (`Test`),
`relcert-slim` (`SlimMain`), `relcert-choice-verdicts` (`ChoiceVerdictsMain`),
`relcert-progress-verdicts` (`ProgressVerdictsMain`), `relcert-bridge-verdicts`
(`BridgeVerdictsMain`), `relcert-refute-verdicts` (`RefuteVerdictsMain`). The root imports
`InstancesV2.BatteryV2`, `InstancesV2.WellFormedBattery`, `InstancesV2.Refute` but NOT
`InstancesV2.Bridge` (built separately; `docs/CERTIFICATION-CHECK.md:69`).

Roots used for the closure: `Main`, `Test`, `BridgeVerdictsMain`, `RefuteVerdictsMain`,
`ProgressVerdictsMain` (run by `CERTIFICATION-CHECK.md:70`, cited by `PAPER-MAPPING.md:240,249`),
`ChoiceVerdictsMain` (run by `scripts/paper_numbers.sh:56`), `InstancesV2/Bridge.lean`,
`InstancesV2/Refute.lean`, `InstancesV2/WellFormedBattery.lean`,
`InstancesV2/Bridge/WatertankStrict.lean` + `scripts/strict_demo_verdicts.lean` (imports
`VerdictsV2.RunBridge`), `scripts/refute_dump.lean` (imports `RunV2`, `Emitted.RefuteData`,
`KeyAudit`, `Emitted.Window`). README recipe steps 1 to 5 and `paper_numbers.sh` run:
`relcert` (`--check-quick-v2`, `--wellformed`, `--emit-*`), `relcert-test`,
`relcert-bridge-verdicts`, `relcert-refute-verdicts`, `relcert-choice-verdicts`,
`scripts/suite_v2_matrix.py`. Nothing runs `relcert-slim`.

## 1. KEEP set (after §2.1)

Lean, by directory (files, lines):

| dir | files | lines | note |
|---|---|---|---|
| top: `Main`, `Test`, `BridgeVerdictsMain`, `RefuteVerdictsMain`, `ProgressVerdictsMain`, `RelCertifier.lean` | 6 | ~900 | root import list edited (§3) |
| `Trusted/` | 20 | 3,916 | all in closure |
| `Core/` | 3 | 546 | |
| `Checker/` + `Checker/Cover/` | 13 | 10,523 | incl. `Faithful.lean` (407; imported by `EvolStrengthening`) |
| `Proofs/Encoding/` | 58 | 20,215 | 67 minus the 9 of §2.5 |
| `Proofs/Encoding/Emitted/` | 19 | 6,650 | the bridge and refutation chain |
| `Proofs/Flow/` | 15 | 5,886 | incl. `MultisegLanding{,Bridge}` (imported by `UniformEvol`) |
| `Proofs/Soundness/` | 8 | 4,034 | incl. `GuardThreaded` (imported by `WellFormedChecker`, `CutChannel`), `CutLiftX` |
| `Proofs/Transfer/` | 2 | 2,712 | `FaithfulBridge` (imported by `CutLiftX`), `Rescale` |
| `InstancesV2/` aggregators: `BenchIR`, `BenchCovers`, `BenchProgress`, `BenchChoice`, `Cuts`, `Bridge`, `Refute`, `WellFormedBattery` | 8 | 940 | |
| `InstancesV2/{BenchIR,BenchCovers,BenchProgress,BenchChoice,Cuts}/` | 255 | 9,986 | 50 suite + `watertank_strict` each |
| `InstancesV2/Bridge/` | 53 | 3,487 | 50 suite + 2 exhibits + strict demo |
| `InstancesV2/Refute/` + `Refute/Data/` | 135 | 9,117 | 67 instances + `Table` + 67 data leaves |
| `InstancesV2/WellFormed/` | 31 | 4,316 | grows under §2.1 (right-model defs move in) |
| `Instances/WellFormed/` | 19 | 1,429 | same; consider renaming into `InstancesV2/WellFormed/` so `Instances/` disappears |
| `InstancesV2/Choice/` leaves (`BenchIR`, `BenchCovers`, `BenchProgress`, `BenchChoice`, `Cuts`) + `ConstMirror` | 11 | 535 | |
| `InstancesV2/Choice/General/{VehicleAccelCopy,VehicleHypercert,WatertankChoice}` | 3 | 837 | only `wellFormedR` needed (§2.1, P4) |
| `Verdicts/{Coverage,GenericPins,ModalPins,Combinators,Mirrors}` | 5 | 366 | imported by `VerdictsV2/{ModalX,ProgressPin,RunV2,RunRefute}` and `RunHandoff` |
| `Verdicts/RunHandoff` | 1 | 115 | the tool's handoff check (`Main`, `--handoff`, `--check-quick-v2`); imports only `Trusted/*` |
| `VerdictsV2/{RunV2,RunBridge,RunRefute,RunProgress,ModalX,ModalDynX,ModalXStrict,ProgressX,ProgressPin}` | 9 | 2,195 | `RunV2` trimmed (§2.1, P2) |

Non-Lean keep: `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `README.md`, `STATUS.md`;
`benchmarks/{suite_v2 (50), choice (2), strict_demo (1), refute_mutants (67), negative (1), README.md}`
(`negative/freedm_meter_leaky` is cited by README:360, STATUS:81, benchmarks/README:182, but no
script or recipe step runs it); `docs/refute/witnesses.jsonl` (input of `gen_refute.py`);
scripts: `paper_numbers.sh` (-> `suite_v2_matrix.py` -> `z3_timing_proxy.py`), `gen_v2_data.py`,
`gen_bridge.py`, `gen_strict_demo.py` + `strict_demo_verdicts.lean`, `gen_refute.py` ->
`refute_finder.py` -> `inv_smt.py`, `refute_dump.lean`, `refute_experiment.py`,
`domain_widening.py` (README:76), `trust_audit.py` (`Trusted/README.md:37`) = 14 of 16;
docs: `CERTIFICATION-CHECK`, `PAPER-MAPPING`, `WELLFORMED`, `HANDOFF`, `BRIDGE`,
`THEOREM3-GENERAL`, `CHOICE-SOUNDNESS`, `SUITE-REDESIGN`, `REFUTATION-RESULTS`,
`REFUTATION-SCOPE`, `CLOCKED-RIGHT-SCOPE` (11), `benchmarks/README.md`, `Trusted/README.md`.

## 2. ARCHIVE set

### 2.1 Prerequisites: what must move before the archive is safe

P1. **WellFormed self-containment (50 files).** Every `InstancesV2/WellFormed/<B>.lean` (31)
imports `InstancesV2/Modal/<B>.lean`; every `Instances/WellFormed/<B>.lean` (19) imports
`Instances/<B>Guarded.lean` (and 17 of them `Instances/GuardedPins.lean` for the single pin
`gp_1_0 : Run.parseRat "1.0" = some 1`). What they use from the instance is the right model, not
the Theorem 3 proof: `vs`, `mR`, `modeW`, `fR`, `domR`, `Gr`/`GrG`, `edgeW`/`edgeG`,
`edge_mem`, `Gr_modeAt_inv`, `sat_domR`, `sat_guardR*`, `fR*_eval`, `flowR_exists`, `nbF`,
`solΦ*`, `linkFields`, `cst*_eq`, `LR`, the `hp*` rational pins (7 to 45 names per file; the
`Modal/` files are 400 to 2,000 lines each and the right-model part is their first ~150 lines).
Move those definitions and lemmas into the `WellFormed/<B>.lean` file (or a
`RightModel/<B>.lean` beside it); replace `gp_1_0` by a local lemma. After P1 the bridge's
transport (`wellFormedR_lift` on `<ns>.<b>_wellFormedR`, `gen_bridge.py:60-67`) is unchanged
as long as the theorem names and namespaces stay. P1 is mechanical but is the bulk of the work.

P2. **`VerdictsV2/RunV2.lean` (673 lines) loses its legacy phase.** It imports
`Verdicts/RunModal` (-> `Instances/ModalSpecs`, `Instances/BenchIR`: the 19 carried-over
literals) for `sameModalTable` ("copied benchmarks (legacy packs) 385/385", lines 629-666).
Delete that phase and its declared count; `Main --check-quick-v2` and `runAllVerdictsV2` keep
the certify / handoff / strict-wellformed phases. `RunBridge` uses only `discharged` /
`dischargedCount` from `RunV2`; `RunRefute`, `RunProgress` import `RunV2` the same way.

P3. **`InstancesV2/Choice/Verdicts.lean` + `ChoiceVerdictsMain` (`relcert-choice-verdicts`).**
They discharge the three exhibits' *standalone* packs and import `Choice/Modal/*` and
`Modal/Watertank`. The exhibits' bridge groups are already inside `relcert-bridge-verdicts`'
4457. Archive both, drop the exe from `lakefile.toml` and step 3 of `paper_numbers.sh:55-57`
(check first whether `numbers.tex`, lines 62 ff., reads `choice_verdicts.txt`).

P4. **`Choice/General/{VehicleAccelCopy,VehicleHypercert,WatertankChoice}.lean`** import
`Choice/Modal/<X>.lean` (and `ConstMirror`, `WellFormedR`) and still carry `AG_*`, `hop_cover`,
`Gr_sys/dom/weight`, `GrP_*` besides `wellFormedR`. Reduce each to the right model +
`theorem wellFormedR : WellFormedR G guardR 1` (the shape `gen_bridge.py:78-86` looks up) and
either leave them in place or move them to `InstancesV2/WellFormed/` (then update
`gen_bridge.py` lines 24, 78-86 and the `WellFormedBattery` import of `VehicleHypercert`).

### 2.2 Standalone Theorem 3 route (stale legacy route; the paper's route is the bridge)

| group | files | lines | kept-set importers after P1-P4 |
|---|---|---|---|
| `InstancesV2/Modal/*` | 31 | 34,326 | none (today: 31 `WellFormed/*`, `Choice/Verdicts`, `PinsV2`, `BatteryV2`) |
| `Instances/*` except `WellFormed/`: 42 `*Modal/*Guarded/*Handoff/*Pruned`, `GuardedPins`, `ModalSpecs`, `BenchIR.lean`, `LeftAutLegacy`, `AxiomCheck` | 48 | 46,524 | none (today: 19 `Instances/WellFormed/*`, `RunModal`, `ModalPinTable`, root) |
| `Instances/BenchIR/*` (the 19 legacy literals) + `Instances/EvolStrengthenings/match_multi_rate` | 21 | 2,223 | none (today: `Instances/BenchIR.lean`, `RunModal`) |
| `InstancesV2/Choice/Modal/*`, `Choice/PointwiseCouple` | 4 | 2,753 | none (today: `Choice/General/*`, `Choice/Verdicts`) |
| `InstancesV2/Choice/General/{ChargerFastSetpoints,Watertank}` (not imported by anything) | 2 | 612 | none |
| `InstancesV2/{BatteryV2,SameIR,CoverReplay,LeftAutV2}` | 4 | 1,133 | none (root only) |
| `InstancesV2/Choice/Verdicts` + `ChoiceVerdictsMain` (P3) | 2 | ~170 | none |

### 2.3 Pins and runners of the standalone route

| group | files | lines | why safe |
|---|---|---|---|
| `VerdictsV2/{PinsV2,LamPinV2,NonConnPinV2,CoveragePinsV2}` | 4 | 1,011 | imported only by `BatteryV2` (and `NonConnPinV2` by the root); they pin `Modal/*` `Verd`s to `RunV2` tables |
| `Verdicts/{RunModal,ModalVerd,ModalPinTable,ModalTablePins,ModalCodePins}` | 5 | 1,371 | the 19 legacy packs; imported only by `RunV2` (P2), `CoveragePinsV2`, root |

No `decide`/`rfl` in the keep set reads an archived module: the bridge instances decide over
`BenchIR/Cuts/BenchCovers/BenchProgress/BenchChoice` leaves; the refutations over
`Refute/Data` + `Refute/Table`; `RunBridge`/`RunRefute` import those leaves, not `Modal/*`.
Reverse direction checked: `Verdicts/*` and `VerdictsV2/*` import no archived module except
through the five files above and `RunV2`'s `RunModal` import (P2).

### 2.4 Historical generic development used only by the standalone instances

| group | files | lines | importers |
|---|---|---|---|
| `Proofs/Encoding/{ContractRun,LadderReplay,LadderSync,ModeRegion,ReplayBridge,ReplayComps,ReplayModeKeyed,ReplayOne,SinkExtension}` | 9 | 1,361 | `Instances/*`, `InstancesV2/Modal/*`, root only |
| `Proofs/Encoding/StrictModal` | 1 | 250 | root only |
| `Proofs/Flow/{AffineFaces,AffineFaces2}` | 2 | 643 | instances, root only |
| `Proofs/Transfer/{FaithfulBridgeGuards,FaithfulBridgePad,RealEndToEnd}` | 3 | 1,243 | root only |

Historical generic development that STAYS because the kept proof chain imports it (renaming or
pruning it is proof surgery, out of scope): `Checker/Faithful` (<- `EvolStrengthening`),
`Proofs/Transfer/{FaithfulBridge,Rescale}` (<- `CutLiftX`), `Proofs/Soundness/GuardThreaded`
(<- `WellFormedChecker`, `CutChannel`), `Proofs/Encoding/ClockedTop` (<- `FvDischarge`),
`Proofs/Flow/{MultisegLanding,MultisegLandingBridge}` (<- `UniformEvol`).

### 2.5 Non-Lean

* `scripts/gen_multif_instance.py` (1,022 lines; generated the legacy `Instances/*Modal`),
  `scripts/gen_multif_lambda_k.py` (284; referenced only by README:363): archive.
  `scripts/black_mutation.py` is referenced by `refute_finder.py` and `REFUTATION-SCOPE.md`
  but does not exist (dangling; fix the references). `scripts/__pycache__/` is untracked.
* `docs/history/*` (25 files, 6,845 lines): its own README says none describes the current
  artifact. Five are linked from current docs (`PAPER-MAPPING-2026-10-10`, `README`,
  `RESET-MAPS-SCOPE`, `ROTATION-SCOPE` x2, `VERDICT-EVIDENCE-AUDIT`). Archive the directory,
  replace the links by "see branch `archive/legacy-2026-10`".
* Current docs about the standalone route: `docs/VERDICTS.md` (100 lines, the `BatteryV2`
  packs), `docs/REPLAY.md` (227, per-benchmark replays of the standalone proofs),
  `docs/GUARDED-SWITCHING.md` (472, the standalone statement's history; holds the
  per-benchmark findings `PAPER-MAPPING.md:131` points at). Archive `VERDICTS.md` and
  `REPLAY.md` (or rewrite `VERDICTS.md` around the bridge/refute/progress runners); decision
  needed on `GUARDED-SWITCHING.md`.
* `docs/refute/{results.json,relcert.json,runner.log,experiment.log}` (~250 KB of outputs of
  `refute_experiment.py`): archive; keep `witnesses.jsonl`.
* `SlimMain.lean` / `relcert-slim`: closure entirely inside the keep set, run by no recipe;
  archive unless wanted as the "no instance imports" build check.

## 3. Mechanics

1. `git branch archive/legacy-2026-10 3d64743 && git push -u origin archive/legacy-2026-10`;
   on it add `ARCHIVE-README.md` (what was archived and why, that `lake build` of the
   snapshot is the full pre-cleanup artifact, the recipe of README step 1-5 as of 3d64743).
2. On a branch `cleanup-legacy` from main, in this order, each a commit that builds:
   a. P1 (50 WellFormed files self-contained), P4 (three General files reduced), P2 (`RunV2`
      legacy phase removed), P3 (choice verdicts removed).
   b. `git rm` of §2.2 to §2.5 (Lean: ~136 files).
   c. `RelCertifier.lean`: drop the archived imports (direct: `Instances.AxiomCheck`,
      `InstancesV2.BatteryV2`, `Proofs.Encoding.StrictModal`, `Proofs.Flow.AffineFaces2`,
      `Proofs.Transfer.{FaithfulBridgeGuards,FaithfulBridgePad,RealEndToEnd}`,
      `Verdicts.ModalCodePins`, `VerdictsV2.NonConnPinV2`, plus the §2.4 modules it names);
      add `InstancesV2.Bridge` so `lake build` covers the paper route (or keep the explicit
      `lake build RelCertifier.InstancesV2.Bridge` in the recipe). `lakefile.toml`: remove
      `relcert-choice-verdicts` (and `relcert-slim` if archived).
   d. `gen_bridge.py` (WF lookup, if P4 moves files), `paper_numbers.sh` (step 3), `trust_audit.py`.
   e. Prose: README lines 20, 57, 76-77, 123, 164-165, 178-194 ("Theorem families", all
      counts read off `BatteryV2`), 212, 236-244 (expected output: drop the 71 `BatteryV2`
      axiom lines and the "copied benchmarks (legacy packs) 385/385" phase), 251-258 (heavy
      files), 299, 337-363 (layout), 470-479 ("The 19 carried-over theorems" becomes "19
      carried-over Assumption 1 proofs"); STATUS.md lines 5-7, 18-22; `PAPER-MAPPING.md` lines
      129-131 (the standalone row of the two-routes table), 222, 234 (`--run-verdicts-v2`),
      300, 352 (the "46 standalone instances, 1410 hypotheses" row); `CERTIFICATION-CHECK.md`
      lines 20-29, 50-52, 81-96, 107-120, 140, 173, 220-246 (per-benchmark inventory);
      `WELLFORMED.md` wherever it cites `Modal/` imports.
   f. Cold check: `rm -rf .lake/build; lake build; lake build relcert relcert-test
      relcert-bridge-verdicts relcert-refute-verdicts relcert-progress-verdicts;
      lake build RelCertifier.InstancesV2.Bridge`; then README steps 2b-5 and
      `scripts/paper_numbers.sh OUT`. Expected: `[suite_v2] 50 certified, 0 declined`,
      `[wellformed] STRICT: 174/174`, `relcert-test` `ALL PASS`, `relcert-bridge-verdicts`
      `4457/4457`, `refute: 188/188`, `relcert-progress-verdicts` 261/261,
      `WellFormedBattery` 50/50 right models with the three standard axioms only (76 axiom
      lines today; re-count after P1), `gen_v2_data.py` + `gen_bridge.py` + `gen_refute.py`
      re-emission byte-identical (`git diff` empty), `trust_audit.py` clean, and
      `grep -rn 'InstancesV2.Modal\|Instances\.\|BatteryV2\|run-verdicts-v2' README.md STATUS.md docs scripts` empty.
3. Merge to main; the heavy-files paragraph of the README mostly disappears (the archived
   instances dominated the build: `CERTIFICATION-CHECK.md:81-96`).

## 4. Risks and open questions

1. **P1 size and fidelity.** 50 files, 7 to 45 names each, taken from 400 to 2,000-line
   instances. The `wellFormedR` theorems are Z3-free, so no verdict count moves, but the
   `WellFormedBattery` axiom-line count (76) and `WELLFORMED.md`'s per-benchmark table may.
2. **`--check-quick-v2` phases.** After P2, `RunV2` still re-sends the suite's modal
   (625), non-connection (88), pruned-edge (44) and reposition (81) queries from the
   `ModalX`/`ModalDynX`/`ProgressX` tables, which no kept theorem assumes once `BatteryV2` is
   gone (the bridge's 4457 groups cover the same facts). Keep them as a tool self-check, or
   drop them and then also archive `ModalX`, `ModalDynX`, `ModalXStrict`, `ProgressX`,
   `ProgressPin` and `Verdicts/{GenericPins,ModalPins,Combinators,Mirrors}` (not verified
   whether `RunBridge`/`Emitted/StrictRun` rebuild queries through `ModalX`; check before).
3. **`Instances/AxiomCheck.lean`** (52 lines, "reproducible axiom audit of the generic
   theorems", `CERTIFICATION-CHECK.md:120`): not read; may name archived theorems. Prune or
   archive after reading.
4. **`paper_numbers.sh` step 3 / `numbers.tex`**: whether any cited number comes from
   `relcert-choice-verdicts` (P3). Not checked.
5. **`docs/GUARDED-SWITCHING.md`**: keep (findings) or archive (standalone history)?
6. **`Instances/WellFormed/` directory name**: after P1 the 19 files are the only content of
   `Instances/`; rename into `InstancesV2/WellFormed/` (touches `gen_bridge.py` `WF_DIRS`,
   `WellFormedBattery`, 19 bridge instances' imports) or leave.
7. **`benchmarks/negative`** is cited as the expected DECLINE exhibit but no recipe step runs
   it; add one line to `paper_numbers.sh` or README step 3, or archive it.
8. **Branch state**: 23 local branches (`cleanup`, `mutation`, `refutation`, ... ) exist; the
   archive branch should be cut from `main` only, not from `cleanup`.
