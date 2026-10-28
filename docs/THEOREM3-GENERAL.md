# Theorem 3, generically, with the existential mode choice (branch `theorem3-general`)

Status: the general theorem is proved (`Proofs/Encoding/Theorem3General.lean`,
`theorem3_of_coverX`, axioms `propext`, `Classical.choice`, `Quot.sound`); instances for
`vehicle_hypercert`, `vehicle_accel_copy`, `watertank_choice` and the suite's `watertank` went
through it as hand-written general instances (`InstancesV2/Choice/General/`), each with the
standard three axioms plus `z3_unsat_sound`; their Theorem-3 parts were retired on 2026-10-21
(git 61d7389) and only their Assumption 1 proofs remain, every benchmark and exhibit now going
through the generated bridge instances of §5. Before this branch the paper's Theorem 3 was mechanized per
benchmark: generic lemmas (the outer loop rule, the replay engine, guarded switching) and a
per-benchmark construction of the response. Now the construction is one theorem whose
hypotheses are Theorem 3's conditions.

## 1. The statement

`theorem3_of_coverX` concludes `rvalid (theorem3Form L R ψ)`: the encoded ∀∃ invariance over
the guard-gated left windows `L` (one per left mode, each of duration at most `dt`) and the
guarded right automaton `R`, with the loop invariant `ψ` = the declared row ∧ the evolve
envelope ∧ the right mode's region (its guard and its kept atoms: the paper's operating region
`op_R`). Its hypotheses, grouped as the paper's conditions 1 and 2 with the covers' certificates
as a third group (the paper's condition 3, the handoff, enters where `theorem3_modeKeyed`
composes the rows):

1. **Assumption 1** (`hwf : WellFormedR G guard ε_R`): from every state of a mode's guard the
   run of one right interval exists, and every run of duration at most `ε_R` ends in some
   declared successor's guard.
2. **The covers** (`hcov`): for every left mode `l` and every admissible start `q`
   (`AdmissibleStart`: some joint state satisfies the left guard, the row, the envelope and the
   right region), `CoveredX G (ch l) (q, B_l, preJ)`; and `dt ≤ B_l · δ_l`.
3. **The certificates** (`CoverHyps`, per left mode): the flow certificate of every certified
   pairing at its stretch (`hbox`, the paper's Definition 5 and Lemma 2); the reposition-progress
   premise of every reposition node (`hrepoProg : RepoProgress …`, into which the reposition flow box `hboxD` and the right-only
   non-connection fact `hpruneD` are folded when `repoProgress_*` discharges it; they are not `CoverHyps` fields);
   the non-connection certificates of the pruned edges (`hprune`, the paper's Definition 6); the
   coverage certificates of the chosen sets (`hcovJ`, `hcovR`, `hcovS`, with the regions
   implied by the anchor); the entry condition (`hhand`); and the reposition-progress premise
   (`hrepoProg`, §3).

The time model is the tool's: a common segment span `δ = ε_R / λ_max` with `λ_q δ ≤ ε_R` per
pairing (`hspan`), unit weights, budget `B = ⌈ε_L / δ⌉`.

## 2. The proof

`CoveredX` (`Checker/CoverX.lean`) is the paper's Definition 8 with its committed subsets, cases 3 and 4 of
`docs/CHOICE-SOUNDNESS.md`; `decideCoveredX` is the checker and `decideCoveredX_sound` its
soundness. The cover flags (which pairings are certified) and the chosen sets are per window
(`ChoiceData`), so one right automaton serves every window.

`coverX_piece` (`Proofs/Encoding/CoverResp.lean`) is the induction (the paper's Theorem 1, Soundness of
Witness Strategies, whose steps are Lemmas 3 and 4): a covered configuration
answers one clocked left piece from left time `a` if `r − a ≤ B δ`. Base and step run the
joint segment (Assumption 1 gives the right run, `joint_stretch` carries the anchor, Assumption
1 again gives an enabled successor, the non-connection certificates of Definition 6 exclude
pruned ones); chosen successors come
from the coverage certificate at the segment's end; right-only steps reach an exit by
reposition progress; chosen exits and hops switch at duration zero. `coverX_gresp` lifts the
piece response to the gated window; `Hmulti_of_coverX` and `theorem3_of_coverX` assemble the
windows into the loop through `Hmulti_regionG`, `hstep_assembled_GR` and
`theorem3_faithful_multiR_LR`, exactly as every per-benchmark instance did.

## 3. Reposition progress: the certificate the paper's proof sketch was missing

An earlier proof sketch of Theorem 3 (before the paper stated the right-only obligation as
Lemma 4 and the certificate as Definition 7) said
Assumption 1 "continues every segment along a retained edge". For a joint segment that is right. For a **right-only** segment it is not: Assumption 1
may enable only the self-loop, the rule requires a non-self exit, and the tool never checked
that an exit is reached. The 12 benchmarks whose covers use right-only steps rest on exactly
that (with the all-successors right-only rule disabled, `RELCERT_NO_REPO=1`, they decline:
34/46). Their standalone Lean proofs had discharged it from explicit solutions (`HExit`).

The fix is a **progress certificate** (the paper's reposition certificate, Definition 7, consumed by Lemma 4 Proving Right-Only Segments; `Trusted/ProgressEmit.lean`; the tool's default, `RELCERT_NO_PROGRESS=1` disables it),
checked by the tool per reposition node like every other certificate: a stage
`(x, θ, r)` says "while `x < θ` (on the node's region, the facts the reposition flow keeps)
the field of `x` is at least `r > 0`"; an optional helper stage `(y, y₀, r₁)` first (its
crossed fact `y ≥ y₀` is kept, and the main rate holds under it); and the landing: on the
crossing line `x = θ` and at a start already crossed (`guard(q) ∧ x ≥ θ`) some exit's guard
holds. With the certificate required the suite certifies 46/46 (261 certificates, 110 with a
helper stage; the four nodes without one are never used). The right-only rule and Assumption
1 are unchanged; the right-only kind is now *certified*: preservation (certificate 3) plus
progress.

The emitted certificates (`InstancesV2/BenchProgress`, 261 over the suite) are rebuilt into
their queries by `VerdictsV2/ProgressX.lean` and discharged by `relcert-progress-verdicts`
(261/261 unsat); `VerdictsV2/ProgressPin.lean` reads a certificate's verdict as the host-level
facts, and `charger_fast_setpoints` went through the general theorem with its `BULK` reposition
node discharged that way (it moved to `benchmarks/reserve/` on 2026-10-27; its instance is in git
history).

`Proofs/Encoding/Progress.lean` proves the certificate sound: `repoProgress_one`,
`repoProgress_one_down` (a single downward stage, the mirror) and `repoProgress_two` give `RepoProgress` (the general theorem's premise: from a reposition start,
cycles of the node until an exit is enabled, the anchor kept) from the certificate's facts,
Assumption 1 (each cycle's run, and an enabled successor at its end), the reposition flow
certificate (the anchor is kept) and the right-only non-connection certificate (a pruned exit
is never enabled). Each cycle without crossing advances the stage coordinate by `r ε_R`, so the
cycles are bounded; a crossing lands by the intermediate value theorem. Axioms: the standard
three.

## 4. Instances

Historical: the Theorem-3 parts of these hand-written general instances were retired on
2026-10-21 (git 61d7389); their Assumption 1 proofs remain and are transported and lifted into
the generated bridge instances (§5, `docs/WELLFORMED.md` §6).

| benchmark | windows | cover | discharged here |
|---|---|---|---|
| `vehicle_hypercert` | 5, `dt ≤ 1` | hop into the left's mode, then base | hop certificate by arithmetic; Assumption 1 (`odeSol_constRight`); 5 packs |
| `vehicle_accel_copy` | 3, `dt ≤ 1` | the same | hop certificate (`guardR_of_guardL`); 3 packs |
| `watertank_choice` | 3, `dt ≤ 1` | `Low` at the per-pairing stretches (δ = 2/7, B = 4), all-successors with `Low → PumpOff` pruned; `Mid` from `MidEco` by a hop into `MidBoost`; decided by `decideCoveredX` in the kernel | Definition 6 for the pruned edge by arithmetic; hop certificate; Assumption 1 with the economy set point; 7 packs |
| `watertank` (suite) | 3, `dt ≤ 1` | the tool's emitted cover: `Low` and `Mid` at stretch 2 (δ = 1/2, B = 2), all-successors with `Low → PumpOff` pruned; no choice; decided in the kernel | Definition 6 by arithmetic; Assumption 1 transported from the suite's lemma; the suite's 7 packs plus `Low/High` at 2 (see below) |

| `charger_fast_setpoints` (suite until 2026-10-27, now in `benchmarks/reserve/`) | 3, `dt ≤ 2` | the tool's emitted cover: `BULK` a reposition node in the `BULK` and `ABSORB` windows (the right charges at the bulk rate until `ABSORB`'s guard opens), `BULK → FAULT` pruned; decided in the kernel | **reposition progress from the emitted progress certificate** (`progressVerd_one`, the queries the progress verdict runner discharges) with Assumption 1, the reposition packs (`VerdD`) and Definition 6 for the pruned edge; the suite's 6 joint packs |

**A finding on the suite's replay.** The tool's emitted `Low` cover of `watertank` marks `High`
joint-certified (a `MidEco` start may continue in `High` after one segment), so the tool issued
and discharged the `Low/High` flow query at stretch 2. The suite's verdict runner (`packsV2`)
never re-checked that pack: the standalone Lean proof's response stays in the start mode for
the whole window, so it does not need it. The general instance replays the tool's cover, needs
the pack, and the choice verdict runner now carries it (`wt 0 3 2 1`, unsat). The lesson: a
hand-built response can be simpler than the tool's cover, and then the pins cover the proof,
not the tool's decision. Replaying emitted covers through `decideCoveredX` (D5) closes this
for every benchmark.

The per-benchmark standalone proofs (`InstancesV2/Choice/Modal/`, `InstancesV2/Modal/`)
remained until 2026-10-22 (archived on branch `archive/legacy-2026-10`); the general instances were theorems (`*_general`) with the same conclusion shape
(their region beyond the declared modes was `⊤` instead of `⊥`, immaterial under `mvRegionR`)
until their retirement on 2026-10-21.

## 5. The generic bridge (2026-10-14/15)

The per-benchmark instances of §4 are superseded for the suite by the generic bridge
(`docs/BRIDGE.md`, `Proofs/Encoding/Emitted/`): one layer instantiates the general theorem
from a benchmark's emitted records (IR, cut certificate, cover, progress certificates), the
structural facts decided in the kernel, every verdict read from one Z3 run
(`relcert-bridge-verdicts`, 4874 groups over the 50 suite benchmarks and the 2 choice
exhibits, all discharged). Mode-dependent rows
are assembled through `theorem3_modeKeyed` (`Emitted/Keyed.lean`); the two-stage progress pin
is `progressVerd_two`. Generated instances: `InstancesV2/Bridge/`, all 50 suite benchmarks
(37 window form, 13 mode-keyed) and the two choice exhibits, every one with the
paper's unconditional Assumption 1 (the detumble models carry their momentum band in the
right evolve domain).

The tool emits its choice covers (`RELCERT_CHOICE_OUT`, `Trusted/ChoiceEmit.lean`) and the
bridge replays them (`Emitted/Choice.lean`): `vehicle_accel_copy` and `watertank_choice` are
generated bridge instances, and so is `vehicle_hypercert`. `repoProgress_one_down`, the mirror of
`repoProgress_one` for a single downward stage, was used by the velocity-only `vehicle_hypercert`
(its reposition node's stage crossed its threshold downward); since that benchmark's redesign with
the position coordinate (2026-10-27) no suite record uses the downward form, and its Assumption 1
lemma is its own `InstancesV2/WellFormed/VehicleHypercert.lean` (before, the hand-written general
instance of §4, whose Theorem-3 part was retired on 2026-10-21, git 61d7389).
