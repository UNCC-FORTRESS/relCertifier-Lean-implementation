# Status (2026-10-15, branch `theorem3-general`)

**The artifact.** `benchmarks/suite_v2` (50 benchmarks: 46 designed for the paper and four from the literature, 2026-10-15), the tool `relcert`, the generic
soundness development (`RelCertifier/Core`, `Checker`, `Proofs`, `Trusted`) and the suite_v2
battery (`RelCertifier/InstancesV2/BatteryV2.lean`). The legacy suite `suite_uniform` and its
batteries were retired on 2026-10-10; the 19 theorems the battery carries over from it are
kept with exactly what they need (`README.md`, "The 19 carried-over theorems").

**Proved, all 50, one statement.** Theorem 3 with the paper's LEFT program (the guard-gated
left automaton `leftAutomatonBody A u_L`: each left window entered inside its lowered guard,
the declared successors and `u_L` read from the file) against the GUARDED right automaton
(every edge tests the lowered guard of the mode it enters), with the loop invariant carrying
the rows keyed by `u_L`, both envelopes, `u_L ∈ modes` and `regionG guard cuts q = guard q ∧
cuts q` of the right's current mode (`docs/GUARDED-SWITCHING.md` §3.1, §3.3). 44 benchmarks
for every window length, `refinement_ladder_rover_rung2c_6dof` for every window up to its
control interval (`dt ≤ ε_L = 1`); every switch on both sides kernel-checked legal. 12
mode-keyed, 33 mode-independent (carried to the left automaton by the generic bridge
`theorem3_leftAut_of_choice`, proved once); **every one of the 46 standalone proofs replays the cover the
tool emits** (`docs/REPLAY.md`: joint segments at `jointOK` nodes at the cover's stretch, each
preserved by its pack; right-only repositions at `dynPre` nodes, each preserved by its
reposition pack; legal switches along retained edges; inadmissible starts contradictory), so
none is Z3-free (was 16; 234 joint + 41 reposition pack hypotheses); the 6 satellites' standalone
statements carry the conserved-momentum band in their region (since 2026-10-15 also in the right
evolve domain). No theorem carries a nonblocking (Assumption 1) hypothesis; no new
axiom; the declared rows unchanged. Plus the Theorem 2 instance of `match_multi_rate`'s
pruned edge. Axioms of every battery theorem ⊆ `{propext, Classical.choice, Quot.sound,
z3_unsat_sound}`; no `sorry`.

**Repaired.** `platoon3_linkloss`, `platoon3_profiles`: the guarded Theorem 3 was refuted in the
kernel on the old model (commit `1a3507f`) because its nominal controller BLOCKED after a full
cycle (engagement-band stay guards, no catch-all mode: a violation of Assumption 1 the
certificate cannot detect). The guards are now the operating range (floor 20, radar range,
rated closing rate, projected gap `21 ≤ g + 2r ≤ 59`; `docs/SUITE-REDESIGN.md` §20); both are
CERTIFIED and proved. The earlier "refuted by argument" entries (`rung2_3to6`, the story2
pair) refuted only a left program without guard tests; they are proved
(`docs/GUARDED-SWITCHING.md` §4.5).

**Assumption 1, verified per benchmark** (`docs/WELLFORMED.md`). The paper's Assumption 1
(the right model is nonblocking and complete for its declared successors over one control
interval `ε_r`) is stated once as `WellFormedR` (`Proofs/Encoding/WellFormedR.lean`) and
**proved for all 50 right models**, Z3-free (`InstancesV2/WellFormedBattery.lean`, declared
counts `(44, 0, 6)`: every mode outside the detumble family, refuted, the detumble family;
the three standard axioms only): **literally for all 50** (the six satellites since 2026-10-15,
when the conserved momentum band `|h_i + J_i w_i| ≤ 2`, kept by every mode's flow, entered
their right evolve domains; without it `DETUMBLE` had no full-interval run). Nine models violated it until 2026-10-10
(refuted in the kernel with exhibited blocking states, declared counts `(30, 9, 6)`) and were
repaired (`docs/SUITE-REDESIGN.md` §21): `platoon_delay_{linkloss,profiles}` (the AEB sink
re-engages FOLLOW at 20 m), `quad_light_{airframe_20,profiles}` (the limiter hands back to the
climb controller, whose operating range now reaches the limiter threshold),
`platoon3_{linkloss,profiles}` (latched speed-matching AEB sinks with an invariant guard; the
tool's pruning now accepts a compound sink guard on its strict leading conjunct),
`arm_plateau_{crit,profiles,slow}` (the sampled planner's successor sets name every band one
interval can reach). Each re-certifies, every counter-run and prune unchanged; matrix change
M3 12 → 14 (`arm_plateau_crit`, `_slow` now branch); widening unchanged except
`quad_light_profiles` (the deployed's rated 3.5 m/s climb cap is now load-bearing). The tool's
sufficient check (`relcert --wellformed`) reports 174 right modes: 94 ok (invariant), 80 ok
(exit), 0 UNKNOWN (was 77 / 53 / 16), and is STRICT in the recipe: `--check-quick-v2`
certifies in the strict mode and fails on any `UNKNOWN` against the declared 174 modes.

**The generic bridge (branch `theorem3-general`, 2026-10-14/15; `docs/BRIDGE.md`).** The
general Theorem 3 (`theorem3_of_coverX`, `docs/THEOREM3-GENERAL.md`) is Definition 4 with the
existential mode choice (chosen successor sets, entry hops; `docs/CHOICE-SOUNDNESS.md`) and the
reposition-progress premise discharged by the tool's progress certificates (emitted by default;
`RELCERT_NO_PROGRESS=1` disables them). One generic layer (`Proofs/Encoding/Emitted/`) turns a
benchmark's emitted records (IR, cut certificate, cover, progress and choice records) into
Theorem 3 of that benchmark: the structural facts decided in the kernel (`decide +kernel`),
Assumption 1 transported from the benchmark's `WellFormedR` lemma, every verdict read from one
Z3 run (`relcert-bridge-verdicts`: 4457 groups over the 50 suite benchmarks and the 2 choice
exhibits, all discharged). Generated instances (`InstancesV2/Bridge/`, `scripts/gen_bridge.py`):
all 50 suite benchmarks (38 window form, 12 mode-keyed) and the choice exhibits
`vehicle_accel_copy`, `watertank_choice` (their chosen sets replayed); `vehicle_hypercert`'s
downward progress stage goes through the mirror lemma `repoProgress_one_down`. Axioms
of every `*_bridge` theorem: the three standard ones and `z3_unsat_sound`.

**Literature benchmarks (2026-10-15).** Four models from cited papers joined the suite, each
header stating the source and what the sampled form changed: `drl_car_stop` and
`drl_lane_control` (differential refinement logic: a time-triggered controller refines the
permissive sampled one, identity invariant, the leader's acceleration a finite choice) and
`vehicle_hypercert` (HyperCertificates §9.2, formerly a choice exhibit) and `freedm_meter` (the
FREEDM transformer of hybrid-dynamic information flow: the battery level is not deducible from
the grid meter under the free-source controller `batS`; the leaky `batI` is the negative exhibit
`benchmarks/negative/freedm_meter_leaky`, DECLINED as expected). All four need the
existential mode choice (the right commits to the left's mode), which is now the tool's default
(`RELCERT_NO_CHOICE=1` disables it); the 46 original covers are byte-identical either way. The
Assumption 1 lemmas of the three new models are proved directly over the bridge's automaton (`_wellFormedR_direct`,
`trajRs_sol` explicit runs); `vehicle_hypercert`'s comes from its hand-written general instance.

**Discharged.** Every Z3 hypothesis is re-sent by `relcert --run-verdicts-v2` against
declared counts (modal 625, handoff 401, non-connection 88 over 44 pruned edges, legacy
packs 385, reposition 81), each query pinned in the kernel to the hypothesis it discharges.
On branch `replay` every proof was made to replay the emitted cover (`docs/REPLAY.md`): the 46
statements take 234 joint packs (every row of `RunV2.packsV2`, was 104 rows) and 41 reposition
packs (the new table `RunV2.dynPacksV2` and runner phase); 132 pack hypotheses before. No
headline statement takes a legacy pack any more; the legacy phase re-sends the packs of the
choice-form and relaxation theorems that stay in the tree.

**Assumed.** The trust base: parser, lowering (including the right guards placed on the
edges), SMT printer, Z3's `unsat`, the Lean kernel. Guard-gated switching is no longer
assumed (both sides) (`README.md`, "Trust base").

**Last verified run.** 2026-10-15, branch `theorem3-general` (commit `12a0c6b`), Apple M2 Max,
Z3 4.15.1. Full `lake build` exit 0, no `sorry`; `relcert-test` `ALL PASS`; `relcert
--run-verdicts-v2` all phases discharged (reposition 81/81); `relcert-progress-verdicts` 261/261;
`relcert-choice-verdicts` 32/32; `relcert-bridge-verdicts` 3512/3512; `scripts/paper_numbers.sh`
re-run on the clean commit (46 CERTIFIED, 18 sync, 19 without prune declarations, 3 choice
exhibits, 32 choice verdicts unsat, covers identical with choice on and off). Previous run:
2026-10-11, branch `per-pairing-stretch` (the stretch per pairing, `docs/SUITE-REDESIGN.md` §22).

**Open (other).**

* `rung2c` beyond its control interval: `1 < dt ≤ 2.12` neither proved nor refuted, `dt > 2.12`
  false by a stated argument (not kernel-checked); outside the model (`ε_L = 1`).
* Per-mode evolve domains (the paper's Eq. 2) are outside the Lean lift; no suite_v2
  benchmark has them.
* The generic X-channel theorem is the throughout form (`check_sound_multi_cutX`); the
  Theorem 3 instances are per benchmark (response strategy and existence).

How to re-check: `docs/CERTIFICATION-CHECK.md`.
