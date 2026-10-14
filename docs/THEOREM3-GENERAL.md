# Theorem 3, generically, with the existential mode choice (branch `theorem3-general`)

Status: the general theorem is proved (`Proofs/Encoding/Theorem3General.lean`,
`theorem3_of_coverX`, axioms `propext`, `Classical.choice`, `Quot.sound`); instances for
`vehicle_hypercert`, `vehicle_accel_copy`, `watertank_choice` and the suite's `watertank` go
through it (`InstancesV2/Choice/General/`), each with the standard three axioms plus
`z3_unsat_sound`. Before this branch the paper's Theorem 3 was mechanized per
benchmark: generic lemmas (the outer loop rule, the replay engine, guarded switching) and a
per-benchmark construction of the response. Now the construction is one theorem whose
hypotheses are Theorem 3's conditions.

## 1. The statement

`theorem3_of_coverX` concludes `rvalid (theorem3Form L R ψ)`: the encoded ∀∃ invariance over
the guard-gated left windows `L` (one per left mode, each of duration at most `dt`) and the
guarded right automaton `R`, with the loop invariant `ψ` = the declared row ∧ the evolve
envelope ∧ the right mode's region (its guard and its kept atoms: the paper's operating region
`op_R`). Its hypotheses, grouped as the paper's conditions:

1. **Assumption 1** (`hwf : WellFormedR G guard ε_R`): from every state of a mode's guard the
   run of one right interval exists, and every run of duration at most `ε_R` ends in some
   declared successor's guard.
2. **The covers** (`hcov`): for every left mode `l` and every admissible start `q`
   (`AdmissibleStart`: some joint state satisfies the left guard, the row, the envelope and the
   right region), `CoveredX G (ch l) (q, B_l, preJ)`; and `dt ≤ B_l · δ_l`.
3. **The certificates** (`CoverHyps`, per left mode): the flow certificate of every certified
   pairing at its stretch (`hbox`, Theorem 1); the reposition certificates (`hboxDpre/Post`);
   the non-connection certificates of the pruned edges (`hprune`, `hpruneD`, Theorem 2); the
   coverage certificates of the chosen sets (`hcovJ`, `hcovR`, `hcovS`, with the regions
   implied by the anchor); the entry condition (`hhand`); and the reposition-progress premise
   (`hrepoProg`, §3).

The time model is the tool's: a common segment span `δ = ε_R / λ_max` with `λ_q δ ≤ ε_R` per
pairing (`hspan`), unit weights, budget `B = ⌈ε_L / δ⌉`.

## 2. The proof

`CoveredX` (`Checker/CoverX.lean`) is Definition 4 with cases 3 and 4 of
`docs/CHOICE-SOUNDNESS.md`; `decideCoveredX` is the checker and `decideCoveredX_sound` its
soundness. The cover flags (which pairings are certified) and the chosen sets are per window
(`ChoiceData`), so one right automaton serves every window.

`coverX_piece` (`Proofs/Encoding/CoverResp.lean`) is the induction: a covered configuration
answers one clocked left piece from left time `a` if `r − a ≤ B δ`. Base and step run the
joint segment (Assumption 1 gives the right run, `joint_stretch` carries the anchor, Assumption
1 again gives an enabled successor, Theorem 2 excludes pruned ones); chosen successors come
from the coverage certificate at the segment's end; right-only steps reach an exit by
reposition progress; chosen exits and hops switch at duration zero. `coverX_gresp` lifts the
piece response to the gated window; `Hmulti_of_coverX` and `theorem3_of_coverX` assemble the
windows into the loop through `Hmulti_regionG`, `hstep_assembled_GR` and
`theorem3_faithful_multiR_LR`, exactly as every per-benchmark instance did.

## 3. Reposition progress: the certificate the paper's proof sketch was missing

The proof sketch of Theorem 3 says Assumption 1 "continues every segment along a retained
edge". For a joint segment that is right. For a **right-only** segment it is not: Assumption 1
may enable only the self-loop, the rule requires a non-self exit, and the tool never checked
that an exit is reached. The 12 benchmarks whose covers use right-only steps rest on exactly
that (with the all-successors right-only rule disabled, `RELCERT_NO_REPO=1`, they decline:
34/46). Their standalone Lean proofs had discharged it from explicit solutions (`HExit`).

The fix is a **progress certificate** (`Trusted/ProgressEmit.lean`, `RELCERT_PROGRESS=1`),
checked by the tool per reposition node like every other certificate: a stage
`(x, θ, r)` says "while `x < θ` (on the node's region, the facts the reposition flow keeps)
the field of `x` is at least `r > 0`"; an optional helper stage `(y, y₀, r₁)` first (its
crossed fact `y ≥ y₀` is kept, and the main rate holds under it); and the landing: on the
crossing line `x = θ` and at a start already crossed (`guard(q) ∧ x ≥ θ`) some exit's guard
holds. With the certificate required the suite certifies 46/46 (261 certificates, 110 with a
helper stage; the four nodes without one are never used). The right-only rule and Assumption
1 are unchanged; the right-only kind is now *certified*: preservation (certificate 3) plus
progress.

`Proofs/Encoding/Progress.lean` proves the certificate sound: `repoProgress_one` and
`repoProgress_two` give `RepoProgress` (the general theorem's premise: from a reposition start,
cycles of the node until an exit is enabled, the anchor kept) from the certificate's facts,
Assumption 1 (each cycle's run, and an enabled successor at its end), the reposition flow
certificate (the anchor is kept) and the right-only non-connection certificate (a pruned exit
is never enabled). Each cycle without crossing advances the stage coordinate by `r ε_R`, so the
cycles are bounded; a crossing lands by the intermediate value theorem. Axioms: the standard
three.

## 4. Instances

| benchmark | windows | cover | discharged here |
|---|---|---|---|
| `vehicle_hypercert` | 5, `dt ≤ 1` | hop into the left's mode, then base | hop certificate by arithmetic; Assumption 1 (`odeSol_constRight`); 5 packs |
| `vehicle_accel_copy` | 3, `dt ≤ 1` | the same | hop certificate (`guardR_of_guardL`); 3 packs |
| `watertank_choice` | 3, `dt ≤ 1` | `Low` at the per-pairing stretches (δ = 2/7, B = 4), all-successors with `Low → PumpOff` pruned; `Mid` from `MidEco` by a hop into `MidBoost`; decided by `decideCoveredX` in the kernel | Theorem 2 for the pruned edge by arithmetic; hop certificate; Assumption 1 with the economy set point; 7 packs |
| `watertank` (suite) | 3, `dt ≤ 1` | the tool's emitted cover: `Low` and `Mid` at stretch 2 (δ = 1/2, B = 2), all-successors with `Low → PumpOff` pruned; no choice; decided in the kernel | Theorem 2 by arithmetic; Assumption 1 transported from the suite's lemma; the suite's 7 packs plus `Low/High` at 2 (see below) |

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
remain; the general instances are new theorems (`*_general`) with the same conclusion shape
(their region beyond the declared modes is `⊤` instead of `⊥`, immaterial under `mvRegionR`).

## 5. Not yet done

* Mode-dependent rows (one row per left mode): the per-window response `Hmulti_of_coverX` is
  row-generic; the assembly through `theorem3_modeKeyed` is not written.
* Replay of the tool's emitted choice covers: the tool does not emit them yet (D5); the
  instances above write their covers by hand and decide them in the kernel.
* The progress verdict runner and pins (the emitted `ProgressE` rebuilt into the queries the
  tool issued, their `unsat` answers bridged to the semantic facts `repoProgress_*` take), and
  an instance with a reposition node through the general theorem.
* The remaining 43 suite benchmarks are not re-derived through the general theorem (their
  standalone proofs stand).
