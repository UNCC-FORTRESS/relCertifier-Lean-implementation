# Pre-landing right-only certificates (the right-only flow certificate only before the landing)

Branch `prelanding`, 2026-10-30, from `benchmark-fixes` at `4b154c3`. Scope record: the
pre-landing scoping of 2026-10-30 (probe files under `tmp/landing-scope/` of the main checkout,
not committed).

## Semantics

A right-only (reposition) segment of right mode `m_R` in window `m_L` (paper Definition
Segments) is existential: from an entry state the right runs cycles of `m_R` with the left
frozen, and the segment holds if SOME such run ends in the invariant with a retained successor
enabled. Definition Segments asks for the invariant only at the end. The certification lemma
(paper Lemma Proving Right-Only Segments) asked for more: a right-only flow certificate on the
whole domain, so the invariant holds along every run of `m_R`, also after it has landed.

With the opt-in key the right-only flow certificate is checked only BEFORE the landing:

* **Target.** The node's progress certificate names the landing: its last stage `(x, θ)`,
  built from a nonstrict threshold atom of an exit guard. The target is the closed half-space
  `x ≥ θ` (upward) or `x ≤ θ` (downward); its land queries already prove that every point of the
  line `x = θ` in the region, and every start already past it, enables an exit.
* **Region.** The pre-landing region is the half-open complement, `x < θ` (upward) or
  `x > θ` (downward) (`ProgressEmit.before`, the region the rate query already uses).
* **Certificate.** Per invariant component, one of the routes A (`dom ∧ ġ > 0`), B
  (`dom ∧ g = 0 ∧ ġ ≥ 0`), C (`dom ∧ g ≥ 0 ∧ ġ > 0`) is UNSAT over the reposition domain
  (both evolves, both modes' kept atoms, the proven strata, the left guard pre-joint) conjoined
  with the pre-landing region, the left frozen, stretch 1. A strict component takes route A
  only. The whole-domain certificate (route A on the whole domain) implies this one.
* **Witness.** The right run of the progress argument (full cycles of `m_R`, then a landing
  cycle) stops at its FIRST entry into the target and ends that control cycle early (a cycle of
  any duration in `[0, ε_R]` is legal: the plant is `{x' = f & dom ∧ t ≤ ε}`, `t := 0` per
  cycle). Before that instant the run is in the pre-landing region, where the certificate
  keeps the invariant; at the instant the invariant holds by continuity, and the line
  `x = θ` is reached, where an exit is enabled.

## Opt-in

`[problem] prelanding = true` (default `false`; any value other than `true`/`false` is a parse
error; `KeyAudit` recognizes the key; the IR prints `prelanding := true` only when set). With the
key:

* `coverMode` does not try the whole-domain pack (`checkDynRepo`); every reposition node is a
  pre-landing node (the pre-landing pack is implied by the whole-domain pack on the same strata,
  so no node is lost).
* Progress runs first. `checkProgress` takes an `accept` callback: a found stage list is
  returned only if the pre-landing pack holds on the region before its last stage
  (`checkDynRepoPL`); otherwise the next candidate threshold is tried. Without the key the
  callback accepts, so the search is the old one.
* The node is recorded in its own list (`prelandLog`, emitted under `RELCERT_PRELANDING_OUT` as
  `Preland.PrelandEmitE`: `(mL, mR, pre, order)` per node). It is NEVER written as the cover's
  `dynPre`/`dynPost` flag: the emitted cover keeps those for the whole-domain pack, and with the
  key they are all off. The cover graph is built on the merged rows (`effRows`: the emitted rows
  with the pre-landing nodes merged in), the kernel's `Emitted.withPL` is the same merge.

**Guard.** `certifyWithData` turns a cover with a pre-landing node into ERROR unless the problem
has `prelanding = true` (defence in depth: `coverMode` finds none without the key). The
kernel-side data gate `Emitted.plOK` admits a nonempty pre-landing record only when the IR has
`prelanding := true`, and then requires the emitted whole-domain flags to be all off.

## Soundness

Paper Theorem 3 (`lem:composition`), Definitions Segments and Strategy, `RepoProgress` and
`theorem3_of_coverX` are unchanged. What changes is how `RepoProgress` of a node is proved.

1. **Closed target, first entry.** The target `x ≥ θ` is closed (a nonstrict threshold), so
   the first entry into it is attained (`first_hit`: the `sInf` of the closed hitting set,
   `IsClosed.csInf_mem`, the pattern of `Flow/DIStrictOpen.lean`). Before it the run is in
   `x < θ`; at it `x = θ` (the intermediate value theorem on `[0, t*]` and minimality).
2. **The invariant before and at the stop point.** On every proper prefix `[0, s]`, `s < t*`,
   the run is in the region, so the pre-landing pack keeps the rows and the kept atoms
   (`couple_box_dynPL`, the closed-domain DI with routes A/B/C, lifted through the checked
   cuts). The row and atom terms are `≤ 0` terms, continuous along the run, so they are `≤ 0`
   at `t*` too (`AG_boxPLH`, `le_zero_of_Ico`). The barriers of the pruned exits and the
   envelope are whole-domain facts (unchanged). A strict component (`< 0`) passes only route A
   in the tool, where `g` is nonincreasing on `[0, t*)` and so `g(t*) ≤ g(0) < 0`; the Lean
   chain of this branch is the non-strict one (the strict chain `StrictKeyed` keeps the
   whole-domain pack).
3. **Landing.** At `t*` the right ends its cycle early (a legal duration) and switches along
   an exit enabled on the line (land query 1); a start already past the threshold lands at
   once (land query 2). Cycles before the landing cycle have `x < θ` on their whole interval,
   so the certificate applies to all of them; at their boundaries Assumption 1 (ii) gives
   `m_R` again or a declared successor (a non-self one is an earlier landing; a pruned one is
   excluded by the non-connection certificate).
4. **Progress queries.** They assume the region (with the invariant), which holds along the
   pre-landing run and at its stop point; rate and keep live before the threshold, the land
   queries on the line. Unchanged.
5. **Composition, budget, handoff, stutter, choice.** A right-only segment consumes no budget
   and the left is frozen during it; handoff concerns left mode changes; stutter is a joint
   kind; a chosen subset's coverage is over `leftFacts ∧ rightFacts(m_R)`, which the stop state
   satisfies. All unchanged.

**Excluded, by construction:** an open target (a strict guard gives no threshold candidate,
so no progress certificate and no node: the source's `temp > 100`); a landing at a non-first
hit (the witness is the first entry); a strict component through routes B/C (route A only); an
old-path consumer reading `dynPre`/`dynPost` as a whole-domain certificate (the pre-landing
node has its own record; the emitted flags are off).

## Lean (no `sorry`, no new axiom)

The whole-domain chain and its 51 instances are untouched: every new piece is additive.

| file | content |
|---|---|
| `Trusted/PrelandEmit.lean` (new) | `PrelandNodeE`, `PrelandEmitE`, `find`, the emitter |
| `Trusted/Parse.lean`, `KeyAudit.lean`, `EmitIR.lean` | `PProblem.prelanding : Bool := false`, the key, printed only when true |
| `Trusted/OracleAPI.lean` | `checkDynRepoPL`; `checkProgress`'s `accept`; `coverMode`: progress first under the key, `plMap`, `effRows`, the merged context; `prelandLog`; the guard; `RELCERT_PRELANDING_OUT` |
| `Proofs/Encoding/ProgressPL.lean` (new) | `first_hit`, `first_hit_down`; section `NodeB` with the pre-landing premise `hboxB` (the anchor is kept along a right-only run that stays in a region `Bf` before its last instant): `merged_runB`, `keep_preservedB`, `phaseB`, `phase_downB`; section `CloseB`: `repoProgress_oneB`, `repoProgress_twoB`, `repoProgress_one_downB` |
| `Proofs/Encoding/ReplayDynPL.lean` (new) | `VerdDynCorePL`, `modalVerdDynPLX` (the pack as `checkDynRepoPL` sends it), `segPresAll_dynPL`, `couple_box_dynPL` |
| `VerdictsV2/ModalDynPL.lean` (new) | `modalVerdDynPLXQueries` (the rebuild, one group of three routes per component), `modalVerdDynPLX_of_queries` (the pin) |
| `Proofs/Encoding/Emitted/Prelanding.lean` (new) | `withPL`, `plOK`, `DynVerdPL` (the pack at the region before the certificate's last stage, read via `certFor`), `VerdictsPL`, `le_zero_of_Ico`, `merge_continuousOn`, `AG_boxPLH` (the half-open extension), `hrepoProg_ofPL`, `coverHyps_ofPL`, `hcov_ofPL`, `theorem3_window_of_records_pl` (the claim over the EMITTED cover), `dynGroupsPL`, `bridgeGroupsPL`, `verdictsPL_of_groups` |
| `InstancesV2/WellFormed/EngineCoolingPrelanding.lean` (new) | Assumption 1 of the demo's right model, Z3-free |
| `InstancesV2/Bridge/EngineCoolingPrelanding.lean` (generated) | the demo's Theorem 3 |

`RepoProgress`, `theorem3_of_coverX`, `CoverHyps`, the suite's `Verdicts`/`bridgeGroups` and
every existing instance keep their statements. Pieces of `Keyed.lean`/`Window.lean`/`Run.lean`
that read the `Verdicts` structure (`cov_of_entry`, `coverHyps_of`, `hcov_of`,
`theorem3_window_of_records`, `verdicts_of_groups`) are restated for `VerdictsPL` (about 250
of the 631 lines of `Emitted/Prelanding.lean`, chosen over editing the chain that 51 instances
rest on). `ProgressPL.lean` (652 lines) mirrors `Progress.lean`'s `merged_run`,
`keep_preserved`, `phase`, `phase_down` and the three closers with the first-hit landing and the
`Bf` premise; the whole-domain versions stay as they were. This is a deviation in form from the
scope (which planned in-place edits of `Progress.lean`, `ReplayDyn`, `StrictCouple`, `ModalDynX`,
`Emitted/{Anchor,StrictAnchor,Progress,Run,Keyed,StrictKeyed}` and `RunV2`): the additive
route leaves every existing statement, file and count untouched. New Lean lines: about 1760.

## The demo: NAHS 2025 engine cooling

`benchmarks/prelanding_demo/engine_cooling_prelanding` (NOT in suite_v2): Xiang, Lanotte, Tini,
Chong, Merro, arXiv 2403.05829, Secs. 3-5, Examples 3 and 5. Left (attacked): Cool
`temp > 99.7` (`temp' = -0.5`), Heat `temp <= 100.3` (`temp' = 1`); right (genuine): Cool
`temp >= 100`, Heat `temp <= 100`; `ε_L = ε_R = 1`, `λ = 1`, domain `temp >= 0`; rows
`|temp_L - temp_R| <= 0.3` in both modes.

**Departure (disclosed):** the genuine Cool guard is closed to `temp >= 100` (the source has
`temp > 100`, so the genuine controller becomes nondeterministic at exactly 100). The progress
certificate takes its threshold from a nonstrict guard atom only; with the source's guard the
file DECLINES (no closed target), as the tests check. A strict-landing extension was scoped
(about 60-100 Lean lines) and not built.

Cover (`RELCERT_DEBUG`): Cool_L {Cool joint; Heat pre-landing (`temp ≥ 100` at rate 1) then
Cool joint}, Heat_L {Heat joint; Cool pre-landing (`temp ≤ 100` at rate 1/2) then Heat joint};
budget 1, so only pre-joint nodes.

| measurement | result |
|---|---|
| band 0.3 (the paper's forward distance, Example 3/7) | CERTIFIED |
| band 0.29 | DECLINED (tight value 0.3, attained: the region is half-open) |
| band 0.31 | CERTIFIED |
| band 0.3 without the key | DECLINED |
| band 0.3 with the key, `RELCERT_NO_REPO=1` | DECLINED: the right-only kind is genuine, letter R |
| the source's strict genuine Cool `temp > 100`, with the key | DECLINED (no closed target) |
| cause: attack offset `o` in {0, 0.1, 0.5, 1}, band `o` / `o - 0.01` | CERTIFIED / DECLINED for every `o > 0`; `o = 0` certifies at band 0 (exact): the tight band tracks the attack offset |
| letters (`suite_v2_matrix.py` + `suite_v2_letters.py` over `benchmarks/prelanding_demo`) | `engine_cooling_prelanding: R`, `TOTALS ... R=1` |

**Kernel.** `scripts/gen_prelanding_demo.py` emits the demo's leaves (IR, cover, progress,
choice, cuts, and the pre-landing record `InstancesV2/BenchPrelanding/`) and the bridge instance
`InstancesV2/Bridge/EngineCoolingPrelanding.lean`: the data gate `pl_ok`, `struct_ok`, `prog_ok`,
`covers_ok`, `rows_same`, `pad_ok` decided in the kernel on the merged cover; Assumption 1 from
the demo's own lemma lifted to dimension 4; `prelanding_on`, `uses_prelanding` decided.
`engine_cooling_prelanding_bridge_run` is Theorem 3 (window form) over the EMITTED cover from a
green run of `bridgeGroupsPL`. `lake env lean scripts/prelanding_demo_verdicts.lean`:
`4 pre-landing groups`, `18/18 groups, ALL DISCHARGED`. `lake env lean
scripts/prelanding_kernel_checks.lean`: the instance theorems at `[propext, Classical.choice,
Quot.sound, RelCertifier.z3_unsat_sound]`, `first_hit` and `repoProgress_twoB` at the three
standard axioms, and two kernel negatives: the record with the key off fails `plOK`, and the
emitted cover without the pre-landing nodes fails `coversOK`.

## Tests

`scripts/prelanding_tests.py` (variant files in a temporary directory, `RELCERT_IMPLIED_CUT=1`),
101/101 as expected (2026-10-30):

| case | verdict |
|---|---|
| engine band 0.3 / 0.31 | CERTIFIED |
| engine band 0.29; band 0.3 without the key; band 0.3 under `RELCERT_NO_REPO`; the source's strict genuine guard | DECLINED |
| cause: offset `o` in {0, 0.1, 0.5, 1}, band `o` | CERTIFIED |
| cause: offset `o` in {0.1, 0.5, 1}, band `o - 0.01` | DECLINED |
| adversarial fails-after: a frozen left against a right that climbs in `Up` (guard `y <= 0`) and holds in `Hold` (guard `y >= 0`), row `y_R <= 0`: the row breaks only past the landing threshold | CERTIFIED with the key, DECLINED without |
| adversarial fails-before: the same with the threshold `1` and the row `y_R <= 0.5`: the row breaks before the landing (the claim is false) | DECLINED |
| adversarial strict-target: fails-after with the `Hold` guard opened to `y > 0` | DECLINED |
| the 75 `refute_mutants` and 3 `negative` files with the key | 78/78 DECLINED |

## Regression (key off, no input changed)

The `4b154c3` binary against this branch's, both with `RELCERT_IMPLIED_CUT=1`, over the 50
suite_v2 files, the 2 choice exhibits, the stutter demo and the 2 strict demos (55 files):
the `--emit-cover` output with its progress and choice leaves, and the verdict lines (time
stripped) under the control run, `RELCERT_SYNC`, `RELCERT_NO_CHOICE`, `RELCERT_NO_PRUNE`,
`RELCERT_NO_REPO`, `RELCERT_NO_CUT`, `RELCERT_NO_PAIR_STRETCH`: 440 comparisons, 0 differences.
`--check-quick-v2` output (times stripped) identical: 50 certified, modal 1185/1185, handoff
2831/2831, non-connection 38/38, pruned 19/19, reposition 70/70, strict gate 176/176 (78
invariant, 98 exit), `SUITE_V2 QUICK CHECKS PASSED`. Lean, rebuilt (`lake build`: 9287 jobs, exit 0, no `sorry`; the five
executables): `relcert-bridge-verdicts` 7375/7375, `relcert-progress-verdicts` 162/162,
`relcert-refute-verdicts` 227/227, `relcert-test` ALL PASS (50 IR literals), each output
identical (times stripped) to the runners built before the branch; `WellFormedBattery` 77 axiom
lines (75 at the three standard axioms, the 2 `CutLiftX` replay lines with `z3_unsat_sound`),
`AxiomCheck` 9, no `sorryAx`; `check_one_domain.py` PASS (48 + 2 kind (iii)); the three
negatives DECLINED (`errors=0`); `lit_hypercert_vehicle_s8` 5/5 BLOCKING, DECLINED under strict;
`scripts/stutter_tests.py` 109/109; stutter demo 54/54 groups, `stutter_kernel_checks.lean` 6
axiom lines, no error. (`scripts/gen_stutter_demo.py` regenerates the stutter leaves
byte-identically but writes `stutter_on`/`uses_stutter` twice into its instance, since
`gen_bridge.py` now emits them for a keyed file too; a pre-existing generator issue, not
touched here; the committed instance was restored.)

**Global key (ablation preview, not a suite change).** Every suite_v2 file with
`prelanding = true` added: 50/50 CERTIFIED; 38 files have pre-landing nodes (963 node records
in all). With the key every reposition node is a pre-landing one, so covers and counts change;
the paper numbers stay those of the key-off suite.

## Paper (draft wording; the paper repository is not edited)

New macros, next to the progress-certificate family of `mymacros.sty` (Section 4.2):

```latex
\newcommand{\preLand}[1]{\hostE{\mathit{pre}(#1)}}   % pre-landing region of right mode #1: its certificate's last stage not yet crossed (x_n < theta_n upward)
\newcommand{\flowCrop}[2]{\hostE{\flowCsym(#1,#2,\rightonlyKind,\mathit{pre})}}   % right-only flow certificate on the pre-landing region
```

**Lemma (l.1379), replacing the statement and proof sketch.** The `\retsucc` landing stays.

```latex
\begin{lemma}[Proving Right-Only Segments]
\label{lem:rightonly-segment}
If $\repoC{\preSyncFlag}{\modesymR}$ holds with last stage
$\progStage{\nstage}$, and $\flowCrop{\modesymL}{\modesymR}$ holds, the right-only flow
certificate with its domain conjoined with $\preLand{\modesymR}$, then
$\rightSeg{\preSyncFlag}{\modesymR}{\retsucc{\modesymR}}$ holds.
\end{lemma}
\begin{proof}[Proof sketch]
An entry state satisfies $\cutOf{\modesymL}$ and
$\cutOf{\modesymR}$, and so does
the start of every later cycle, since the \leftsys is frozen and
$\rightCycle$ tests $\guardcond{\modesymR}$. Take the run of cycles that the reposition
certificate gives and stop it at its first entry into the closed set
$\stageVar{\nstage} \geq \stageTh{\nstage}$, ending that cycle early, which the timer bound
$\timerR \leq \intVR$ allows. Before that instant the run lies in $\preLand{\modesymR}$, where
the flow certificate keeps $\relfmlinvMode{\modesymL}$, and at the instant the invariant
holds by continuity. There $\stageVar{\nstage} = \stageTh{\nstage}$, where a retained successor
is enabled, so the run witnesses the segment.
\end{proof}
```

**Sec. 4.1, l.1143-1146** (the sentence after Eq. `rightonly-product`):

> A flow certificate guarantees that one of these product programs keeps
> `\relfmlinvMode{\modesymL}`. For a right-only segment Definition~\ref{def:segments} needs
> `\relfmlinvMode{\modesymL}` only at the end, and
> Lemma~\ref{lem:rightonly-segment} uses this: it needs the flow certificate only before the
> landing.

**Sec. 6.1, l.1674** (the reposition paragraph's last sentence):

> This yields a reposition certificate: cycles stay in `\regionR` by the right-only flow
> certificate and the mode facts until the last threshold is crossed, and an uncrossed stage
> gains at least `\stageRate{i}\intVR` per cycle, so the last threshold is crossed in finitely
> many cycles.

The running example (l.1440-1443) stays true: its failure point lies before the landing.
`docs/SUITE-REDESIGN.md` lesson 5 ("needs ... preserved on the whole domain") holds without the
key only. Net page cost about +2 lines. The paper's Lie Conditions already state routes A, B
and C for the right-only kind; with the key the tool and Lean use all three.

## Not done (scope)

* The strict-landing extension for an open target (the source's `temp > 100`): not built; the
  demo closes the genuine Cool guard (disclosed above).
* The strict chain (`StrictKeyed`, strict rows): keeps the whole-domain pack; a keyed benchmark
  with strict rows certifies in the tool (route A on strict components) without a bridge
  instance.
* Not merged into `benchmark-fixes`; the engine benchmark is not installed in suite_v2.
* The global setting (the key on for every file) is an ablation for later: the 2026-10-30 census
  counts 1187 nodes in 43 suite files that fail today's whole-domain check.
