# Stutter (stretch 0): independent soundness double check, 2026-10-30

Subject: the opt-in stretch 0 (`[problem] stutter = true`, letter W, `docs/STUTTER.md`), commits
16a8349 (tool and Lean backing) and bba18b3 (demo, tests, letter W), merged into `benchmark-fixes` in
f4050e0; `lit_nahs25_salt_tank` set the key in dbeadfc. Two fresh reviewers who did not write the
add-on read the diff (one with the emphasis on the Lean chain and the paper's semantics, one on the
trusted tool, the kernel gate, the letters and the tests); the kernel and CLI checks below were run
after their reports.

**Verdict: sound. No HIGH finding.** Every relaxed hypothesis and every new lemma is true as stated,
no existing theorem's statement got weaker in a way that matters, Theorem 3's statement is
unchanged (only its proof now admits stretch 0), and every adversarial claim declines. Five LOW
items were fixed (below); three LOW items are open notes.

## 1. Lean: relaxed hypotheses and new lemmas

| item | verdict |
|---|---|
| `CoverHyps.hlam : ∀ q, 0 ≤ lam q` (`Theorem3General.lean`), `Theorem3GeneralS` passes it through | TRUE. A weaker hypothesis makes Theorem 3 stronger; the only constructors (Keyed, StrictKeyed) supply it. |
| `CoverResp.hlam`, `epsR_nonneg` | TRUE. `epsR_nonneg` is still non-vacuous (`hspan 0` gives `0 ≤ ε_R`). |
| `SyncSwitch.joint_of_sols_lam`, `ReplayEngine.joint_stretch` at `0 ≤ λ` | TRUE. At λ = 0 the right is `Φ_R 0 = ρ`; `domR ρ` comes from the duration-0 `ODESol.hdom` at t = 0. `ODESol` (dL-caltiming `PlantT.lean`) has `hr : 0 ≤ r`, so duration 0 is a legal run, as in dL. |
| `ReplayEngine.stretch_split` (new) | TRUE, not vacuous. λ > 0: `b = a + τ/λ`; λ = 0: `τ ≤ λ(r − a) = 0` forces τ = 0 and b = a. |
| `replay_piece(_q)`, `replay_pieces(_q)`, `replay_gresp(_q, _k_q)` | TRUE. The recursion is on `K − rank q` and the second branch needs `rank q < rank e.tgt`, so well-foundedness does not depend on λ; at λ = 0 each step is a real discrete switch after a duration-0 run (`HMove` already quantified `∀ T, 0 ≤ T`). |
| `Emitted.frozen_right_constant` (new, `Region.lean`) | TRUE. Reads derivative 0 off the pair `(Rv i, 0·fR i)` of `jointSys fL fR (const 0)`; monotone and antitone; independent of `hfR`. The mirror of `frozen_left_constant`. |
| `reg_kept_joint` at `0 ≤ c` | TRUE. At c = 0: coincidence on `reg.fv ⊆ range Rv` plus the frozen coordinates. |
| `CutLift.atom_boxle_R_stutter` (new) | TRUE. DI with Lie derivative `0·(…) = 0` under `fv ⊆ Rv` (no left variable); auxiliary variables are unbound in `jointSys`, so constant too. |
| `CutLift.atom_boxle_R_strict0` (new) | TRUE. A clean split: c = 0 by `atom_boxle_R_stutter`, c > 0 by the old strict lemma. The positive-only lemmas left (`atom_boxle_R_strict`, `AtomFact.ofR_strict`, `odeSol_right_of_joint`) are reached only at c > 0 or are off the Emitted path. No division by the pairing's λ remains. |
| `Stay` (`stayR_of_query`, `atomsStayC_R`), `Barrier.nonconn_keep`, `Anchor`, `Keyed`, `StrictAnchor`, `StrictKeyed`, `Progress` | TRUE. Signature changes only (`lam_pos` → `lam_nonneg`); no downstream use needs positivity. |
| `lam_nonneg`, `lamOf_nonneg` | TRUE (the `q ≥ nR` default still goes through `lamQ > 0`). |
| `Emitted/Data.lean` `timeOK`: `0 < s.lamN ∨ p.stutter` | TRUE, and identical for `stutter = false`. The window conditions (`0 < lc.lamQ`, the budget check) are unchanged, so `δ = ε_R/lamQ > 0`, `δ_pos`, `budget_span` are still proved from the window, not the pairing. `structOK` includes `timeOK`, so the gate reads the IR literal's parsed key. |

Existing statements: none weakened in a way that matters. `jointSys`, `segDur`/δ and the budget are
unchanged for λ > 0; the verdict facts (`hbox`, `hprune`) are still queried at the pairing's own
stretch, so at λ = 0 the left's motion is checked against the mixed rows with the right frozen. Only
intermediate conclusions changed (`lam_pos` → `lam_nonneg`). The key is policy, not soundness:
`windowClaim` mentions neither λ nor the key, and the chain is proved at `0 ≤ λ`.

## 2. End to end: axioms, sorry, kernel gate

`scripts/stutter_kernel_checks.lean` (`lake env lean`, measured 2026-10-30): Theorem 3 of
`salt_tank_stutter_bridge`, `salt_tank_stutter_bridge_run`, `lit_nahs25_salt_tank_bridge` (the two
stutter benchmarks) and of three non-stutter benchmarks picked at random
(`rover_patrol_lag_bridge`, `watertank_bridge`, `turbine_startup_gearratio_bridge`) each depend on
exactly `[propext, Classical.choice, Quot.sound, RelCertifier.z3_unsat_sound]`. Grep over
`RelCertifier/`: the only `axiom` declaration is `Trusted/Oracle.lean` `z3_unsat_sound`; no
`sorry`, `admit`, `native_decide`, `implemented_by` or `@[extern]` (prose hits only).

Kernel negatives (new, same script): the demo's IR and the suite salt tank's IR with the key off
(`{ IR with stutter := false }`) and their own covers (stretch-0 pairings) make `structOK` decide
`false` (`decide +kernel`). So no bridge instance of a file without the key can accept a stretch-0
pairing, independently of the CLI guard.

The CLI side: `Run.lambdaCandidates` filters 0 out of the grid and appends it last only under the
key; `RELCERT_SYNC` gives `[1]`; a negative λ gets a negative span and is skipped before any query;
`certifyWithData` (the only `.certified` return) turns a cover with `lamQ ≤ 0`, or with `lamN = 0`
and no key, into ERROR. The joint query at λ = 0 is `ilieDeriv g fL fR (.rat 0)`: the left term is
kept, only the right field drops out (confirmed by the clock control below).

## 3. Semantics against the paper

* Definition 2 (∀∃ relational invariance) has no time alignment: ⟨Rsys⟩ already admits
  zero-iteration and zero-duration witnesses. The add-on finds witnesses the claim always allowed;
  **Theorem 3's statement does not change**.
* Joint segment ⟨leftFlowUpto(τ), rightCycle⟩: a right cycle of duration 0 is legal (the plant
  `{x' = f, t' = 1 & dom ∧ t ≤ ε}` admits duration 0 where `dom` holds; the anchor implies the one
  shared `domR`, so the frozen state is in its mode's domain).
* Assumption 1 (ii) "including the empty one" (Lean `WellFormedRModeIn` quantifies every `t` with
  an `ODESol`, t = 0 included) gives the landing after the zero-length cycle, so op_R is kept: the
  successor's guard holds at ρ, `hhand` gives the successor's anchor. Clause (i) (nonblocking) is
  not used for that node.
* Cover finiteness: in an all-stutter window the span is ε_L and the budget 1, so the node is a
  leaf; in a mixed window a stutter pairing spends budget like any other.
* No Zeno or progress assumption in the chain relies on positive right time: progress is measured
  by the left span δ > 0 and by rank.
* A stutter certificate says nothing about the reference keeping pace (by design; tested below).

Paper edits needed (`paper.tex`; Theorem 3 itself unchanged): the stretch λ > 0 → λ ≥ 0 at the
definition of stretched segments (~l. 1048) with the opt-in remark; Lemma "Time Stretching" (~l. 1115)
at λ ≥ 0 (a duration-0 run corresponds to a constant run whose domain holds at its start); the
convention ε_R/0 = ∞ so segDur = ε_L (~l. 1260, 1343, 1652; an all-stutter window uses the window
stretch ε_R/ε_L); "Selecting the stretch" (~l. 1648): 0 is the last candidate, under the key only,
and the per-pairing fallback takes 0 only for a pairing that passed at no positive stretch; the
letter legend W; the sentence that the reference need not keep pace; a macro for any new named
notion (`mymacros.sty`, next to `\stretchF`).

## 4. Adversarial tests (all with the key; `scripts/stutter_tests.py`, new cases marked adv/control)

Each "adv" claim is false for every choice of right duration, so a CERTIFIED would be unsound.

| case (edit of `benchmarks/stutter_demo/salt_tank_stutter`) | why false | verdict |
|---|---|---|
| attacked Off creeping, `xp' = 0.001` | the genuine tank can never rise | DECLINED |
| the same at band 0.0005 | one cycle opens a gap 0.001 | DECLINED |
| attacked Off sinking, `xp' = -0.1` | the left leaves `xp_L >= 25` on its own while the right waits | DECLINED |
| attacked Off drifting away, `xp' = 0.1 (xp - 25)` (field 0 at the boundary) | the right cannot rise; strict route must fail too | DECLINED |
| attacked On rising to 30 | out of the genuine tank's reach | DECLINED |
| right-only atom `xp_R <= 25.5` in the Off row | kept for free under stutter, but the On → Off handoff at 27 breaks it | DECLINED |
| shared clock `c' = 1` both sides, two-sided pace row 0.5 | needs the reference to keep pace | DECLINED |
| shared clock, `c_L <= c_R` | needs the reference to keep up | DECLINED |
| `lit_csf25_salt_tank_hold` with the key, slope 1.24 (tight 1.25) | every left mode moves; below the tight value | DECLINED |
| control: shared clock, `c_R <= c_L` | true while the right waits; checks the stretch-0 query keeps the left field in mixed rows | CERTIFIED |
| control: `lit_csf25_salt_tank_hold` with the key at its own values; its emitted cover equals the one without the key | a file that closes at λ > 0 keeps its cover | CERTIFIED, equal |
| (existing) band −0.01, λ ∈ [0, 0], attacked Off `xp' = 0.1`, the guard at `λ_min = 0` without the key, the 75 refute mutants and 3 negatives with the key | | all DECLINED |

Not in the script (Assumption 1 is a premise of Theorem 3, not a stutter matter), run by hand: the
genuine On's guard raised to 25.5, or its `next = [Off]` (no enabled successor for a frozen state in
[25, 25.5), resp. after On): the default CLI certifies (with and without the key, at band 0 and 3,
the frozen successor-completeness contract), `relcert --wellformed` reports On `UNKNOWN`, and
`RELCERT_WELLFORMED_STRICT=1` DECLINES; the Assumption 1 lemma could not be proved, so no bridge
instance exists. A positive control with ε_L = 4, ε_R = 0.25 certifies (the Off window's span is
ε_L with budget 1).

Measured 2026-10-30 after the rebuild: `stutter_tests.py` **103/103 as expected** (25 demo, control and
adversarial cases, the csf25 cover comparison, and the 78 refute mutants and negatives with the key).

## 6. Checks after the fixes (one serial `lake build`, exit 0, then the five executables)

`--check-quick-v2` 50 certified, modal 1162/1162, handoff 2827/2827, non-connection 44/44, pruned 22/22,
reposition 74/74, strict gate 181/181 (80 invariant, 101 exit), 0 UNKNOWN, 0 BLOCKING; `relcert-test`
ALL PASS (50 literals); bridge 7437/7437; progress 194/194; refute 206/206 (the 76 refutation modules
build); WellFormedBattery 77 axiom lines (75 standard, 2 `CutLiftX` lines with `z3_unsat_sound`), no
`sorryAx`; AxiomCheck 9; the three negatives DECLINED; `lit_hypercert_vehicle_s8` BLOCKING, DECLINED
under strict; ONE DOMAIN PASS (48 + 2 kind (iii)); `--wellformed` 181 modes ok; stutter demo 54/54
groups ALL DISCHARGED; `stutter_kernel_checks.lean` six axiom lines, all four standard, kernel
negatives green. Regression of the fallback change: `gen_v2_data.py` over all 50 with the new binary
leaves every committed leaf (IR, covers, progress, choice, cuts) byte-identical.

## 5. LOW findings and what was done

Fixed (2026-10-30):
1. Per-pairing fallback took 0 over a positive pass (`OracleAPI.lean`: 0 is the last and smallest
   candidate, `if lam < t` replaced a positive record), contradicting "a file that closes at some
   λ > 0 keeps that cover". Now the smallest *positive* passing stretch, 0 only if none passed (the
   reference keeps pace wherever it can). Not a soundness issue (both are certified pairings); no
   suite file reaches the fallback with a stretch-0 pass (the salt tank closes in the common pass).
2. `docs/STUTTER.md` said "keep the key off (or λ_min > 0)"; with the key, 0 is appended whatever
   λ_min is. Corrected, and the fallback rule documented.
3. Letter S for a stutter file (`scripts/suite_v2_letters.py`): SYNC drops the stretch-0 candidate,
   so a SYNC decline can be W's; S now also needs the λ = 1 variant *with the key kept* to decline.
   Likewise `\numsyncrightonly` (`scripts/paper_numbers.sh`) counted the salt tank as right-only;
   SYNC declines without a positive stretch are now split into right-only and the new
   `\numsyncstutter`.
4. `scripts/stutter_tests.py` could pass silently: four of its edits (`band`, `guard`, `lam00`,
   `with_key`) were not checked to apply. Every edit now asserts that it changes the file.
5. The suite bridge of a stutter file had no kernel record of the key: `scripts/gen_bridge.py` now
   emits `stutter_on` and `uses_stutter` (decided in the kernel) for every file with the key, as the
   demo has; plus the kernel negatives of section 2.

Open (LOW, notes):
* W could additionally require the stretch-0 pairing on the replayed path (as R does); today a
  stretch-0 pairing off the path cannot earn W anyway (the file without the key still certifies).
* The demo's BenchIR literal is not in `relcert-test`'s drift manifest (suite_v2 only); the demo is
  now the suite salt tank under another name, whose literal is checked.
* The paper does not yet state stretch 0 (section 3).
