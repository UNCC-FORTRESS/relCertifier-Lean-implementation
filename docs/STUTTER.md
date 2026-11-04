# Stretch 0 on joint segments (the witness stands still)

The paper's stretch is any `λ ≥ 0` (Lemma 1, Time Stretching); at stretch 0 the witness stands
still while the left runs (Section 6.1, "Flow certificates and the stretch.": `0` comes last,
and only when the declared range includes it). The tool and Lean call this "stutter". Stretch 0
is credited under the mechanism letter S.

**Status: always on, within the declared range.** Stretch 0 is a run feature, on for every
benchmark (`PProblem.stutter`, default `true`, not read from the file; the former key `stutter`
is refused by the unknown-key gate). It is a candidate (the last one, after every positive
stretch, and per pairing in the fallback) only when the feature is on AND the file's declared
stretch range includes 0, i.e. `lambda_min = 0` (`Run.stutterAllowed`): the declared range is
part of the file's stated timing tolerance (`lit_freedm_meter`, for example, declares `[1, 1]`
because its source treats time as public). The positive grid is built on the declared range,
`0` removed. The CLI guard and the kernel gate `Emitted.timeOK` read the same predicate (the
kernel decides it on the IR's `lambdaMin`); a bridge instance's `stutter_on` states
`Run.stutterAllowed IR = true`. The ablation `RELCERT_NO_STUTTER=1` switches it off for a run
(`Oracle.withRunFeatures`); the emitted IR records the run's value (printed only when off). The
property (Theorem 3's statement) is unchanged and the feature is sound for every benchmark
(below). The suite file `lit_nahs25_salt_tank` and the demo declare `[0, 1]` (the source's
distance is time-abstract); every other file declares `λ_min > 0` and never tries stretch 0.
Only `lit_nahs25_salt_tank` needs it (it declines under the ablation,
`docs/paper-numbers/nostutter.txt`). Below, "on" is the default run and "off" is
`RELCERT_NO_STUTTER=1`.

## Semantics

A joint segment of a left mode `m_L` with a right mode `m_R` at stretch `λ` runs the product
`{x_L' = f_L, x_R' = λ·f_R} & dom_L ∧ dom_R` (`FlowCert.jointSys`): the right covers `λ` units of
its time per unit of left time. At **λ = 0** the right does not move while the left runs the
segment: the right's witness cycle has duration 0 (the right *waits*, or stutters). This is the
mirror of the right-only (reposition) segment, in which the left waits.

* The property is unchanged: ∀∃ relational invariance (paper Def. 2) asks, for every left
  cycle, for *a* right run of any duration ending in the invariant. A zero-duration right cycle
  is such a run (the plant `{x' = f, t' = 1 & dom ∧ t ≤ ε}` admits duration 0 where `dom` holds,
  and Assumption 1 (ii) quantifies over every duration `≤ ε_R`, including 0).
* A stutter certificate says nothing about the right keeping pace: the witness may wait for as
  long as the left holds a level it can match. A file whose reference must keep time declares
  `λ_min > 0`, and stretch 0 is then never tried.

## The candidate order

`Run.lambdaCandidates` appends `λ = 0` as the **last** candidate, after `ε_R/ε_L` and the
21-point grid on `[λ_min, λ_max]`, so a file that closes at some `λ > 0` keeps that cover. In
the per-pairing fallback (no common `λ` closes the cover) each pairing takes the smallest
*positive* stretch at which it passed and `0` only if it passed at none
(`docs/STUTTER-SOUNDNESS.md`): the reference keeps pace wherever it can. `RELCERT_SYNC=1`
(λ = 1 only) drops it.

**Guard.** `certifyWithData` turns a cover with a stretch-0 pairing into ERROR unless
`Run.stutterAllowed` holds (and any window stretch `≤ 0` into ERROR always).

## The certificate

The certificate of a stretch-0 pairing is the existing joint flow certificate with `λ = 0`
substituted: the same queries (`ilieDeriv g f_L f_R (.rat 0)`: the right field drops out), the
same strata, cuts and routes A/B/C. There is no new certificate kind, emission format or checker.

The emitted cover (`CoverEmit`): the pairing's `lamN = 0, lamD = 1`; the window keeps a positive
`lamQ`. An all-stutter window (`Run.windowOf`) has `lamQ = ε_R/ε_L`, span `δ = ε_L` and budget
`B = 1` (one segment covers the left residence); a mixed window (per-pairing fallback) keeps
`λ̂ = max` of its pairings. So the window invariants of the bridge (`0 < lamQ`, `δ_pos`,
`budget_span`) are untouched and only the pairing's stretch becomes `≥ 0`.

## Soundness (paper Theorem 3 and the Lean chain)

Every `λ > 0` ingredient holds at `λ = 0`:

1. **Joint segment.** The right runs its current mode for duration `λ·(b − a) = 0`; the joint run
   is the left run with the right constant (`SyncSwitch.joint_of_sols_lam`, which needed only
   `0 ≤ λ`). The flow certificate keeps the anchor along it (`CoverHyps.hbox`, unchanged).
2. **Landing.** After a zero-duration right cycle, Assumption 1 (ii) gives an enabled declared
   successor (`WellFormedRIn` quantifies `t ≤ ε`, including 0); non-connection pruning is checked
   along right cycles from the entry, which include the duration-0 state.
3. **Budget.** `segDur = min(ε_L, ε_R/0 = ∞) = ε_L`: a stutter node closes the branch. In the
   replay engines the right's switch time `τ ≤ λ(r − a) = 0` forces `τ = 0` and the left switch
   time `b = a` (`ReplayEngine.stretch_split`); the recursion still climbs in rank.
4. **Frozen right.** The ∀-side lemmas that recovered a right run from a joint run by dividing by
   `λ` get a frozen case: right coordinates are constant along `jointSys f_L f_R (const 0)`
   (`Emitted.frozen_right_constant`, the mirror of `frozen_left_constant`), and a right-only term
   has Lie derivative `0·(…) = 0` (`atom_boxle_R_stutter`), so right atoms, barriers and the
   region stay.
5. **Composition** (handoff at left mode changes) is `λ`-independent.

Lean changes (no `sorry`, no new axiom):

| file | change |
|---|---|
| `Proofs/Encoding/Theorem3General.lean` | `CoverHyps.hlam : ∀ q, 0 ≤ lam q` |
| `Proofs/Encoding/CoverResp.lean` | `hlam` to `0 ≤`; `epsR_nonneg` from `0 ≤ λ·δ ≤ ε_R` |
| `Proofs/Encoding/SyncSwitch.lean` | `joint_of_sols_lam` at `0 ≤ λ` |
| `Proofs/Encoding/ReplayEngine.lean`, `ReplayEngineQ.lean` | `joint_stretch`, `replay_piece(_q)`, `replay_pieces(_q)`, `replay_gresp` at `0 ≤ λ`; new `stretch_split` (the τ/λ case split) |
| `Proofs/Soundness/CutLift.lean` | new `atom_boxle_R_stutter` (frozen right atom), `atom_boxle_R_strict0` (route B at `0 ≤ c`) |
| `Proofs/Encoding/Emitted/Stay.lean`, `Barrier.lean` | `stayR_of_query`, `atomsStayC_R`, `nonconn_keep` at `0 ≤ c` (route B via `atom_boxle_R_strict0`) |
| `Proofs/Encoding/Emitted/Region.lean` | new `frozen_right_constant`; `reg_kept_joint` at `0 ≤ c` |
| `Proofs/Encoding/Emitted/Data.lean` | `timeOK`: `0 < lamN ∨ Run.stutterAllowed p` (stretch 0 only when the feature is on and `lambdaMin = 0`) |
| `Proofs/Encoding/Emitted/Anchor.lean`, `Keyed.lean`, `StrictAnchor.lean`, `StrictKeyed.lean` | `timeOK_at` yields `0 ≤ lam`; `lam_pos` to `lam_nonneg`, `lamOf_pos` to `lamOf_nonneg`; `stayR_dom`, `barriers_keep` at `0 ≤ c` |
| `Trusted/Parse.lean`, `KeyAudit.lean`, `EmitIR.lean` | `PProblem.stutter : Bool := true` (a run feature, set by `Oracle.withRunFeatures`; the file key is refused), printed only when off |
| `Trusted/Run.lean`, `OracleAPI.lean` | `lambdaCandidates … stutter`, `windowOf`, the window stretch separate from the pairing's in the λ loop, the per-pairing fallback and the choice path; the guard |

## Tests

`scripts/stutter_tests.py` (variant files in a temporary directory, `RELCERT_IMPLIED_CUT=1`;
172/172 on the last run, `docs/CERTIFICATION-CHECK.md`, with the adversarial cases of
`docs/STUTTER-SOUNDNESS.md` and the declared-range cases). Its base cases:

| case | verdict |
|---|---|
| `benchmarks/stutter_demo/salt_tank_stutter` (the suite salt tank, range `[0, 1]`), band `c` in {0, 0.5, 1, 2, 2.99, 3} | CERTIFIED (all) |
| band 0 with the feature off | DECLINED |
| band 3 / 2.99 with the feature off | CERTIFIED / DECLINED (the suite file's tight value 3) |
| band -0.01 with the feature on | DECLINED (the rows admit no start) |
| band 0, `λ_min = 0`, feature off (the guard) | DECLINED |
| `λ ∈ [0, 0]` with the feature on | DECLINED (the attacked On moves, the frozen right cannot follow) |
| the attacked Off drifting (`xp' = 0.1`), band 0, with the feature on | DECLINED |
| the 140 `refute_mutants` and 3 `negative` files, feature on | 143/143 DECLINED |

So the salt tank's tight band is **0 with the feature on** (3 without). The demo's cover: On_L at
`λ = 1` (budget 1); Off_L window `lamQ = 1 = ε_R/ε_L`, budget 1, both pairings `lamN = 0`
(`RELCERT_DEBUG`: `[Off_L λ=1] On=fail`, `[Off_L λ=0] On=pass Off=pass`). It declines under
`RELCERT_SYNC=1` and certifies under `RELCERT_NO_CHOICE`, `RELCERT_NO_PRUNE`, `RELCERT_NO_REPO`.

Kernel: `scripts/gen_stutter_demo.py` emits the demo's leaves and the bridge instance
`InstancesV2/Bridge/SaltTankStutter.lean` (window form, Assumption 1 transported from the suite
salt tank); `lake env lean scripts/stutter_demo_verdicts.lean` discharges its query groups.

Measured: the instance kernel-checks (`lake build RelCertifier.InstancesV2.Bridge.SaltTankStutter`,
no `sorry`); `stutter_on` (`Run.stutterAllowed IR = true`) and `uses_stutter` (a pairing with `lamN = 0`)
are decided in the kernel; `[stutter demo] 54/54 groups, ALL DISCHARGED`. So
`salt_tank_stutter_bridge_run` gives Theorem 3 at band 0 end to end; its axioms are
`[propext, Classical.choice, Quot.sound, RelCertifier.z3_unsat_sound]`, as every bridge instance.

## Letters

Stretch 0 is a special case of stretching, so it is credited under **S**; there is no separate
letter. `scripts/suite_v2_letters.py` marks S needed for a stutter pairing when some cover has a
stretch-0 pairing (`lamN = 0`) and the file under `RELCERT_NO_STUTTER=1` DECLINES (at the same
values). The positive-stretch part of S: `RELCERT_SYNC=1` declines and some pairing runs at a
positive stretch other than 1; when the cover also has a stutter pairing, the lambda = 1
variant with stretch 0 kept must decline too (SYNC drops the stretch-0 candidate, so a SYNC
decline alone may be the stutter's). The matrix cell M1 (`suite_v2_matrix.py`) counts
stretch-0 pairings as well, and `\numsyncstretch` counts SYNC declines of files that use any
stretch other than 1, stretch 0 included. On the demo: `salt_tank_stutter: S`; the suite file
`lit_nahs25_salt_tank` carries S.
