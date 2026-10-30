# Stutter: stretch 0 on joint segments (the right waits)

Branch `stutter`, 2026-10-29, from `benchmark-fixes` at `de241c5` (not rebased; `benchmark-fixes`
has moved on since). Scope record: the λ = 0 scoping of 2026-10-29 (probe files under
`tmp/lam0-scope/` of the main checkout, not committed).

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
  long as the left holds a level it can match. A reader who wants "the reference keeps time"
  keeps the key off (or `λ_min > 0`).

## Opt-in

`[problem] stutter = true` (default `false`; any value other than `true`/`false` is a parse
error; `KeyAudit` recognizes the key). With the key, `Run.lambdaCandidates` appends `λ = 0` as the
**last** candidate, after `ε_R/ε_L` and the 21-point grid on `[λ_min, λ_max]`, so a file that
closes at some `λ > 0` keeps that cover. `λ = 0` is never taken from the grid: without the key a
file with `λ_min ≤ 0` never tries 0. `RELCERT_SYNC=1` (λ = 1 only) drops it.

**Guard.** `certifyWithData` turns a cover with a stretch-0 pairing into ERROR unless the problem
has `stutter = true` (and any window stretch `≤ 0` into ERROR always). Before this branch,
`lambda_min = 0` reached an unbacked CERTIFIED (no suite file did this).

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
| `Proofs/Encoding/Emitted/Data.lean` | `timeOK`: `0 < lamN ∨ p.stutter` (stretch 0 only under the key) |
| `Proofs/Encoding/Emitted/Anchor.lean`, `Keyed.lean`, `StrictAnchor.lean`, `StrictKeyed.lean` | `timeOK_at` yields `0 ≤ lam`; `lam_pos` to `lam_nonneg`, `lamOf_pos` to `lamOf_nonneg`; `stayR_dom`, `barriers_keep` at `0 ≤ c` |
| `Trusted/Parse.lean`, `KeyAudit.lean`, `EmitIR.lean` | `PProblem.stutter : Bool := false`, the key, printed only when true |
| `Trusted/Run.lean`, `OracleAPI.lean` | `lambdaCandidates … stutter`, `windowOf`, the window stretch separate from the pairing's in the λ loop, the per-pairing fallback and the choice path; the guard |

## Tests

`scripts/stutter_tests.py` (variant files in a temporary directory, `RELCERT_IMPLIED_CUT=1`):

91/91 as expected (measured 2026-10-29):

| case | verdict |
|---|---|
| `benchmarks/stutter_demo/salt_tank_stutter` (the suite salt tank with the key), band `c` in {0, 0.5, 1, 2, 2.99, 3} | CERTIFIED (all) |
| band 0 without the key | DECLINED |
| band 3 / 2.99 without the key | CERTIFIED / DECLINED (the suite file's tight value 3) |
| band -0.01 with the key | DECLINED (the rows admit no start) |
| band 0, `λ_min = 0`, no key (the guard) | DECLINED (before the key this certified unbacked) |
| `λ ∈ [0, 0]` with the key | DECLINED (the attacked On moves, the frozen right cannot follow) |
| the attacked Off drifting (`xp' = 0.1`), band 0, with the key | DECLINED |
| the 75 `refute_mutants` and 3 `negative` files with the key | 78/78 DECLINED |

So the salt tank's tight band is **0 with the key** (3 without). The demo's cover: On_L at
`λ = 1` (budget 1); Off_L window `lamQ = 1 = ε_R/ε_L`, budget 1, both pairings `lamN = 0`
(`RELCERT_DEBUG`: `[Off_L λ=1] On=fail`, `[Off_L λ=0] On=pass Off=pass`). It declines under
`RELCERT_SYNC=1` and certifies under `RELCERT_NO_CHOICE`, `RELCERT_NO_PRUNE`, `RELCERT_NO_REPO`.

Kernel: `scripts/gen_stutter_demo.py` emits the demo's leaves and the bridge instance
`InstancesV2/Bridge/SaltTankStutter.lean` (window form, Assumption 1 transported from the suite
salt tank); `lake env lean scripts/stutter_demo_verdicts.lean` discharges its query groups.

Measured: the instance kernel-checks (`lake build RelCertifier.InstancesV2.Bridge.SaltTankStutter`,
no `sorry`); `stutter_on` (`IR.stutter = true`) and `uses_stutter` (a pairing with `lamN = 0`)
are decided in the kernel; `[stutter demo] 54/54 groups, ALL DISCHARGED`. So
`salt_tank_stutter_bridge_run` gives Theorem 3 at band 0 end to end; its axioms are
`[propext, Classical.choice, Quot.sound, RelCertifier.z3_unsat_sound]`, as every bridge instance.

Regression (key off, no input changed), the de241c5 binary against this branch's, both with
`RELCERT_IMPLIED_CUT=1`: the `--emit-cover` output of the 50 suite_v2 files and the 2 choice
exhibits byte-identical (52/52); the verdict lines (time stripped) of the suite under the control
run, `RELCERT_SYNC`, `RELCERT_NO_CHOICE`, `RELCERT_NO_PRUNE`, `RELCERT_NO_REPO`, `RELCERT_NO_CUT`,
`RELCERT_NO_PAIR_STRETCH` and of the exhibits (off, on, sync on) identical; `--check-quick-v2`
output identical (50 certified, modal 1162/1162, `SUITE_V2 QUICK CHECKS PASSED`). Lean, rebuilt:
`relcert-test` ALL PASS (50 IR literals match their files); bridge 7437/7437, refute 206/206,
progress 194/194; `WellFormedBattery` 66 lines at the three standard axioms (plus the 11 replayed
`CutLiftX` lines), `AxiomCheck` 9 (6 standard, 3 plus `z3_unsat_sound`), no `sorryAx`. The
rebuild after the change took about 11 min wall on 12 cores (two passes, 7m51s and 2m54s).

## Letters

Stutter has its own mechanism letter **W** (the witness waits), the dual of **R** (right-only
segments, in which the left waits). `scripts/suite_v2_letters.py` credits W when some cover has
a stretch-0 pairing (`lamN = 0`) and the file without `stutter = true` DECLINES (at the same
values: a file that certifies only with a looser value without the key declines at its own).
S stays the positive-stretch letter: a stretch-0 pairing alone does not credit S (S needs a
pairing at a positive stretch other than 1; covers without stutter pairings keep the old S rule
exactly). The matrix (`suite_v2_matrix.py`) is unchanged; its M1 cell counts positive stretches
only. Measured on the demo (matrix and letters run over `benchmarks/stutter_demo`):
`salt_tank_stutter: W`, `TOTALS S=0 … W=1`. No suite_v2 file sets the key, so every suite
letter is unchanged; `letters.json` gains the key `W` (false everywhere) and the total `W 0`.
