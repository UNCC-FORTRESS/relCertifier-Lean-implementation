# Verdict report — empirical discharge of theorem hypotheses

## The five checked-cut benchmarks at their declared invariant (2026-10-08, branch `cut-composition`)

`arm_chain_rung3`, `arm_fidelity_high`, `arm_fidelity_mid`, `plant_fan_high` and
`plant_fan_mid` gained a second theorem each, `<name>_declared`
(`Instances/<Name>Declared.lean`): the DECLARED row (`θ_L ≤ θ_R + tol`) with the `Hold`
cut `θ_R ≥ 0.6` carried as `Hold`'s mode region only (`mvRegionR`, `⊤` at the approach
modes), where the base theorem conjoins the cut to the invariant at every mode. The
responses are right-only catch-ups (constant-rate reach of `θ_R = 0.6` in the start mode,
zero-duration hops into `Hold`, endpoint arithmetic), so the theorems carry **no verdict
hypothesis** and audit to the standard three axioms. Nothing changed in the runner: no new
row, pin or coverage constant; the base theorems' `Verd3` packs (rows 3, 4, 6, 14, 16 of
`RunModal.modalTable`, 2 × 2 queries each) and the 12 cut probes of the high trio are
re-run as before. The plain-`mvValid` statement of the declared row is false for these
automata — countermodel and per-benchmark table in `docs/CUT-COMPOSITION.md`; the cut
mechanism in `docs/PAPER-MAPPING.md` §2c.

| benchmark | base theorem (kept) | declared theorem (new) | runner |
|---|---|---|---|
| `arm_chain_rung3` | `arm_chain_rung3_modal`, 2×`Verd3`, region at every mode | `arm_chain_rung3_declared`, std 3, region at `Hold` only | unchanged (4 cut probes + 4 modal queries) |
| `arm_fidelity_high` | `arm_fidelity_high_modal`, 2×`Verd3` | `arm_fidelity_high_declared`, std 3 | unchanged (4 + 4) |
| `plant_fan_high` | `plant_fan_high_modal`, 2×`Verd3` | `plant_fan_high_declared`, std 3 | unchanged (4 + 4) |
| `arm_fidelity_mid` | `arm_fidelity_mid_modal`, 2×`Verd3` (region via route C) | `arm_fidelity_mid_declared`, std 3 | unchanged (4 modal queries; no cut probes) |
| `plant_fan_mid` | `plant_fan_mid_modal`, 2×`Verd3` | `plant_fan_mid_declared`, std 3 | unchanged (4; no cut probes) |

## Cross-mode handoff and the mode-keyed theorems (2026-10-07/08, branch `mode-handoff`)

`--run-verdicts` gained a fourth phase, **handoff**: for every emitted benchmark and every
declared left transition `m' → m` (self-loops included) the domain-conditioned static query
`UNSAT(φ_inv(m') ∧ evolve_{m'}(x_L) ∧ guard_m(x_L) ∧ evolve_R(x_R) ∧ ¬φ_inv(m))` is printed
through `toScript` and sent to Z3 (`Trusted/Handoff.lean`, `Verdicts/RunHandoff.lean`). 215
transitions over the 46 emitted benchmarks; 215 `unsat` (after the `rover3tier_rung12` row
repair of 2026-10-08; with the original rows `ACCEL → COAST` was `sat` and declared in
`Coverage.expectedHandoffFailures`, now empty). Per-benchmark table, the candidate record
and the countermodel of the original rows: `docs/HANDOFF.md`.

The modal phase grew from 483 to 522 queries: rows 42–46 of `RunModal.modalTable` are the
packs of the **mode-keyed** theorems (`Instances/*Handoff.lean`, seven benchmarks, `#print axioms` in
`ModalBattery.lean`), which state each benchmark's DECLARED per-left-mode invariant as a
∀∃ invariant of the full left automaton (`Proofs/Encoding/ModeHandoff.lean`,
`docs/PAPER-MAPPING.md` §2b): the STEEP window of `story1_attdist_rung_a_6to8` and
`story3_rollover_ladder_rung_b` at its full three-component row (3 pairs × 3 = 9 each),
and `story1_attdist_rung_b_12dof`'s three rows with the ceiling head (3×4 + 2×3 + 1×3 =
21). The rover trio's composed theorems are Z3-free. All new packs are pinned
(`ModalPinTable` rows 42–46, `ModalTablePins`, `ModalCodePins`) and counted
(`CoveragePins.derivedModal_eq_expected`, `derivedHandoff_eq_expected`).

Run of 2026-10-08 (this branch, after the conditioned query and the row repair):

```
  [coverage] watertank: 6/6 hypotheses discharged
  [coverage] cut probes: 105/105 hypotheses discharged
  [coverage] modal: 522/522 hypotheses discharged
  [coverage] handoff: 215/215 hypotheses discharged
ALL HYPOTHESES DISCHARGED
```

(The 2026-10-07 run, domain-free query and original rows: 213/213 with the two declared
`rover3tier_rung12` failures.)

---

Last run: `relcert --run-verdicts` on **2026-07-30** — 111 queries, **111 UNSAT, 0
failures**, `ALL HYPOTHESES DISCHARGED` (6 `VerdW` hypotheses of
`watertank_modal_certified` + the per-atom O2 route probes for the 13 cut instances).
Counts unchanged since the 2026-07-19 run (X0: watertank evolve floor x ≥ 0, IR leaf
modularization).

**What the runner does and does not cover** — it discharges the watertank modal pack
(each query tied to the theorem's named query by a kernel identity theorem in
`Verdicts/Watertank.lean`) and the cut probes. The verdict packs of the other 41 modal
instances were each measured through the same printer and Z3 and recorded per instance
below, but do not yet have kernel identity pins; folding them into this runner is the one
open item in the checking story. See `docs/CERTIFICATION-CHECK.md` § Check 3.

Every theorem hypothesis is a fact `z3solve (query) = Verdict.unsat`. `z3solve` is
opaque; operationally it is the tool's printer (`toScript`) plus Z3 — the trust
wording. The kernel guarantees the printed queries ARE the hypothesized ones:

* `Verdicts/Watertank.lean` — per-query identity theorems for the modal gate;
* `Verdicts/GenericPins.lean` — generic pins: the runtime-rebuilt probes (from the
  emitted IR + cut certificates) denote exactly the `getD`-lowered queries the cut
  instances hypothesize, for every benchmark at once.

## Families and their empirical records

| theorem family | hypotheses | record |
|---|---|---|
| modal watertank (`watertank_modal_certified`) | 6 route verdicts; existence PROVEN in-kernel | this runner (below) |
| cut throughout, 13 benchmarks | per-atom O2 route probes | this runner (below) |
| cut throughout, 13 benchmarks | strata/region/dyn cover verdicts | the tool's cover-certification run (kernel-replayed emitted flags, `BenchCoverReplay`); re-run: `relcert benchmarks/suite_uniform/*` |
| throughout, 33 cut-free | cover verdicts | same certification run |
| settling, 46 | flow/cut verdicts | settling-arc certification + printer battery |
| bounded viability (S3 census) | face tags | `BenchViability2.lean` (`--emit-viability2`, 1121/1121 faces) |

## Runner output (111 UNSAT, 0 failures)

```
== watertank_modal_certified : 6 VerdW hypotheses ==
  UNSAT (route B)  watertank window Low  / right Low 
  UNSAT (route B)  watertank window Low  / right Mid 
  UNSAT (route B)  watertank window Mid  / right Mid 
  UNSAT (route B)  watertank window High / right Low 
  UNSAT (route B)  watertank window High / right Mid 
  UNSAT (route B)  watertank window High / right High
== cut instances : per-atom O2 route probes ==
  UNSAT [B(strict)]  arm_chain_rung3 R/ApproachA
  UNSAT [B(strict)]  arm_chain_rung3 R/ApproachB
  UNSAT [B(strict)]  arm_chain_rung3 R/ApproachC
  UNSAT [A(frozen)]  arm_chain_rung3 R/Hold
  UNSAT [B(strict)]  arm_fidelity_high R/ApproachA
  UNSAT [B(strict)]  arm_fidelity_high R/ApproachB
  UNSAT [B(strict)]  arm_fidelity_high R/ApproachC
  UNSAT [A(frozen)]  arm_fidelity_high R/Hold
  UNSAT [B(strict)]  plant_fan_high R/ApproachA
  UNSAT [B(strict)]  plant_fan_high R/ApproachB
  UNSAT [B(strict)]  plant_fan_high R/ApproachC
  UNSAT [A(frozen)]  plant_fan_high R/Hold
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung1_2to3 L/STEEP
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung1_2to3 L/MODER
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung1_2to3 L/FLAT
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung1_2to3 R/STEEP
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung1_2to3 R/STEEP
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung1_2to3 R/MODER
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung1_2to3 R/MODER
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung1_2to3 R/FLAT
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung1_2to3 R/FLAT
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung3_6to8 L/STEEP
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung3_6to8 L/STEEP
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung3_6to8 L/MODER
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung3_6to8 L/MODER
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung3_6to8 L/FLAT
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung3_6to8 L/FLAT
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung3_6to8 R/STEEP
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung3_6to8 R/STEEP
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung3_6to8 R/MODER
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung3_6to8 R/MODER
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung3_6to8 R/FLAT
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung3_6to8 R/FLAT
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung4_8to12 L/STEEP
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung4_8to12 L/MODER
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung4_8to12 L/FLAT
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung4_8to12 R/STEEP
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung4_8to12 R/STEEP
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung4_8to12 R/MODER
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung4_8to12 R/MODER
  UNSAT [A(nonstrict)]  refinement_ladder_rover_rung4_8to12 R/FLAT
  UNSAT [C(superlevel)]  refinement_ladder_rover_rung4_8to12 R/FLAT
  UNSAT [A(nonstrict)]  rover_attitude_cone_12dof L/STEEP
  UNSAT [A(nonstrict)]  rover_attitude_cone_12dof L/MODER
  UNSAT [A(nonstrict)]  rover_attitude_cone_12dof L/FLAT
  UNSAT [A(nonstrict)]  rover_attitude_cone_12dof R/STEEP
  UNSAT [C(superlevel)]  rover_attitude_cone_12dof R/STEEP
  UNSAT [A(nonstrict)]  rover_attitude_cone_12dof R/MODER
  UNSAT [C(superlevel)]  rover_attitude_cone_12dof R/MODER
  UNSAT [A(nonstrict)]  rover_attitude_cone_12dof R/FLAT
  UNSAT [C(superlevel)]  rover_attitude_cone_12dof R/FLAT
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung1 L/STEEP
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung1 L/MODER
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung1 L/FLAT
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung1 R/STEEP
  UNSAT [C(superlevel)]  rover_dof_terrain_rung1 R/STEEP
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung1 R/MODER
  UNSAT [C(superlevel)]  rover_dof_terrain_rung1 R/MODER
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung1 R/FLAT
  UNSAT [C(superlevel)]  rover_dof_terrain_rung1 R/FLAT
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung2 L/STEEP
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung2 L/MODER
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung2 L/FLAT
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung2 R/STEEP
  UNSAT [C(superlevel)]  rover_dof_terrain_rung2 R/STEEP
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung2 R/MODER
  UNSAT [C(superlevel)]  rover_dof_terrain_rung2 R/MODER
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung2 R/FLAT
  UNSAT [C(superlevel)]  rover_dof_terrain_rung2 R/FLAT
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3_8d L/STEEP
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3_8d L/MODER
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3_8d L/FLAT
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3_8d R/STEEP
  UNSAT [C(superlevel)]  rover_dof_terrain_rung3_8d R/STEEP
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3_8d R/MODER
  UNSAT [C(superlevel)]  rover_dof_terrain_rung3_8d R/MODER
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3_8d R/FLAT
  UNSAT [C(superlevel)]  rover_dof_terrain_rung3_8d R/FLAT
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3 L/STEEP
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3 L/MODER
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3 L/FLAT
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3 R/STEEP
  UNSAT [C(superlevel)]  rover_dof_terrain_rung3 R/STEEP
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3 R/MODER
  UNSAT [C(superlevel)]  rover_dof_terrain_rung3 R/MODER
  UNSAT [A(nonstrict)]  rover_dof_terrain_rung3 R/FLAT
  UNSAT [C(superlevel)]  rover_dof_terrain_rung3 R/FLAT
  UNSAT [A(nonstrict)]  story3_rollover_base_12dof L/STEEP
  UNSAT [A(nonstrict)]  story3_rollover_base_12dof L/MODER
  UNSAT [A(nonstrict)]  story3_rollover_base_12dof L/FLAT
  UNSAT [A(nonstrict)]  story3_rollover_base_12dof R/STEEP
  UNSAT [C(superlevel)]  story3_rollover_base_12dof R/STEEP
  UNSAT [A(nonstrict)]  story3_rollover_base_12dof R/MODER
  UNSAT [C(superlevel)]  story3_rollover_base_12dof R/MODER
  UNSAT [A(nonstrict)]  story3_rollover_base_12dof R/FLAT
  UNSAT [C(superlevel)]  story3_rollover_base_12dof R/FLAT
  UNSAT [A(nonstrict)]  story3_rollover_ladder_rung_a L/STEEP
  UNSAT [A(nonstrict)]  story3_rollover_ladder_rung_a L/MODER
  UNSAT [A(nonstrict)]  story3_rollover_ladder_rung_a L/FLAT
  UNSAT [A(nonstrict)]  story3_rollover_ladder_rung_a R/STEEP
  UNSAT [C(superlevel)]  story3_rollover_ladder_rung_a R/STEEP
  UNSAT [A(nonstrict)]  story3_rollover_ladder_rung_a R/MODER
  UNSAT [C(superlevel)]  story3_rollover_ladder_rung_a R/MODER
  UNSAT [A(nonstrict)]  story3_rollover_ladder_rung_a R/FLAT
  UNSAT [C(superlevel)]  story3_rollover_ladder_rung_a R/FLAT
ALL HYPOTHESES DISCHARGED
```

**Every hypothesis of every theorem is discharged**: proven in-kernel, observed unsat
by this runner, or recorded by the tool's own certification runs. The only standing
assumptions are the frozen contract's: parser, printer, Z3-on-unsat, Lean kernel, and
successor-completeness with guard-gated switching.


---

> **SUPERSEDED — historical snapshot.** The section below counts seventeen modal
> instances. The arc closed on 2026-07-30 with all 46; the current inventory is the
> FULL SUITE section at the end of this file and the per-benchmark table in
> `docs/CERTIFICATION-CHECK.md`.

## Modal Theorem-3 instance residuals (T3 arc, 2026-07-29)

Seventeen benchmarks carry `rvalid (theorem3Form …)` modal instances. Every
theorem's Z3 residual is a hypothesis of the stated theorem (never assumed
internally); the table records the residual inventory and the empirical check.

| instance | residual verdicts | empirical record |
|---|---|---|
| arm_chain_rung3 / arm_fidelity_high / plant_fan_high (clones) | 2 route packs each | cover-certified queries (emitted covers) |
| arm_fidelity_mid / plant_fan_mid (clone) | 2 route packs each | cover-certified queries |
| rover_drag | 1 route pack | cover-certified query |
| robot_braking | 2 route packs | cover-certified queries |
| rover_4d_box | 2 route packs | cover-certified queries |
| match_multi_eps / rover3tier_M1 (clone) | 2 route packs each | cover-certified queries |
| refinement_ladder_rover_rung2c_6dof | 3 stratified-DC packs (9 queries each) | semantic mirrors 27/27 unsat (route C for the 8 lockstep conjuncts with strata stacking, route A for the region face) |
| arm_fidelity_low / arm_refinement / plant_fan_low (clones) | 2 route packs each | route-A mirrors unsat (`dg/dt = v_L − 1 ≤ 0` domain-wide) |
| arm_chain_rung1 | 3 route packs | route-A mirrors unsat (`dg/dt = rL − λ/5` = 0, 0, −2/5) |
| arm_chain_rung2 | 4 route packs | route-A mirrors unsat (`dg/dt = rL − 0.3λ` < 0 all four) |
| watertank | 6 `VerdW` packs | `--run-verdicts` battery (kernel-identity IR mirrors) |

Existence residuals: **zero** across all seventeen — every `HExistSegB` /
split-phase witness is discharged in-kernel (stratified faces, closed-form
drift, or explicit linear curves). The dt-capped switch instances
(`dt ≤ 1/5`) state the cap as a hypothesis.

The five switch instances and rung2c use hand-stated `z3solve` Props (the
same `flowQuery`/`strataDomHost` families the cover emits); folding them
into the `--run-verdicts` kernel-identity battery is routine follow-up work,
not a soundness gap — the theorems' hypotheses are explicit either way.


---

## The composite tier and the cover-row λ (2026-07-30)

Five λ ≠ 1 instances were generated, elaborated green, and then **withdrawn**:
`rover_attitude_cone_12dof`, `story3_rollover_base_12dof`,
`story3_rollover_ladder_rung_a`, `refinement_ladder_rover_rung3_6to8`,
`endurance_orderlift_1to2`.

Their residual Props were stated at the **cover row's λ**. Semantic mirrors of
the shared velocity conjunct are **satisfiable** there for most (window, mode)
pairs — take `v_L = v_R = 0.8`, where `g = v_L − v_R = 0` and
`ġ = 3(c − v) − λ·3(c − v) > 0` whenever `λ > 1` and `v > c`. All three routes
(nonstrict, strict-boundary, superlevel) die on that witness. The same query
family at λ = 1 is unsat on all six climb pairs (6/6), which is what every
landed plain-tier instance uses.

A theorem conditioned on a false hypothesis is vacuous, so those five were
removed rather than left in the tree looking green.

**What has to be settled first.** `CoverEmit.ModeFlagsE` is documented as
carrying flags "at the emitted λ", and the tool re-certifies these benchmarks
end to end, so one of the following is true and has not yet been determined:

* the emitted row λ is the settling/ε stretch, and the joint flow certificates
  were discharged at some other (per-pair) λ found by the search; or
* the flags' provenance needs an audit of the same kind as
  [`COVER-AUDIT.md`](COVER-AUDIT.md).

The query **domain** is not the issue: `Run.flowQueryIR` is confirmed to use
the evolve domains only (no guards), which is exactly what the generated Props
use. The gap is the λ.

Until the per-pair certified λ is read out of the checker rather than inferred
from the cover row, no λ ≠ 1 instance can state an honest residual. The
generator machinery for that tier is kept and is independent of this question
(`scripts/gen_multif_lambda_k.py`).


---

## Resolution: all five withdrawn instances re-landed (2026-07-30)

The λ-provenance question is settled and every withdrawn benchmark carries a
(correct) modal Theorem 3 again:

* The cover row's λ **is** the flow-certificate λ. The withdrawn Props failed
  because the tool's queries conjoin per-mode **checked cuts**
  (`RELCERT_NO_CUT=1` turns `rover_attitude_cone_12dof` into DECLINED — the
  cuts are load-bearing). For the terrain-family composites the right cuts
  are the shape-route contraction ceilings `v_R ≤ c_m`.
* No cut-free λ exists for those benchmarks (velocity conjunct forces λ = 1,
  position conjunct forces λ ≈ 1.65+), so the honest modal statement is
  **region-conditioned**: the L4 chain (`mvRegionR`) with regions := the cut
  ceilings, region face first in the strata order, climb-to-max dispatch,
  and existence through the stratA affine **upper** face (the ceiling is an
  equilibrium of the contraction). Landed: `rover_attitude_cone_12dof`,
  `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a`,
  `refinement_ladder_rover_rung3_6to8`.
* `endurance_orderlift_1to2` was withdrawn by mistake: the blanket mirror
  tested a conjunct (`v_L ≤ v_R`) this benchmark does not have. Its real
  invariant's Lie derivative is state-constant and true on all used pairs;
  the file was re-landed byte-identical.

Also landed since: `endurance_gain_M1`, `rover_terrain_M1` (combined
functionals at λ = 1, climb dispatch), `match_multi_rate` (per-window λ
∈ {3,2,1,1} against the single drive mode, symbolic-λ analytic layer).

Suite (snapshot, superseded — the final count is 46/46): **36/46** benchmarks carry modal Theorem 3 (attitude_rate, rung4_8to12, and orderlift_2to3 landed after this note; the last via the L1d monotone-face pass in AffineFaces2.lean). Remaining blockers are
catalogued per benchmark in the working notes: an L1d existence-consumer
variant (affine-on-affine chaining) for `endurance_orderlift_2to3`,
`attitude_rate`, `refinement_ladder_rover_rung4_8to12`; the per-mode-invariant
device for the story1/rollover-b/rover3tier group; and the three specials
(closed-form witness, no cover, smt2 invariants).


---

## Modal Theorem 3 — FULL SUITE (2026-07-30, final close)

> **Hypothesis-truth audit, 2026-07-31.** Separately from the axiom audit, every
> `Verd` hypothesis was checked for *truth* (a false hypothesis makes a theorem
> vacuous, which `#print axioms` cannot see). Six were false; all six are repaired.
> Five of the repairs add the landing mode's guard as a region conjunct, so those
> five theorems are now conditioned on it — see the README's *Conditioning* note
> and [`VERDICT-EVIDENCE-AUDIT.md`](VERDICT-EVIDENCE-AUDIT.md) Part II.

> **Verified end to end 2026-07-31 on `1bcee57`**: `lake build` 8987
> jobs exit 0; `relcert-test` ALL PASS; `--run-verdicts` 594/594 `unsat`; axiom
> audit 47 theorems = 42 with `z3_unsat_sound` + 5 with the standard three alone,
> no `sorryAx`, no `native_decide`. Recipe and costs:
> [`CERTIFICATION-CHECK.md`](CERTIFICATION-CHECK.md).

**46 of 46 certified benchmarks carry `rvalid (theorem3Form …)`.** The six
listed as out-of-scope in the marathon-close note above all landed the same
day, each through a new response-structure device (new leaf modules only —
no verified-chain theorem was modified):

* `rover3tier_rung12` — **per-left-mode theorems** (`…_ACCEL`, `…_COAST` in
  `Rover3tierRung12Modal.lean`): `theorem3Form`'s invariant is a parameter,
  so each left window family gets the modal theorem at its own declared
  invariant (λ = 2 / λ = 1 respectively). Cross-mode handoff is not claimed,
  and is not claimed by the tool's per-mode certificates either.
* `rover3_M1`, `rover_coupled`, `rover_position` — **catch-up** (the
  `WindowGrowth.lean` leaf): `faModal`'s response runs AFTER the left window,
  so it can be pure right-only flow. The right evolve domain's velocity floor
  (`v_x ≥ 1/4`) means zero-duration hops to Safe plus ONE hold of `8·dt`
  regain more position than `windowSeg_growth`'s `2·dt` ceiling on the left
  window; the weakest declared tolerance (`Stop`, offset 2 — the modes'
  invariants nest) is re-established by endpoint arithmetic. No pumping, no
  mode switching at value-dependent times, no Picard machinery.
* `refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof`
  — **combined-coordinate catch-up**: the declared tolerance bounds
  `g₂ = s + v/3`, whose Lie along the right's FLAT hold is EXACTLY `0.65`
  (the asymptotic `v`-row cancels: `ṡ + v̇/3 = v + (0.65 − v)`). An explicit
  exponential witness flow gains `0.65·τ` in `g₂` precisely, while
  `lie_two_coord` + `windowSeg_growth` cap any left window at `0.65·(2·dt)`;
  `τ = 2·dt` closes the invariant with zero slack. The reposition
  certificates the tool uses are thereby bypassed, not mechanized: the modal
  theorem holds without them.

**Five of the six are Z3-free** — `rover3_M1`, `rover_coupled`,
`rover_position`, `refinement_ladder_rover_rung2_6dof`,
`refinement_ladder_rover_rung2b_6dof`: `#print axioms` on each is exactly
`[propext, Classical.choice, Quot.sound]`, with no `z3_unsat_sound` and no
verdict hypotheses in the statement. `rover3tier_rung12` is **not** in that
set: its two per-left-mode theorems carry the usual route verdicts
(`VerdQA`/`VerdQC`, two each) and audit to the standard three plus
`z3_unsat_sound`. (An earlier revision of this section said "all six" — that
was wrong; the audit in `Instances/ModalBattery.lean` is the authority.)

Files: `Rover3tierRung12Modal.lean`, `Rover3M1Modal.lean`,
`RoverCoupledModal.lean`, `RoverPositionModal.lean`,
`RoverRung26dofModal.lean`, `RoverRung2b6dofModal.lean`; the shared leaf is
`Proofs/Encoding/WindowGrowth.lean` (`clk_wellFormed`, `windowSeg_growth`,
`windowSeg_mask`, `windowSeg_end_domL`). The whole-suite audit and the
per-benchmark inventory live in `docs/CERTIFICATION-CHECK.md`.

`shield_unreachable` stays the 47th benchmark: the tool itself reports an
inconclusive Z3 verdict, so it is outside the certified suite entirely.

### Superseded note (2026-07-30 morning, kept for the record)

The marathon-close snapshot earlier the same day read "40 of 46" and
classified the six above as out of scope (reposition-reliant / pump-then-hold
/ per-mode-shape). The classifications were accurate about the TOOL's
certificate structure; the modal statements nevertheless hold through the
response-structure arguments above, which need nothing from the retired
cadenced chain.

Landed in the closing stretch before those six: `rover_tier_r1` (the
closed-form polynomial witness — the first instance whose existence has no
Picard machinery), `story3_rollover_ladder_rung_b`,
`story1_attdist_rung_a_6to8`, `story1_attdist_rung_b_12dof` (the nested
per-mode group, certified at their COMMON declared invariant — the modes'
invariants nest, so the shared row is the honest modal loop invariant).
