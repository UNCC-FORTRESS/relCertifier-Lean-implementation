# Scope: the clocked right automaton (closing the "unclocked right" gap)

Status: DONE 2026-10-21, branch `clocked-right` (scoped the same day against main = b30d15c;
outcome and deviations in §7). Companion: `docs/PAPER-MAPPING.md` §9 (the row
"`t := 0; {…, t' = 1 & t ≤ ε_R}` on the right", now "exact (cap as post-test)"),
`docs/history/ROTATION-SCOPE.md` on branch `archive/legacy-2026-10` (rotation, a different row). Sections 1 to 6 are the scope
as written before the work; line numbers in them are those of main = b30d15c.

## 1. The gap

The paper's Eq. (1) gives the right system a sampled controller: each cycle is
`t := 0; {x' = f_u(x), t' = 1 & Q_u ∧ t ≤ ε_r}`, so a mode flows for at most one control
period before the guards are re-checked. The Lean right automaton drops the timer:

```
modeStep G mv q m = ?(mv = q) ; {x' = m.sys & m.dom} ; ⋃_{e ∈ edgesFrom q} (?e.guard ; mv := e.tgt)
```
(`Proofs/Encoding/JointBridge.lean:33`, `rightAutomatonBody` at `:40`). One right cycle may flow
arbitrarily long in a mode. The right is the ∃-side, so Lean's "some matching right run exists"
ranges over more runs than Eq. (1) allows: the mechanized Theorem 3 is *weaker* on the right
than the paper's Eq. (10). No certificate is known to exploit it (every witness the chain builds
has cycle duration ≤ ε_R, see §3), but the *statement* does not say so, and the paper's
"Theorem 3 is a Lean theorem over the programs of Eq. (1)" is not literally true today.

## 2. The target

Replace, in the paper's route (the generic bridge), the unclocked body by the clocked one that
already exists in `Proofs/Encoding/ClockedTop.lean:101-115` (retired file, still compiled):

```
modeStepC G mv tr dt q m = ?(mv = q) ; clockedSeg m.sys m.dom tr dt ; ⋃_e (?e.guard ; mv := e.tgt)
clockedSeg sys dom tr dt = tr := 0 ; {x' = sys, tr' = 1 & dom} ; ?(tr ≤ dt)
```
(`clockedSeg` at `BridgeReposition.lean:245`, `clk`/`clkGuard` at `:228-244`.) With `dt := epsR p`
this is Eq. (1)'s right cycle up to the rotation (flow-then-select) and the cap written as a
post-test, which admits exactly the same runs as `& t ≤ ε` from `t = 0` (the left side already
uses this form: `gwindowSeg … tg dt`, `Emitted/Data.lean:177`). The right clock is a fourth
auxiliary coordinate `(Side.Aux, d)`, next to `a` (mode variable), `b` (left clock), `c` (stored
left mode).

Afterwards the remaining differences from Eq. (1) are the rotation (exact, algebraic), one
domain per system (a suite fact, disclosed) and ℕ budgets (a discretization). The paper can keep
its sentence and drop the planned "right flows unclocked" disclosure.

## 3. Why it is feasible: every right flow the chain builds has an explicit duration ≤ ε_R

All right runs of the general chain are built through `rrespP_step hm he hflow hleg hrest`
(`GuardedClimb.lean:116`), whose `hflow : Program.sem (Program.ode m.sys m.dom) ν κ` comes from
exactly four producers:

| producer | site | duration available |
|---|---|---|
| joint step (full span) | `CoverResp.lean:269-298, 331-355` | `T = lam q * δ`, and `hspan : lam q * δ ≤ epsR` is already a hypothesis (`Theorem3General.lean:47`, discharged by `lamOf_span`, `Keyed.lean:257`) |
| joint step (closing) | `coverX_finish`, `CoverResp.lean:174-184` | `T = lam q * (r − a)` with `r − a ≤ δ`, so `T ≤ epsR` by `hspan` |
| reposition cycles | `Progress.lean:295, 312, 365, 379` (`phase`, `phase_down`) | `sem_ode_zero`, or `sem_ode_restrict hHm …` of a solution over `[0, epsR]` from Assumption 1 (duration `t' ≤ epsR` or exactly `epsR`) |
| hops / chosen exits | `CoverResp.lean:373, 390` | zero (`sem_ode_zero`) |

The only hand-written reposition discharge (`InstancesV2/Choice/General/ChargerFastSetpoints.lean:373`)
goes through the generic `repoProgress_one`, so no bespoke run construction exists outside
`Progress.lean`. The response relation itself is a list of `(q, m, e)` segments with a
`bigSeq` of `gseg` runs (`GuardedClimb.lean:88`), turned into a `star (rightAutomatonBody)` run by
`guarded_rights_bridge` (`GuardedSwitch.lean:112`). So the clock enters at one relation and one
bridge, and the four producers supply the bound.

Dressing an unclocked flow with the clock is already proved: `sem_clockedSeg_of_flow`
(`ClockedTop.lean:117`) takes a solution over `[0, dt]` plus the hygiene facts `tr ∉ sys.bound`,
`tr ∉` the right-hand sides, `tr ∉ dom.fv`. It needs the trivial generalization to a solution over
`[0, r]` with `r ≤ dt` (final clock `r ≤ dt` passes `?(tr ≤ dt)`). The hygiene facts are generic:
`grOf_sys_bound` (`Refute.lean:147`) and `aux_ne_Rv`.

## 4. Design: additive below the general chain, in place inside it

* **Keep untouched** `RRespP`, `gseg`, `guarded_rights_bridge`, `modeStep`, `rightAutomatonBody`
  and every theorem of `GuardedClimb`/`GuardedSwitch`/`JointBridge`/`BridgeReposition`/
  `EnvelopeChain*`. The 28 then-kept standalone instances (`InstancesV2/Modal/*`, archived 2026-10-22; "the earlier route,
  kept", `PAPER-MAPPING.md:71`) import `CutRespond`, `GuardedSwitch`, `ModeHandoff` and none of
  `CoverResp`/`Theorem3General` (checked: 0 files), so they keep building.
* **Add** the clocked twins: `gsegC`, `RRespPC`, `rrespP_stepC`/`stopC`/`monoC`
  (`GuardedClimb`), `guarded_rights_bridgeC` → `star (rightAutomatonBodyC G mv tr dt)`
  (`GuardedSwitch`), `sem_clockedSeg_of_flow_le`, and the hygiene lemmas of the clocked body
  (`bv`: `{mv, tr} ∪ Rv`; `fv` adds `tr`; `vars_modeStepC_sub` — a precedent exists for the
  settling model at `FvDischarge.lean:385`).
* **Change in place**, in the general chain only (its consumers are the generated instances):
  `RepoProgress` (`CoverResp.lean:100`) over `RRespPC`; the four producers above; `coverX_piece`,
  `coverX_gresp`, `coverX_finish`, `repoStep` (`CoverResp.lean`), `CoverExtract`,
  `theorem3_of_coverX` (`Theorem3General.lean:178`, right program
  `rightAutomatonBodyC Gr mv tr (epsR)`); `Progress.lean` `phase`/`phase_down`/
  `repoProgress_one`/`_two` produce `RRespPC`.
* **Claims**: `keyedClaim`/`windowClaim` (`Keyed.lean:409`, `Window.lean:49`) and
  `keyedClaimS` (`StrictKeyed.lean:278`) take the clocked body and a fourth index `d` with
  `d ≠ a, b, c`; `theorem3_keyed_of_records` (`Keyed.lean:419`) and the strict/window twins
  gain `d`. The disjointness facts the ∀∃ coupling needs (left program vars
  `Lv ∪ {(Aux,b), (Aux,c)}` vs right program vars, now with `(Aux,d)`) follow from `d ≠ b, c`.
* **Refutations**: `refute_keyed_C/A/B`, `refute_window_B` (`Refute.lean:472, 493`,
  `RefuteFlow.lean:383, 450`) conclude `¬ keyedClaim`. Fewer right runs make the claim harder,
  so `keyedClaimC → keyedClaim` (erase the clock: a run of `clockedSeg sys dom tr dt` restricted
  to the coordinates other than `tr` is a run of `ode sys dom`, since `tr` is in no right-hand
  side or domain — the converse of `sem_clockedSeg_of_flow`) and the 67 refutations transfer by
  contraposition without touching their internals (`t3_elim`, `post_facts`, the rigidity
  analysis stay as they are).
* **Tool side**: nothing. Queries, emission, pins, runners and `paper_numbers.sh` are unchanged;
  `Verdicts` keeps its meaning. `WellFormedRIn`/Assumption 1 is stated over `ODESol … ε` and is
  unchanged.
* **Generators**: `scripts/gen_bridge.py` pads `n` to `max(nvars, 4)` (today 3,
  `gen_bridge.py:246`) and passes `d`; `gen_refute.py` and `gen_strict_demo.py` likewise; the
  52 bridge, 70 refute and strict-demo instances regenerate. Small benchmarks (watertank,
  n = 1) get one more padded coordinate in their `decide +kernel` structural checks.

## 5. Work packages (agent-days; the refutation arc, 6 days scoped, took one wall-clock day
with agents)

| WP | content | days |
|---|---|---|
| W1 | clocked response layer: `gsegC`/`RRespPC`/steps, `guarded_rights_bridgeC`, `sem_clockedSeg_of_flow_le`, clocked hygiene lemmas | 1 |
| W2 | general chain in place: `RepoProgress`, the four producers (`hspan` gives the joint bound), `Progress.lean`, `coverX_*`, `theorem3_of_coverX` with `tr`, `epsR` | 1.5 |
| W3 | claims with `d` (`Keyed`, `Window`, `StrictKeyed`), `theorem3_keyed_of_records` and twins, generator padding, regenerate and build the 52 bridge instances (< 35 s each, `docs/CERTIFICATION-CHECK.md:75-80`) | 1 |
| W4 | `keyedClaimC → keyedClaim` (clock erasure), restate the refutation conclusions, regenerate the 70 refute instances | 1 |
| W5 | `PAPER-MAPPING.md` §9 row → "exact (clocked, cap as post-test)", README recipe, paper §6 sentence | 0.5 |

Total ≈ 5 agent-days; W1 ∥ W4's erasure lemma; W2 → W3 sequential.

## 6. Risks

* **Hygiene side-conditions per site** (`tr ∉ sys.bound`, terms, `dom.fv`): generic from
  `grOf_sys_bound` and `aux_ne_Rv`; if any producer works on a merged state with explicit
  `mergeLR`, the `tr` coordinate must be threaded (`right_sol_merge`, `ReplayEngine.lean:48`,
  is the pattern).
* **Padding** changes the IR dimension of small benchmarks; `decide +kernel` costs grow mildly;
  `nR_eq`/`edges_ok` checks are unaffected.
* **`WatertankStrict`** references the claim three times (strict rows); follows `keyedClaimS`.
* **The semantics of the cap**: `?(tr ≤ dt)` after the flow versus `& tr ≤ dt` inside the
  domain admit the same runs from `tr = 0` (the clock is monotone); state this once in
  `PAPER-MAPPING.md` so the paper's Eq. (1) and the Lean body are read as the same program.

Nothing in `Trusted/` changes; the axiom set stays `propext`, `Classical.choice`, `Quot.sound`,
`z3_unsat_sound`.

## 7. Outcome (2026-10-21, branch `clocked-right`)

Commits, in order:

| commit | WP | content |
|---|---|---|
| `d171b02` | W1 | `Proofs/Encoding/ClockedRight.lean`: `sem_clockedSeg_of_flow_le` (`:90`), `gsegC` (`:207`), `RRespPC` (`:226`) with `rrespPC_stop/_mono/_step`, `guarded_rights_bridgeC` (`:325`) to `star (rightAutomatonBodyC G mv tg dt)`, the hygiene lemmas of the clocked body (`bv_rightAutomatonBodyC`, `vars_bodyCG_sub`, `fv_bodyCG_sub`), and the clock erasure `star_bodyC_to_body` (`:616`). `rightAutomatonBodyC`/`modeStepC` are reused from `ClockedTop.lean:101-112` |
| `aa7ae33` | W2 | the general chain produces clocked right runs: `RepoProgress G tr epsR …` (`CoverResp.lean:145`), `coverX_*`, `Progress.lean` (`phase`, `phase_down`, `repoProgress_*`), `theorem3_of_coverX` (`Theorem3General.lean:181`) over `rightAutomatonBodyC Gr (Aux,a) (Aux,d) epsR`, `CoverHyps … tr …` |
| `44c76da` | W3a | `keyedClaim … a b c d dt` (`Keyed.lean:416`), `windowClaim … a b d dt` (`Window.lean:51`), `keyedClaimS`/`windowClaimS`; `theorem3_keyed_of_records` (`Keyed.lean:427`) and twins with `d ≠ a, b, c`; `Proofs/Encoding/ClockedKeyed.lean` (the clocked mode-keyed assembly: `theorem3_modeKeyed_gen`, `hstepMode_GRC`, `HMode_regionGC`, `sides_disjoint4`) |
| `f05b127` | W3b | `Proofs/Encoding/Emitted/Lift.lean`: `padOK` (`:108`), `odeSol_ext`/`odeSol_proj`, `wellFormedR_lift` (`:292`): Assumption 1 proofs at dimension `n` lift to `n+1` |
| `61d7389` | W3c | `bridgeDimV2 = … + 1` (`RunBridge.lean:73`); `gen_bridge.py` emits `IR (n0+1)` with `pad_ok` and `wellFormedR_lift`; the 52 bridge instances regenerated; `relcert-bridge-verdicts` 4457/4457 |
| `c32bdf3` | W4a | the unclocked claims kept as `keyedClaimU` (`Refute.lean:477`) / `windowClaimU` (`RefuteFlow.lean:320`); `t3_right_mono`, `erase_right_clock`, `keyedClaim_to_unclocked` (`Refute.lean:561`), `windowClaim_to_unclocked` (`RefuteFlow.lean:331`); `refute_keyed_C/A/B_clocked`, `refute_window_B_clocked` conclude the clocked claims by contraposition |
| `b14f129` | W4b | `gen_refute.py` emits every instance at its benchmark's bridge dimension (`RefRec.dim + 1`), with the clock index and `names_ok`/`cuts_ok`; 67 refute instances regenerated; `relcert-refute-verdicts` 67/67, 188/188 |
| `ec29603` | W3d | the Theorem-3 parts of the five `InstancesV2/Choice/General/` exhibits retired (Assumption 1 proofs kept and lifted into their bridge instances); aggregator builds |
| (this commit) | W5 | docs: `PAPER-MAPPING.md` §9 exact, dimensions, lift, refutations, stale equation numbers; `WELLFORMED.md` §6; `VERDICTS.md`, `CERTIFICATION-CHECK.md`, `REFUTATION-*.md`, `README.md` |

Deviations from §2 to §5:

* **Hygiene** is two facts, `tr ∉ range Lv` and `tr ∉ range Rv` (`htrL`, `htrR`,
  `CoverResp.lean:159`), discharged by `aux_notin_range_Lv d` / `aux_notin_range_Rv d`; the
  three per-site facts of §3 (`tr ∉ sys.bound`, the right-hand sides, `dom.fv`) are derived
  from `htrR` once (`CoverResp.lean:208-220`), not threaded per producer.
* **The transfer** `keyedClaim_to_unclocked` needs only `d ≠ a` (plus `namesOK`, `cutsOK`,
  `reg.fv ⊆ range Rv`), not `d ≠ a, b, c`; the top theorems keep all three.
* **`ClockedKeyed.lean` is a separate file** (the clocked twin of `ModeHandoff`'s assembly),
  additive; `ModeHandoff.lean` and the unclocked chain are untouched, as §4 planned.
* **The five general exhibits were retired, not repadded** (§4 planned to regenerate every
  instance): they were hand-written at `Var 2` with no slot for the right clock; their
  Assumption 1 proofs are kept and lifted (`wellFormedR_lift`) into the bridge instances.
  The 28 `InstancesV2/Modal/` standalone instances still stated the unclocked claim (archived on branch `archive/legacy-2026-10`, 2026-10-22).
* **67 refute instances, not 70** (§4, §5 counted 70): the refutation arc landed 67
  (`docs/REFUTATION-RESULTS.md`); all 67 regenerated.
* The strict-demo instance (`scripts/gen_strict_demo.py`) regenerated with the others.
* The paper sentence (W5's third item) is the paper's business; the repository side is done.

Counts unchanged: 4457 bridge groups, 188 refute groups (no query reads the padded coordinate).
Trust base unchanged. Axioms unchanged.
