# Paper ↔ mechanization

How the paper's formal elements map onto the Lean development, for the artifact as it
stands (suite_v2, 45 benchmarks, `RelCertifier/InstancesV2/BatteryV2.lean`). The full
2026-07 inventory of every generic `rvalid (theorem3Form …)` theorem, with the findings of
a complete read of `Proofs/` and the legacy-suite counts of that time, is kept as
`docs/history/PAPER-MAPPING-INVENTORY.md`.

---

## 1. What the paper asks for

The paper states its obligation in the ∀∃ modality over the `cpsProg` programs:

- **Definition 1**: `φInv → [|(L, R)⟩⟩ φInv`
- **Eq. (relational-invariant)**: one-iteration preservation, `φInv → [|(Lsysi, Rsys)⟩⟩ φInv`
- **Eq. (mode-inv)**: the same, decomposed per left mode
- **Theorem 3** (Soundness of Synthesis): an all-successors cover induces a certified
  witness strategy, hence `φInv → [|(L,R)⟩⟩ φInv`

Target Lean shape: `rvalid (theorem3Form L R φ)`, where `theorem3Form`
(`Checker/Cover/Encoding.lean`) is `φ → [|(L*, R*)⟩⟩ φ`, both loop bodies starred, bridged
into dL-rel's relational dL by `RFormula.encoding_correct`.

---

## 2. Theorem 3, generically, from the checker's own decision

Three generic theorems take `decideCovered` (the function the tool runs) plus a Z3-backed
`CoverCert` and conclude `rvalid (theorem3Form …)`; none assumes an emission device.

| theorem | where | left shape |
|---|---|---|
| `decideCovered_implies_theorem3_faithful` | `Proofs/Encoding/BridgeDischarge.lean` | one ODE program; also yields the throughout conjunct |
| `theorem3_uniform_from_covered` | `Proofs/Encoding/CoverExtract.lean` | list of `windowSeg`s; the witness is *derived* from `Covered` (the R1 gate) |
| `theorem3_uniform_guarded` | `Proofs/Encoding/CoverExtract.lean` | guard-gated windows, one per left mode (the R2 gate) |

`decideCovered_implies_theorem3_faithful` records what is load-bearing: `cert` (the flow
certificates at every mode) is required for the `rvalid` conjunct; `hchk`
(`decideCovered`) is load-bearing for the duration-coverage (throughout) conjunct. Axioms:
the standard three, parametric in `cert`; `z3_unsat_sound` enters only where a certificate
is constructed from a verdict (`segPres_from_flowCert`, `flow_certified`). These are
re-emitted on every build by `Instances/AxiomCheck.lean`.

**The per-benchmark instances use the list-invariant chain.** The suite_v2 instances state
Theorem 3 through `theorem3_faithful_multiF_LR` (`EnvelopeChainM.lean`; list-valued
invariants), `theorem3_faithful_multiR_LR` (`EnvelopeChainR.lean`; the same with a
mode-region loop invariant) and `theorem3_modeKeyed` (`ModeHandoff.lean`; §2b), with the
per-window step assembled per benchmark: the certified joint coupling at the cover's λ
(`CutRespond.couple_cutX`, the cut-narrowed stratified pack), right-only prefixes where
the right must first reach a certified mode (`RepoPrefixR.lean`, `WindowRF.lean`), λ
reparametrization (`Reparam.lean`), and existence of the right response (explicit
solutions, or the viability faces of `Proofs/Flow/`). The response strategy and existence
are per benchmark; the cover decision itself is replayed in the kernel for all 45
(`InstancesV2/CoverReplay.lean`).

## 2a. Theorem 3, clause by clause

> **Theorem 3 (Soundness of Synthesis).** For a left mode `m_L`, if every admissible
> initial right mode `q₀` admits an all-successors cover from `(q₀, ε_L, pre-joint)`,
> then the cover induces a certified witness strategy for `m_L`. If such a cover exists
> for every `m_L ∈ modes_L`, then `φInv` is a ∀∃ invariant:
> `φInv → [|(L,R)⟩⟩ φInv`.

Against `theorem3_uniform_from_covered`:

| paper clause | Lean |
|---|---|
| *"every admissible initial right mode `q₀` admits an all-successors cover from `(q₀, ε_L, pre-joint)`"* | `hchk : ∀ q, q < Gj.modes.length → decideCovered Gj fuel ⟨q, B, SrcSetting.preJ⟩ = true`: `q₀ ↔ q`, `ε_L ↔ B` (ℕ-discretized), *pre-joint* `↔ SrcSetting.preJ`, and *all-successors* is `decideCovered`'s successor case `(G.retainedSucc q).all (…)`, i.e. Definition 4 |
| *"the cover induces a certified witness strategy for `m_L`"* | not a hypothesis but the proof: the window response is built from the declared self-edges and the `Covered` derivation (Definition 5) |
| *"if such a cover exists for every `m_L ∈ modes_L`"* | one entry of `leftData` per left mode; the left program is `bigChoice (leftData.map (windowSeg …))` |
| *"`φInv → [|(L,R)⟩⟩ φInv`"* | `rvalid (theorem3Form (bigChoice …) (rightAutomatonBody Gr mv) (ϕinv ∧ mvValidR mv Gr.modes.length))` |

The Lean takes the flow certificates `cert : CoverCert Gj g` as a separate argument; the
paper folds them into the graph construction (§4.2: *"If no flow certificate is available
at `m_R`, none of its candidate edges is retained"*). The Lean also yields a second
conjunct, the invariant *throughout* the co-execution (`CoexecInvThroughout`).

## 2b. Mode-dependent invariants: the composition lemma

> **Theorem 3 (general form).** Let `Φ ≡ ⋀_m (u_L = m → φ_inv(m))`. If (i) for every left
> mode `m_L` every admissible initial right mode admits an all-successors cover at
> `φ_inv(m_L)`, (ii) for every declared left transition `m' → m`,
> `φ_inv(m') ∧ guard_m(x_L) → φ_inv(m)`, and (iii) the well-formedness assumption holds,
> then `Φ → [|(L*, R*)⟩⟩ Φ`.

Mechanized in `Proofs/Encoding/ModeHandoff.lean` as `theorem3_modeKeyed`:

| paper element | Lean |
|---|---|
| the left program with mode variable `u_L`, body `⋃_m ?(m ∈ next(u_L)) ; ?guard_m ; u_L := m ; flow_m` | `leftAutomatonBody A ul`: `?(u_L = m') ; ⋃_{t ∈ next m'} (?guard_t ; u_L := t ; window_t)`, jump-then-flow as the paper writes it. `A : LeftAut n` is built per benchmark from the IR (windows, guards, `next` lists resolved by the handoff runner's own `Handoff.leftModeIndex`), and each instance proves by `decide` that its transition list IS `Handoff.transitions IR` |
| `u_L` | a third auxiliary coordinate `(Aux, 2)` beside `mv = (Aux, 0)` and the clock `tg = (Aux, 1)` |
| `Φ` | `modeKeyedR ul ϕ nL = ⋀_{m < nL} (⌊u_L = m⌋_L → ϕ m)` |
| the loop invariant | `psiK ul ϕ nL domL domR BkR = ((Φ ∧ envLR) ∧ BkR) ∧ ⌊u_L ∈ modes⌋_L`, `BkR` the right bookkeeping (`mvValidR` or `mvRegionR`) |
| **(i)** per-mode cover | `hstepM`, the per-mode step the F- and R-chains consume, from the instance's own provider (`hstepMode_multiF` / `hstepMode_multiR`) |
| **(ii)** the handoff, DOMAIN-CONDITIONED (at a switch the left state ends an `m'` residence and satisfies `guard_m`; the right state is in its evolve domain) | `hhand : ∀ m' < nL, ∀ t ∈ A.succ m', ∀ ω, sat (F m') ω → sat env ω → sat (A.guard t) ω → sat (F t) ω`. Two discharges exist: from Z3 on the runner's query (`handoff_of_unsat`, the `IForm` of `Trusted/Handoff.lean` that `relcert --handoff` and `--run-verdicts-v2` print), or in the kernel. **All twelve mode-keyed instances discharge it in the kernel** (no instance uses `handoff_of_unsat`), so they add no verdict beyond their per-mode packs; the runner's handoff phase is the tool-level check of the same implication |
| **(iii)** well-formedness | the trust-base item (successor-completeness; for all 45 theorems guard-gated switching is kernel-checked on both sides and the response exhibits every switch, §2e); mechanized side conditions: freshness of `u_L` and the footprint disjointnesses (`hd_modeKeyed_G`, `hddF_modeKeyed_G`) |
| the conclusion | `rvalid (theorem3Form (leftAutomatonBody A ul) (rightAutomatonBody G mv) (psiK …))` |

Mode-independent invariants are the special case `F m = F`. All 45 benchmarks are stated
over `leftAutomatonBody`: the 33 mode-independent ones are proved over the choice of their
windows (`bigChoice leftProgs`) and carried to the left automaton by the generic bridge
`theorem3_leftAut_of_choice` (`Proofs/Encoding/LeftAutUniform.lean`): the left automaton only
removes left runs (a declared successor, its guard tested, its window) and adds `u_L`. The
choice form is not always the stronger claim WORTH stating: for
`refinement_ladder_rover_rung2_3to6` and the two story2 ladders the choice of PLAIN windows
(no guard test) is false over the guarded right automaton, while the paper's left program is
proved (`docs/GUARDED-SWITCHING.md` §4.5).

**The twelve mode-keyed benchmarks** (tool handoff: `relcert --handoff`, all transitions
`unsat`; the other 33 benchmarks' handoffs are vacuous, their rows being identical):

| benchmark | theorem | handoff transitions | per-mode packs (queries) |
|---|---|---|---|
| `acc_spoof_limp` | `V2AccSpoofLimp.acc_spoof_limp_modeKeyed` | 3 | 6 (12) |
| `acc_tune_limp` | `V2AccTuneLimp.acc_tune_limp_modeKeyed` | 3 | 6 (12) |
| `platoon_delay_linkloss` | `V2PlatoonDelayLinkloss.platoon_delay_linkloss_modeKeyed` | 7 | 6 (12) |
| `platoon3_linkloss` | `V2Platoon3Linkloss.platoon3_linkloss_modeKeyed` (guarded, on the repaired model: operating-range guards, `docs/SUITE-REDESIGN.md` §20) | 3 | 2 (26) |
| `rover_patrol_zones` | `V2RoverPatrolZonesGuarded.rover_patrol_zones_guarded` (guarded, Z3-free; the `⊤` theorem `rover_patrol_zones_modeKeyed` took 10 packs) | 10 | none |
| `rover_patrol_refine` | `V2RoverPatrolRefineGuarded.rover_patrol_refine_guarded` (guarded, Z3-free; the `⊤` theorem took 10 packs) | 10 | none |
| `sat_detumble_phases` | `V2SatDetumblePhases.sat_detumble_phases_modeKeyed` | 3 | 2 (4) |
| `sat3w_detumble_phases` | `V2Sat3wDetumblePhases.sat3w_detumble_phases_modeKeyed` | 3 | 2 (4) |
| `story3_rollover_ladder_rung_b` | `V2Story3RolloverRungBGuarded.story3_rollover_ladder_rung_b_guarded` | 5 | 9 (21) |
| `rover3tier_rung12` (carried over) | `Rover3tierRung12Guarded.rover3tier_rung12_modeKeyed_guarded` (guarded, Z3-free; the `⊤` theorem `Rover3tierRung12Handoff.rover3tier_rung12_modeKeyed` used the packs `VerdQA`, `VerdQC`) | 4 | none |
| `story1_attdist_rung_a_6to8` (carried over) | `Story1AttdistRungAGuarded.story1_attdist_rung_a_guarded` | 5 | 3 `VerdS` (the STEEP window at its full row) + 6 base `VerdD` |
| `story1_attdist_rung_b_12dof` (carried over) | `Story1AttdistRungBGuarded.story1_attdist_rung_b_guarded` | 5 | 6 `VerdR r m` (`r ≤ m`) |

`rover3tier_rung12`'s ACCEL row was re-stated on 2026-10-08 (rows only) because its
original row failed the handoff; the countermodel is in `docs/HANDOFF.md`.
Every row is guarded at the mode-consistent region (`docs/GUARDED-SWITCHING.md` §6).

## 2c. Checked cuts (closed: both channels are lifted to the kernel)

**What a checked cut is.** For each mode (either side) the tool keeps an atom as a CUT
when two obligations hold:

* **O1 (entry)**: the mode's guard implies the atom, so a guard-gated switch into the mode
  lands inside it;
* **O2 (invariance)**: the atom is forward-invariant along this mode's own field, the
  other side frozen.

The kept atoms of a pairing narrow the domain of every query of that pairing (`andCuts`:
the joint flow queries `checkSeg` and the dynamic reposition queries `checkDynRepo`), never
the model. **The wording for Section 4.2:** *a cut is an atom implied by the mode's guard
and preserved by its own flow.*

**The candidates.** By default (`checkedCut`) the candidates are the closed guard
conjuncts, O1 by membership; O2 by the `shape` route (a contraction `x' = k(c − x)` with
the equilibrium on the safe side, no Z3), `frozen`, or the DI routes (B: boundary,
A: whole domain). With `RELCERT_IMPLIED_CUT=1` (`checkedCutX`,
`Checker/EvolStrengtheningX.lean`) three more kinds are offered and each kept atom records
its kind, its O1 justification, its O2 route and its conditioning atoms:

| kind | candidate | O1 | O2 |
|---|---|---|---|
| `guardConj` | a closed guard conjunct | `membership` | `shape`, `frozen`, DI-B, DI-A |
| `closure` | `x ≤ k` from a strict guard conjunct `x < k` (and symmetrically) | `weakening` | as above |
| `impliedContract` | `x ≤ c` / `x ≥ c` for a field `x' = k (c − x)`, `k > 0` | `rational` (a threshold conjunct at least as tight), else `z3` (`UNSAT(guard ∧ ¬atom)`) | as above |
| `linearForm` | `y + r (x − c) ≤ sup` / `≥ inf` over the guard box, for a recognized critically or over-damped pair `x' = y`, `y' = −a (x − c) − b y` with rational roots | `rational` (interval arithmetic) | `linearShape` (`q' = −(b − r) q`), else DI-B, DI-A, DI-C |
| `derivedBound` | `x ≤ c + K/r` from a kept `q ≤ K` (stratified: conditioned on that atom) | `rational`, else `z3` | `derivedShape`, else DI routes over `evolve ∧ q ≤ K` |

**The lift.** The guard-conjunct channel is lifted by `Proofs/Soundness/CutLift.lean` and
`CutCover.lean`; the widened channel by `Proofs/Soundness/CutLiftX.lean` (one lemma per O1
entry kind, `linQ_rate` and `super_linear_*` for the linear shape, `super_derived_*` for
derived bounds, `stay_given` for the stratification, `check_sound_multi_cutX` for the
threading, and `CutRespond.couple_cutX`, the per-segment form the instances consume). All
45 suite_v2 extended certificates are kernel-checked well formed
(`InstancesV2/Cuts/<b>.lean`, `evolStrengtheningWFX … = true := rfl`), and the 23
instances with verdict packs discharge the kept atoms' O1 through
`cutSatL_of_guard`/`cutSatR_of_guard` on that certificate (the three Z3-free
`arm_plateau_*` instances use no cut). In suite_v2 the checked cuts are load-bearing (`RELCERT_NO_CUT=1` declines)
for 29 benchmarks, the widened kinds for 12 (`RELCERT_NO_IMPLIED_CUT=1` declines) and
the linear-form chain for 8 (`RELCERT_NO_LINEAR_CUT=1` declines); matrix columns M6,
M6+, M6L of `docs/SUITE-REDESIGN.md`.

## 2d. Non-connection certificates: Section 4.3 / Theorem 2

A declared right edge `mR → mSuc` whose successor guard is a single strict threshold
`{g > 0}` is pruned from the cover's all-successors obligation when (source) no entry
state of `mR` satisfies the guard and (barrier) on `g = 0` the right flow of `mR` moves `g`
strictly down.

| paper element | Lean / tool |
|---|---|
| Theorem 2 (the certificate is sound) | `nonconn_sound` (`Checker/NonConn.lean`): dL-lean `DI_strict` on the safe-side term |
| the two checks, as the tool sends them | `Trusted/NonConnQuery.lean` `queries`, the one definition the certifier (`nonConnPrune`), the runner and the kernel bridge share; the source mode's checked cut conjoined to both domains |
| the runner's queries ARE Theorem 2's hypotheses | `Proofs/Encoding/NonConnBridge.lean`: `sourceCheck_iff`, `barrierCheck_iff`, `nonconn_of_unsat` |
| where a pruned edge enters the cover | `retainedSucc` (`Checker/Cover.lean`) drops it; `InstancesV2/CoverReplay.lean` replays `decideCovered` with the emitted `pruned` list |
| where it enters Theorem 3 | the witness never takes a pruned edge; pruned sink modes carry the region `⊥` in the right bookkeeping (`mvRegionR`, `Proofs/Encoding/SinkExtension.lean`) |
| the per-edge instance | `MatchMultiRatePruned.match_multi_rate_nonconn` (Theorem 2 for `match_multi_rate`'s `DRIVE → STALL`), its hypothesis pinned to the suite_v2 runner's rebuilt pair by `VerdictsV2/NonConnPinV2.lean` |
| suite_v2 | 44 pruned edges in the emitted covers, both queries of each re-sent by `--run-verdicts-v2` (88 `unsat`); pruning is load-bearing (`RELCERT_NO_PRUNE=1` declines) for 19 benchmarks (matrix column M4) |

## 2e. Guard-gated switching on the right (closed on branch `guarded-right`)

**The paper.** `cpsProg`'s right loop body is `?(m ∈ next(mv)) ; ?guard_m(x) ; mv := m ;
flow_m`: a switch (and a stay, `m = mv`) is possible only where the entered mode's guard holds.

**The mechanization.** `modeStep` (`Proofs/Encoding/JointBridge.lean`) is the same body up to
rotation, `?(mv = q) ; flow_q ; ⋃_e (?e.guard ; mv := e.tgt)`. Until this branch every graph
the instances built set `e.guard := ⊤` (and the bridge lemmas took `htt : e.guard = ⊤`), so
the theorems were about the declared-successor relaxation of `R`. Now, for all 45
theorems, every edge carries the lowered guard of the mode it enters (`hostGuard vars n
Side.R (mR e.tgt)`, the left guards' lowering; each instance proves it as `Gr_guards`), and the
response is built in the guarded layer (`Proofs/Encoding/GuardedSwitch.lean`):

| paper element | Lean |
|---|---|
| `?guard_m(x)` at a switch | `SwitchLegal e ω := Formula.sat e.guard ω`; the segment `gseg s = flow ; ?s.edge.guard` |
| a right run is a sequence of legal switches | `guarded_rights_bridge` (a run of `bigSeq (segs.map gseg)` is a run of `star (rightAutomatonBody G mv)`) |
| the ∃-response of one round | `GResp G q P post σ` (segments chosen after the left run; the final successor is chosen at the end state); chains of `flow ; legal switch` as `RResp`/`RRespP` (`GuardedClimb.lean`) |
| **mode-consistent states** (Theorem 3's loop invariant on the right) | `mvRegionR mv gregion k` with `gregion q = regionG guard cuts q = guard q ∧ cuts q`: the right satisfies the lowered guard of its current mode `q` and `q`'s checked cuts |
| the loop step | `hstep_assembled_GR`, `hstepMode_GR` with `Hmulti_regionG` / `HMode_regionG` (feed `theorem3_faithful_multiR_LR` and `theorem3_modeKeyed`, unchanged) |
| Assumption 1 (nonblocking / successor-completeness) at a response's end | no hypothesis: every response exhibits its switches and their enabled targets explicitly, or makes no step (the right is then still in its current mode's guard, `gresp_guard`) |
| a zero-duration switch, a reposition's switch | `gresp_hop`, `faModalB_repoPrefixG`, `hopAG` (the switch test after the hop) |
| switching inside a left window (the cover's per-segment demonic successor choice) | the ladder climbs (`LadderRun.climb`, `climbD`) and the synchronized climbs (`syncClimb`, `syncWindow`): the right switches at band floors, legal by the explicit end state |
| footprints without `htt` | `vars_bodyG_sub`, `hddF_multiR_G`, `hddF_multiR_plain_G`, `hd_modeKeyed_G`, `hddF_modeKeyed_G`, `hdis_multi_G` |

**Theorem 3, mode-consistent states.** In the flow-then-jump rotation every loop iteration
ends with a guarded jump into the right's current mode, so at every loop boundary the right
satisfies that mode's guard; the mechanized loop invariant states exactly this
(`guard q ∧ cuts q` of the current mode `q`), uniformly for all 45 benchmarks. **The wording
for the paper's Theorem 3:** *a bi-state is mode-consistent when the right component satisfies
the guard of its current mode and that mode's checked cuts; this is what the flow-then-jump
rotation guarantees at every loop boundary, since the right has just taken a guarded jump into
its mode.*

**Theorem 3, the left side.** The left is the paper's own program, jump then flow
(`leftAutomatonBody`, §2b): a left window is entered only where the entered left mode's
lowered guard holds, and the left's mode variable `u_L` selects the declared successors.
At a loop boundary the left has just FLOWED, so it is not in general in its current mode's
guard; the invariant carries `u_L ∈ modes`, the rows keyed by `u_L` and the left envelope,
and the next window's guard is tested by the program before that window. **The wording for
the paper's Theorem 3 (both sides):** *a bi-state is mode-consistent when the right component
satisfies the guard and checked cuts of its current mode; the left component's mode is a
declared mode and its next window is entered only inside that window's guard. This is what the
two rotations guarantee at every loop boundary: the right has just taken a guarded jump into
its mode (flow, then jump), the left takes its guarded jump before its next flow (jump, then
flow).*

**What the migration found.** At the old invariants (rows, envelopes, kept cuts; no guard) the
statement was false for 23 benchmarks: the invariant admitted right states outside their
mode's guard from which the guarded automaton has no move (history:
`docs/GUARDED-SWITCHING.md` §4.3). With mode-consistent states and the paper's left program
all 45 are proved, 44 for every window length and `rung2c` for every window up to its control
interval (`dt ≤ ε_L = 1`). The earlier "refuted by argument" entries
(`refinement_ladder_rover_rung2_3to6`, the two story2 ladders) refuted only the left form with
no guard test. The earlier kernel-checked refutations of the two `platoon3` benchmarks were
real: their nominal controller BLOCKED after a full cycle (engagement-band stay guards, no
catch-all mode: a violation of Assumption 1 the certificate cannot detect); the benchmarks are
repaired (operating-range guards, `docs/SUITE-REDESIGN.md` §20) and proved. The demonic
all-successors cover (the checker) is unaffected: the gaps were in the existential witnesses,
in the stated invariant's right bookkeeping, and in one benchmark family's model. Record and
per-benchmark table: `docs/GUARDED-SWITCHING.md`.

## 3. The generic theorem families

| family | theorems | status |
|---|---|---|
| cover-based, Emit-free | `decideCovered_implies_theorem3_faithful`, `theorem3_uniform_from_covered`, `theorem3_uniform_guarded` | live (§2) |
| `hstep`-parametric (the instances' route) | `theorem3_faithful`, `theorem3_faithful_multiE_LR`, `_multiF_LR`, `_multiR_LR`, `theorem3_modeKeyed` | live; `hstep` assembled per instance |
| Emit-carrying | `theorem3_faithful_multi_reposition`, `theorem3_uniform_multiflow`, `uniform_multiflow_end_to_end`, the `*_of_emit` forms | superseded by the cover-based family; compiled |
| settling / cadenced | `theorem3_faithful_settling` and its clocked and cadenced variants (`ClockedTop.lean`, `GuardThreaded.lean`) | **retired**: their `GBoxAll` hypothesis is unsatisfiable for relational invariants (stated left-context-free), so the statements are vacuous; kept compiled, do not cite |
| encoding | `theorem3_encoded` / `rvalid_of_encoded_unsat` (`Checker/Cover/Encoding.lean`) | Z3 on the encoded negation ⟹ `rvalid`, via dL-rel's `encoding_correct` |

## 4. Per benchmark

The per-benchmark theorem table (theorem name, file, hypotheses, axioms) for all 45 is in
`docs/CERTIFICATION-CHECK.md`, "Per-benchmark inventory"; the per-benchmark mechanism
evidence is the matrix of `docs/SUITE-REDESIGN.md`.

## 5. Modelling choices to state in the paper

| paper `cpsProg` | mechanized | direction |
|---|---|---|
| left has guards, `u_L`, clock | `leftAutomatonBody` with the lowered left guards, the declared `next` lists and `u_L`, windows clock-capped, for all 45 (§2b; mode-independent instances through `theorem3_leftAut_of_choice`) | exact (jump then flow, as the paper writes it) |
| `?guard_m(x)` on right transitions | `e.guard = hostGuard … (mR e.tgt)` for all 45 | §2e |
| `t := 0; {…, t' = 1 & t ≤ ε_R}` on the right | unclocked in `rightAutomatonBody` | permissive (the ∃-side chooses durations) |
| invariant `φInv` | `φInv ∧ envLR ∧ mvRegionR mv gregion` (mode-consistent states: the current mode's guard and checked cuts) | bookkeeping conjuncts on both sides of the implication; the guard part is what the rotation maintains |
| jump-then-flow (right) | flow-then-jump (`modeStep`) | a rotation (`docs/history/ROTATION-SCOPE.md`) |
| budgets `B = ε_L`, `w = ε_R/λ` (real) | `weight : ℕ`, budget `⌈ε_L/δ_L⌉` | ℕ-discretization |
| resets | identities | matches the paper's Limitations (`docs/history/RESET-MAPS-SCOPE.md`) |
| evolve domains | the instances' Lean statement uses each side's uniform evolve domain; every suite_v2 benchmark declares the same evolve in all modes of a side (the matrix's "domains" column, all "uniform") | per-mode domains (the paper's Eq. 2) are not covered by the Lean lift yet |

## 6. The R-series gates (glossary)

The development was built as an ordered arc, R1 to R7 (record:
`docs/history/ROADMAP.md`). Each removed a way the mechanization could have been weaker
than the paper:

| gate | what it established | Lean artifact | paper element |
|---|---|---|---|
| R1 witness extraction | the witness is derived from the `Covered` derivation, not assumed | `theorem3_uniform_from_covered` | Theorem 3, Definition 5 |
| R2 statement conditioning | the ∀ ranges over exactly the admissible entries the tool certifies | `theorem3_uniform_guarded` | §4.3 admissibility, Eq. (mode-inv) |
| R3 canonical invariant | no per-instance encoding hypotheses | `canonInv`, `encode_canonInv` | Eq. (polynomial-invariant), the dL-rel encoding |
| R4 multi-component invariants | the full conjunction certified by sequential (stratified) differential cuts; mutual narrowing was found unsound and replaced | `StratifiedBarrier.lean`, `CoverCertM` | Definition 2, Theorem 1 |
| R5 emission door | what the tool reports CERTIFIED is what the kernel replays | `--emit-cover`, `InstancesV2/CoverReplay.lean` | the evaluation claim |
| R6 viability | the response flows exist for the needed durations | `Proofs/Flow/BoxViability*`, `StratifiedFaces.lean` | existence side of Definition 5 |
| R7 closure | the documented assumptions match the proofs; the settling chain retired | `Instances/AxiomCheck.lean` | the trust-base claim |
