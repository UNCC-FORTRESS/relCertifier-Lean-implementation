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
| **(iii)** well-formedness | the trust-base item (successor-completeness with guard-gated switching); mechanized side conditions: freshness of `u_L` and the footprint disjointnesses (`hd_modeKeyed`, `hddF_modeKeyed`) |
| the conclusion | `rvalid (theorem3Form (leftAutomatonBody A ul) (rightAutomatonBody G mv) (psiK …))` |

Mode-independent invariants are the special case `F m = F`; the 33 mode-independent
suite_v2 instances keep the `bigChoice leftProgs` left form, which over-approximates the
left automaton and so is the stronger claim (the left is ∀-quantified).

**The twelve mode-keyed benchmarks** (tool handoff: `relcert --handoff`, all transitions
`unsat`; the other 33 benchmarks' handoffs are vacuous, their rows being identical):

| benchmark | theorem | handoff transitions | per-mode packs (queries) |
|---|---|---|---|
| `acc_spoof_limp` | `V2AccSpoofLimp.acc_spoof_limp_modeKeyed` | 3 | 6 (12) |
| `acc_tune_limp` | `V2AccTuneLimp.acc_tune_limp_modeKeyed` | 3 | 6 (12) |
| `platoon_delay_linkloss` | `V2PlatoonDelayLinkloss.platoon_delay_linkloss_modeKeyed` | 7 | 6 (12) |
| `platoon3_linkloss` | `V2Platoon3Linkloss.platoon3_linkloss_modeKeyed` | 3 | 2 (26) |
| `rover_patrol_zones` | `V2RoverPatrolZones.rover_patrol_zones_modeKeyed` | 10 | 10 (20) |
| `rover_patrol_refine` | `V2RoverPatrolRefine.rover_patrol_refine_modeKeyed` | 10 | 10 (20) |
| `sat_detumble_phases` | `V2SatDetumblePhases.sat_detumble_phases_modeKeyed` | 3 | 2 (4) |
| `sat3w_detumble_phases` | `V2Sat3wDetumblePhases.sat3w_detumble_phases_modeKeyed` | 3 | 2 (4) |
| `story3_rollover_ladder_rung_b` | `V2Story3RolloverRungB.story3_rollover_ladder_rung_b_modeKeyed` | 5 | 9 (21) |
| `rover3tier_rung12` (carried over) | `Rover3tierRung12Handoff.rover3tier_rung12_modeKeyed` | 4 | the two per-left-mode packs `VerdQA`, `VerdQC` of `Rover3tierRung12Modal` |
| `story1_attdist_rung_a_6to8` (carried over) | `Story1AttdistRungAHandoff.story1_attdist_rung_a_modeKeyed` | 5 | 3 `VerdS` (the STEEP window at its full row) + 6 base `VerdD` |
| `story1_attdist_rung_b_12dof` (carried over) | `Story1AttdistRungBHandoff.story1_attdist_rung_b_modeKeyed` | 5 | 6 `VerdR r m` (`r ≤ m`) |

`rover3tier_rung12`'s ACCEL row was re-stated on 2026-10-08 (rows only) because its
original row failed the handoff; the countermodel is in `docs/HANDOFF.md`.

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

## 2e. The right automaton's ⊤ edge guards

**The certifier's two step kinds.** The cover (`Checker/Cover.lean`, `Covered`) uses two
kinds of right step: the **joint segment** (both systems flow, the right time-stretched by
λ; `Covered.step`) and the **dynamic right-only reposition** (`checkDynRepo`,
`Covered.stepRepositionDynPre/Post`, `RightReach.repositionDynPre/Post`; Lean:
`dynreposition_faModal`, `BridgeReposition.lean`): the right flows under its own field for
a full interval while the left is held, the invariant kept by the whole-domain flow
certificate (route A over the frozen-left field). The dynamic reposition is the paper's
**right-only segment**. The certificate has no zero-duration right switch (a static
reposition existed until 2026-10-09 and was removed because nothing checked that the
successor's guard held at its switch instant; record in `docs/history/COVER-AUDIT.md`).

**The ⊤-model.** Every right automaton the instances build sets `e.guard := ⊤` (the
chain theorems take this as a hypothesis, `htt`, proved per instance or by the instance a
mode-keyed theorem reuses), whereas the paper's `cpsProg` tests
`?guard_m(x)` on each transition. For the two step kinds above this abstraction is
justified under the paper's Assumption 1: every mode change the certificate makes follows
a joint segment or a full-interval right-only flow, and after either the cover demands
that **every** declared, unpruned successor covers (`retainedSucc … .all`), so whichever
successor the guarded automaton actually enables is among those certified; Assumption 1
(nonblocking) supplies that some enabled successor exists. The guard is not discarded: it
does its work in the certificate, as the source of the cut atoms (O1) and of the
non-connection pruning.

**Scope of that argument in the instances.** The argument is about the certificate's step
kinds. The kernel witnesses of the instances are built over the `⊤`-guarded automaton, and
several response constructions include zero-duration right runs followed by a switch
(`static_hop_existsR` in `RepoPrefixR.lean`, or a local `static_hop*` lemma): 19 of the 24
legacy instance modules under `Instances/` (written before the static-reposition removal)
and 10 of the 26 suite_v2 instances (`Watertank`, `ChargerFastSetpoints`,
`ChargerFastTapers`, `PlatoonDelayProfiles`, `Platoon3Profiles`, `QuadLightAirframe20`,
`QuadLightLag`, `QuadLightProfiles`, `RoverPatrolZones`, `RoverPatrolRefine`). Whether each
such switch happens at a state where the successor's guard holds is not checked by the
kernel (the guards are `⊤`) and is not argued in this document; it is an open point about
those instance witnesses, separate from the certificate's step kinds.

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
| left has guards, `u_L`, clock | mode-independent instances: `bigChoice leftProgs` (left flattened, windows clock-capped); mode-keyed instances: `leftAutomatonBody` with guards and `u_L` (§2b) | the flattened left over-approximates the ∀-side, so it is the stronger claim |
| `?guard_m(x)` on right transitions | `e.guard = ⊤` | §2e |
| `t := 0; {…, t' = 1 & t ≤ ε_R}` on the right | unclocked in `rightAutomatonBody` | permissive (the ∃-side chooses durations) |
| invariant `φInv` | `φInv ∧ envLR ∧` right bookkeeping (`mvValidR` or `mvRegionR`) | bookkeeping conjuncts on both sides of the implication |
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
