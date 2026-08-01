# Asset map — the load-bearing theorems

Where each guarantee lives, and what it rests on. (Historic entries retired to
`Archive/`; see git history for the arc-by-arc account.)

| asset | file | role |
|---|---|---|
| **the modal battery (46 benchmarks / 47 theorems)** | `Instances/ModalBattery.lean` | **the headline asset**: imports every benchmark's `rvalid (theorem3Form …)` instance and re-emits its axiom audit on every build. Reproduction recipe: `docs/CERTIFICATION-CHECK.md` |
| `watertank_modal_certified` | `Instances/WatertankViability.lean` | the modal flagship: Theorem 3 with proven existence; six named verdicts, each pinned to the runner's printed query |
| `rover3_M1_modal`, `rover_coupled_modal`, `rover_position_modal`, `rung2_6dof_modal`, `rung2b_6dof_modal` | `Instances/*Modal.lean` | the five **Z3-free** instances — standard three axioms, no verdict hypotheses; right-only responses closed by endpoint arithmetic |
| `theorem3_faithful_multiE_LR` | `Proofs/Encoding/EnvelopeChain.lean` | the multi-mode modal top theorem (envelope loop invariant, LR split) |
| `theorem3_faithful_multiF_LR` | `Proofs/Encoding/EnvelopeChainM.lean` | L6: the same for **list-valued** invariants (19 multi-component benchmarks) |
| `theorem3_faithful_multiR_LR` | `Proofs/Encoding/EnvelopeChainR.lean` | L4: the same with a mode-region loop invariant (`rung2c`, `rung4`, story1-b) |
| `Hmulti_window1_prefixed` | `Proofs/Encoding/EnvelopeChain.lean` | reposition-opened one-piece windows |
| `Hmulti_windowR_prefixed` / `Hmulti_windowRF_prefixed` | `Proofs/Encoding/RepoPrefixR.lean`, `WindowRF.lean` | L2: right-only hop prefixes with **derived** disjointness — what unblocked k > 1 windows |
| `windowSeg_growth` / `windowSeg_mask` / `windowSeg_end_domL` / `clk_wellFormed` | `Proofs/Encoding/WindowGrowth.lean` | the catch-up device: bounds how far a left window can move a quantity, and carries the right state through it. Behind all five Z3-free instances |
| `faModal_ODE_split_bounded` | `Proofs/Encoding/SplitCoupling.lean` | L3: intra-window mode switching (the five `dt ≤ 1/5` switch instances) |
| `sem_rightBlock_reparam{,_iff}` | `Proofs/Encoding/Reparam.lean` | L7: λ-stretched right runs ≡ λ = 1 runs (23 benchmarks state at the real automaton) |
| `HExistSegB_of_viability_strat{ified,A,A2}` | `Proofs/Flow/StratifiedFaces.lean`, `AffineFaces{,2}.lean` | L1/L1c/L1d: existence from stratified, affine-equilibrium, and monotone faces — the routes that make existence Z3-free |
| `check_sound_multi` | `Proofs/Encoding/CoverMulti.lean` | throughput invariant, cut-free (33 instances) |
| `check_sound_multi_cut` / `pres_multi_cut` | `Proofs/Soundness/CutCover.lean` | the guard-threaded cut lift (13 instances) |
| `segment_faModalB_from_certB` | `Proofs/Flow/ViabilityWiring.lean` | the bounded coupling on the honest existence residual |
| `HExistSegB_of_viability` | `Proofs/Flow/ViabilityWiring.lean` | existence from face verdicts + budgets (chained Picard) |
| `WellFormedFlowB_contract` (+`_transfer`) | `Proofs/Soundness/UniformEvol.lean`, `Proofs/Flow/FaceBridge.lean` | existence for contract fields, outright |
| `box_viability_bounded_chain` | `Proofs/Flow/BoxViabilityBounded.lean` | any-duration budget-telescoped viability |
| `flow_certified` + route B/C | `Trusted/Oracle.lean`, `Core/FlowCert.lean` | verdict → invariance (the axiom's single consumer chain) |
| `decideCovered_sound` | `Checker/Checker.lean` | kernel-replayed cover decisions |
| generic pins (`hostDyn_pin`, …, `o2_probe_pin`) | `Verdicts/GenericPins.lean` | printed queries = hypothesized queries |
| modal pins (`pin_*`, 42) | `Verdicts/ModalPinTable.lean` | each modal theorem's `Verd…` **is** the query the runner rebuilds |
| table ties (`ties_*`, 42) | `Verdicts/ModalTablePins.lean` | the runner's `RunInfo` row, incl. its mode pairs via `modalPairs` — corrupting a field fails the build |
| `*_real` battery (46) | `Instances/RealInstances.lean` | right-system well-formedness at the real scale — the paper's nonblocking/successor-complete assumption, **discharged**. Live and non-vacuous (`decideWellFormed`'s `bandOrdered` makes `realGdOf` satisfiable) |
| ⚠️ `theorem3_faithful_settling` + clocked/cadenced variants, `settling_end_to_end` | `Proofs/Soundness/GuardThreaded.lean`, `Proofs/Encoding/ClockedTop.lean`, `FvDischarge.lean` | **VACUOUS for relational invariants** — all require `GBoxAll` (quarantined, unsatisfiable for an `L`-mentioning `g`); the unclocked form also carries `hbudgetAll`. Historical presentation only. See `PAPER-MAPPING.md` §3b |
| ⚠️ `theorem3_faithful_landing_clocked{,_wf,_uniform}` | `Proofs/Flow/MultisegLandingBridge.lean`, `Proofs/Soundness/UniformEvol.lean` | carry `hbudgetAll` — "unsatisfiable for autonomous benchmarks unless the caller smuggles a clock into `domL`". Historical |
| `theorem3_uniform_from_covered` / `_guarded` | `Proofs/Encoding/CoverExtract.lean` | the R1/R2 gates: Theorem 3 from the checker's own decision, **Emit-free** |
| `decideCovered_implies_theorem3_faithful` | `Proofs/Encoding/BridgeDischarge.lean` | Theorem 3 + throughout, from `decideCovered` + `CoverCert` |

Standing discipline: before building anything new, check this map; update it when a
top theorem lands. (This map went un-updated through most of the T3 arc — the entries
above were reconciled against the tree on 2026-07-30.) Any tool↔proof mismatch: record in `COVER-AUDIT.md`, resolve BY THE
CODE or surface the tool fix — never invent parallel structures.
