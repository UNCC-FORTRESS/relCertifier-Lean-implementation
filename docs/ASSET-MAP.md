# Asset map — the load-bearing theorems

Where each guarantee lives, and what it rests on. (Historic entries retired to
`Archive/`; see git history for the arc-by-arc account.)

| asset | file | role |
|---|---|---|
| `watertank_modal_certified` | `Instances/WatertankViability.lean` | the modal flagship: Theorem 3 with proven existence; six named verdicts remain |
| `theorem3_faithful_multiE_LR` | `Proofs/Encoding/EnvelopeChain.lean` | the multi-mode modal top theorem (envelope loop invariant, LR split) |
| `Hmulti_window1_prefixed` | `Proofs/Encoding/EnvelopeChain.lean` | reposition-opened one-piece windows |
| `check_sound_multi` | `Proofs/Encoding/CoverMulti.lean` | throughput invariant, cut-free (33 instances) |
| `check_sound_multi_cut` / `pres_multi_cut` | `Proofs/Soundness/CutCover.lean` | the guard-threaded cut lift (13 instances) |
| `segment_faModalB_from_certB` | `Proofs/Flow/ViabilityWiring.lean` | the bounded coupling on the honest existence residual |
| `HExistSegB_of_viability` | `Proofs/Flow/ViabilityWiring.lean` | existence from face verdicts + budgets (chained Picard) |
| `WellFormedFlowB_contract` (+`_transfer`) | `Proofs/Soundness/UniformEvol.lean`, `Proofs/Flow/FaceBridge.lean` | existence for contract fields, outright |
| `box_viability_bounded_chain` | `Proofs/Flow/BoxViabilityBounded.lean` | any-duration budget-telescoped viability |
| `flow_certified` + route B/C | `Trusted/Oracle.lean`, `Core/FlowCert.lean` | verdict → invariance (the axiom's single consumer chain) |
| `decideCovered_sound` | `Checker/Checker.lean` | kernel-replayed cover decisions |
| generic pins (`hostDyn_pin`, …, `o2_probe_pin`) | `Verdicts/GenericPins.lean` | printed queries = hypothesized queries |
| `*_real` battery (46) | `Instances/RealInstances.lean` | right-system well-formedness at the real scale — the paper's nonblocking/successor-complete assumption, **discharged**. Live and non-vacuous (`decideWellFormed`'s `bandOrdered` makes `realGdOf` satisfiable) |
| ⚠️ `theorem3_faithful_settling` + clocked/cadenced variants, `settling_end_to_end` | `Proofs/Soundness/GuardThreaded.lean`, `Proofs/Encoding/ClockedTop.lean`, `FvDischarge.lean` | **VACUOUS for relational invariants** — all require `GBoxAll` (quarantined, unsatisfiable for an `L`-mentioning `g`); the unclocked form also carries `hbudgetAll`. Historical presentation only. See `PAPER-MAPPING.md` §3b |
| ⚠️ `theorem3_faithful_landing_clocked{,_wf,_uniform}` | `Proofs/Flow/MultisegLandingBridge.lean`, `Proofs/Soundness/UniformEvol.lean` | carry `hbudgetAll` — "unsatisfiable for autonomous benchmarks unless the caller smuggles a clock into `domL`". Historical |
| `theorem3_uniform_from_covered` / `_guarded` | `Proofs/Encoding/CoverExtract.lean` | the R1/R2 gates: Theorem 3 from the checker's own decision, **Emit-free** |
| `decideCovered_implies_theorem3_faithful` | `Proofs/Encoding/BridgeDischarge.lean` | Theorem 3 + throughout, from `decideCovered` + `CoverCert` |

Standing discipline: before building anything new, check this map; update it when a
top theorem lands. Any tool↔proof mismatch: record in `COVER-AUDIT.md`, resolve BY THE
CODE or surface the tool fix — never invent parallel structures.
