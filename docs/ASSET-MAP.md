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
| `theorem3_faithful_settling` + `_real` battery | `Proofs/Encoding/ClockedTop.lean`, `Instances/` | the settling presentation (deprecated for new work) |

Standing discipline: before building anything new, check this map; update it when a
top theorem lands. Any tool↔proof mismatch: record in `COVER-AUDIT.md`, resolve BY THE
CODE or surface the tool fix — never invent parallel structures.
