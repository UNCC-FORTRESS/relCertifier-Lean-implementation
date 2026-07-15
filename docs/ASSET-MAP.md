# Asset map: what is already built (check BEFORE building anything)

Maintained to stop re-derivation. Update when a top theorem lands or retires.

## The modal chain (Proofs/Encoding) — top consumers first

| theorem | file | shape |
|---|---|---|
| `theorem3_uniform_multiflow` | UniformMultiflow | k-piece clocked windows per left mode (`bigChoice`), per-window `∃ Gj, CoverCert ∧ RightProjAlignV`, `EmitWindows` (ASSUMED — to be replaced) |
| `theorem3_faithful_multi_reposition` | RepositionEndToEnd | left = flow mode + frozen-reposition mode interleaved in one star; Hmulti dispatches per mode: `Hmulti_from_cover` (joint) / `Hmulti_from_cover_dyn` (dynamic reposition, fL=0) |
| `decideCovered_implies_theorem3_faithful_multi` | RepositionEndToEnd | decideCovered + CoverCert + RightProjAlign + `EmitSegs` (ASSUMED) → `rvalid(theorem3Form) ∧ CoexecInvThroughout` |
| `decideCovered_implies_theorem3_faithful` | BridgeDischarge | single-flow prototype; same conjunction |
| `rvalid_from_cert` | BridgeDischarge | honest finding: `decideCovered` is NOT load-bearing for the `rvalid` conjunct — per-mode certificates are; the budget walk gates CERTIFIED (search completeness), the modal proof needs `cert` only |
| `check_sound` | Checker/Checker | decideCovered + CoverCert → `CoexecInvThroughout` (RightReach ∀∃-throughout) |
| `Covered`, `decideCovered_sound` | Checker/Cover, Checker | Definition 4 + σ-matched repositions, verified checker the tool itself runs |

Coupling layer (all live): `segment_faModalB_from_cert`, `dynreposition_faModalB_from_cert`,
`Hmulti_window`, `multiseg_clocked`, `faModalB_clockedSeg_iff`, `plantT_split_iter`,
`hstep_single_multi'`/`hstep_assembled_multi'`, `faModal_bigChoiceL`, `relational_loop_multi`.

Dischargers (all live): `UniformFvDischarge` (hd/hddF + `uniform_multiflow_end_to_end`),
`LoweringSide` (side-splits from IR + `namesFree`, `invToG_pipeline_LR` premise-free),
`FvDischarge` (cadenced chain + lowering no-aux), `CutLift` (checked-cut narrowing).

Instances: settling battery 46/46 `_real` (cadenced chain); `rover_drag_multiflow`
(UniformPilot — EmitWindows-based, to be re-based on the extraction).

## The remaining REAL gaps (frozen hypothesis contract: docs/… + memory)

1. **Witness extraction** `emit_from_covered`: from the `Covered` derivation
   (via `decideCovered_sound`) produce the response segment chains that `EmitSegs` /
   `EmitWindows` currently assume. Induction on `Covered`; joint cases yield pieces,
   reposition cases yield frozen-left segments. This replaces the last ASSUMED device.
2. **Admissible-start conditioning + full left family**: statement quantifies over the
   code's admissible entries (`guardL ∧ guardR ∧ inv` SAT), `mv = q0`, σ = preJ; left =
   all modes' windows with `test(guardL)` at entry.
3. **Emission door** (`--emit-cover`, EmitIR pattern) + battery instantiation.
4. **Viability query family** (per evolve-box face forward-invariance) + generic Picard
   lemma — discharges the continuous existence obligation per the frozen contract.

## Fidelity finding (code ↔ proof, surfaced by the extraction design)

The tool's `retainedSucc` = `q :: declared-non-pruned` — the self-loop is IMPLICIT
(staying never needs a declared edge). The mechanized `modeStep`/`rightAutomatonBody`
requires a DECLARED edge after every flow segment. Benchmarks declare self-loops in
`next`, so the suite is unaffected — but a model without a declared self-loop would be
coverable by the tool and not representable as a mechanized response. Resolve during
extraction: either the automaton gains an implicit stay (matches code), or the tool
requires declared self-loops (matches proof). Decide by the code, flag to the user.

## Statement-fidelity note (settled)

`theorem3Form`'s postcondition is `inv ∧ mvValid` — the ∀∃ invariant-preservation
property. Duration alignment (ε-tiling, budget) is the WITNESS STRATEGY, not statement
content; hence `rvalid_from_cert`'s finding that the budget is not load-bearing for
`rvalid`. The budget arithmetic remains load-bearing for the tool's CERTIFIED gate and
for constructing the matched-duration witnesses.
