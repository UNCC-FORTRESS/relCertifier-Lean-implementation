# Scope: the verified checked-cut lift (closing the last tool-side narrowing gap)

## Problem

13 of the 46 certifiable benchmarks certify **only** with the checked-cut channel active
(`RELCERT_NO_CUT=1` ablation, 2026-07-15): arm_chain_rung3, arm_fidelity_high,
plant_fan_high, refinement_ladder_rover rungs 1/3/4, rover_attitude_cone_12dof,
rover_dof_terrain rungs 1/2/3/3_8d, story3_rollover_base_12dof,
story3_rollover_ladder_rung_a.

Their main flow queries are narrowed by guard-derived cuts, so the UNSAT Z3 produced is
for the narrowed query — outside `pair_faModal`'s evolution-domain hypothesis
(`o.domain = domL ∧ domR`). The semantic lift back to the bare-domain obligation exists
(`CutChannel.boxLe_cut_lift`) but has **zero consumers**: nothing re-checks the tool's
O1/O2 fixpoint output, so those 13 certificates currently rest on a documented-but-
undischarged step.

## Key recon findings (route census, instrumented run)

Per kept atom the O2 invariance route is one of:

| family | atoms/mode | route |
|---|---|---|
| arm_chain / arm_fidelity / plant_fan | 1 | DI-strict(B) — boundary `g=0 ⟹ ġ<0` |
| terrain (refinement_ladder, dof_terrain, attitude_cone, rollover) | 2 | DI-nonstrict(A) — whole-domain `ġ≤0` (+ shape/frozen at rung3_6to8) |

**Decisive simplification:** with `RELCERT_CUT_NOMUTUAL=1` (O2 domain = bare evolve, the
other kept atoms dropped), the whole suite still certifies at 45–46/47 — all 13 included.
So the mutual-barrier coupling in O2 is unnecessary in practice, and the hardest Lean
lemma (mutual DI invariance of a barrier conjunction, with real unsoundness corner cases
at joint tangential exits) is **not needed**. Each atom is independently flow-invariant
over the bare evolution domain; the conjunction is invariant trivially.

Both remaining routes already have kernel-checked Lean backing:
* route B → `DLLean.DI_strict` (via `flow_cert_sound_strict`),
* route A → `DLLean.DI_nonstrict_domain` (via `flow_cert_sound`),
* shape/frozen → `contract_stays` (+ a small new `frozen_stays`).

## Plan

**Phase 1 — tool simplification.** Make unconditioned O2 the only mode (delete the
mutual-coupling fold and the `RELCERT_CUT_NOMUTUAL` switch). Audit story1_attdist_rung_a's
query budget (budget-marginal with cut probes; certifies with cuts disabled — either bump
the budget or disable cuts for it).

**Phase 2 — cut-certificate emission (Faithful pattern).** `relcert --emit-cuts`: per
benchmark, per mode/side, the kept atoms as parser-level data `(atom : PForm, route tag)`
into a generated `CutCerts.lean`. Kernel-decidable well-formedness against the BenchIR
literal: each atom is a conjunct of that mode's guard (`cutAtoms` mirror), shape tags
re-checked by the (already pure) `contractShapeOK`, frozen tags by a vars-frozen check.
The O1/O2 *search* stays untrusted; only its final output is certified.

**Phase 3 — per-atom staying lemmas (Lean, ~400–600 lines).**
* `cutAtomG_sound` — the lowered atom formula ≡ `g ≤ 0` (per comparison op; strict
  candidates are already excluded by the tool).
* `atom_boxle_strict` / `atom_boxle_nonstrict` — `z3solve (o2Query …) = unsat` ⟹
  evolve-domain `BoxLe` for the atom, via the existing `flow_cert_sound_strict` /
  `flow_cert_sound`; needs the O2 query restated in Lean literally as printed (printer-
  battery pattern) — deterministic since the O2 domain is now just the evolve lowering.
* `frozen_stays` — an atom over unbound coordinates is constant along the flow.
* `cut_stays` — conjunction of the per-atom facts gives the trace-pointwise staying that
  `boxLe_cut_lift` consumes. Needs run-prefix closure of the ODE semantics (endpoint
  `BoxLe` at every prefix ⟹ pointwise along the trace); add if missing (~80 lines).

**Phase 4 — assembly (~200–300 lines).** `cut_hcert`: valid cut certificate + O2 UNSATs +
UNSAT of the cut-narrowed main query ⟹ the uniform-domain `BoxLe` the `hcert` slot
consumes (`boxLe_cut_lift` instantiated). A `pair_faModal_cut` variant accepting
`o.domain = evolve ∧ cut` closes the tooling statement. Wire into the 13.

**Phase 5 — regression + trust claim.** Printer battery for O2 queries; suite rerun;
ARCHITECTURE/Trusted-README updated: the cut channel moves from "trusted step" to
"z3_unsat_sound leaf only", same as the main queries.

## Out of scope (with reasons)

* **Edge pruning under cuts** (`nonConnPrune`): pruning only *drops* right-automaton
  edges, i.e. restricts the certificate's ∃-side choices — sound unconditionally;
  affects completeness only. Documented, not lifted.
* **Mutual-barrier DI lemma**: obviated by Phase 1 (see recon).
* **Left-side cuts in the ∀-side story**: same lift shape; deferred until a benchmark
  needs it (the 13 need right-side/joint query narrowing only — verify during Phase 4).

## Estimate

Tool work small (Phases 1–2). Lean work ~800–1100 lines (Phases 3–4), no new axioms —
the O2 verdicts enter through the same `z3_unsat_sound` leaf as the main queries.
Risks: run-prefix lemma availability; exact printer identity for O2 queries;
story1_attdist budget flakiness.
