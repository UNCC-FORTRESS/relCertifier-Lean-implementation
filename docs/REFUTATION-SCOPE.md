# Kernel-checked refutations: scope (branch `refutation`)

## The question

The paper reports certified benchmarks, plus the few the tool declines. A decline means only
"no certificate found". To claim that relCertifier *rejects soundly*, every rejected input
needs ground truth at the same trust level as a certificate. In particular, a mutant counted
as "correctly rejected" must be provably false, not just declined or refuted by an
unverified script.

## The claim this enables

> Of N mutants, K are proved false in the Lean kernel (a refutation of Theorem 3's claim for
> the mutated invariant), C are certified, and the rest are open. relCertifier certifies none
> of the K.

The trust base is the same as for certification: parser and lowering, the query printer,
Z3's `unsat` answers, and the kernel. The witness *finder* (today
`scripts/black_mutation.py`) needs no trust at all, because the kernel checks every
refutation.

## What is refuted

The certified claim (`windowClaim` / `keyedClaim`, `Emitted/Window.lean`, `Emitted/Keyed.lean`)
is `theorem3Form L* R* ψ`. Here ψ is the row, the envelope `domL ∧ domR`, and
`mvRegionR (regionG guardR cutsR)`, which is the stored right mode's guard plus the right
cuts. The right automaton is the PRUNED graph `grOf p n (prunedOf cov)`.

Note (2026-10-21, branch `clocked-right`): since the right automaton of the bridge is clocked
(`rightAutomatonBodyC`, right clock `(Aux, d)`; `docs/PAPER-MAPPING.md` §9), the refuted claim
is the clocked `keyedClaim … a b c d dt` / `windowClaim … a b d dt` at the benchmark's bridge
dimension. The arguments below are unchanged: they are stated against the unclocked claims
`keyedClaimU` / `windowClaimU` (the pre-clock forms, `Refute.lean:477`, `RefuteFlow.lean:320`),
and `keyedClaim_to_unclocked` / `windowClaim_to_unclocked` (`Refute.lean:561`,
`RefuteFlow.lean:331`: fewer right runs make the claim harder; the clock is erased by
`star_bodyC_to_body`) transfer each refutation by contraposition. Same 67 variants, same 188
groups.

The refutation target is the same claim with:

- **No pruning** (`cov` with no pruned edges). Pruning only removes right runs, so the pruned
  claim implies the unpruned one. A refutation of the unpruned claim therefore refutes
  every claim any certificate could state. This is what makes a refutation mean "no
  certificate can exist".
- **The model's real cut certificate `cX`.** The cuts are computed from the model and do
  not depend on the invariant (`--emit-cuts`). They make the antecedent stronger, so the
  witness must satisfy them. The finder must add the cuts to its antecedent query; today's
  script does not, so its witnesses must be regenerated.

## Refutation kinds (counts from the mutation run, 72 refuted)

| Kind | Count | Left run | Why every right run fails | Lean needed |
|---|---|---|---|---|
| C: no partner | 11 | switch to `m`, flow 0 (`sem_ode_zero`) | no right state satisfies ψ_m at the witness's left state: one Z3 `unsat` on a closed query | generic theorem + pin |
| A: atom broken, rigid | 18 | switch, flow 0 | the atom fails now, and every right flow keeps it failing (Lie sign over each right mode's domain; switches do not reset) | + right-monotonicity lemma over `R*` |
| B: atom pushed out, rigid | 41 | switch, flow δ > 0 | the left flow pushes the atom out (first order), then as in A | + short-time flow existence (`PicardBridge`) and first-order exit |
| D: projection exit | 2 | flow δ | relies on Z3 quantifier elimination | out of scope (QE is not certified) |

## Pieces

1. **Generic theorems.** `refute_window_C` / `refute_keyed_C`: from
   (i) a witness state satisfying ψ and the guard of a successor mode `m`, checked by
   `norm_num`/`decide` on rational literals in the generated file, and (ii) a `Verd` on the
   no-partner query, conclude `¬ windowClaim …`. Then `refute_*_A` with the
   right-monotonicity lemma, then `refute_*_B`.
2. **Pin layer.** The no-partner query and the rigidity queries are pinned to the exact
   strings the runner sends (the existing pin pattern).
3. **Finder → instance generator.** The finder adds the cuts, regenerates witnesses with
   exact rationals, and emits a Lean instance per refuted mutant (the `gen_bridge` pattern).
   A runner discharges the instance's queries with declared counts.
4. **Experiment.** Rerun the mutation set. A mutant counts as refuted only if its instance
   builds. Report certified / kernel-refuted / open per operator. relCertifier must decline
   every kernel-refuted mutant.
5. **Optional tool feature.** `relcert --refute` runs the finder itself and prints REFUTED
   with an instance, so the tool has three outcomes: certified, refuted, declined.

## Risks

- **Mode-keyed indexing.** The mode-variable and stored-mode encoding (`modeKeyedR`,
  `ulValidL`, `mvRegionR`) must be met exactly by the witness. This is mechanical but fiddly.
- **Cuts change witnesses.** Some of today's 72 may become unrefutable with cuts. Those are
  then reported as open.
- **Kind B is the bulk (41).** Its short-time flow argument is the only new analysis.
  Kinds C and A alone give 29 refutations.

## Effort

| Work | Agent-days |
|---|---|
| C, end to end, with generator and a first batch | 2–3 |
| A | +1 |
| B | +2 |
| Tool feature (optional) | +1 |

Nothing existing changes. It is all new files, as with strict atoms.
