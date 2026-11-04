# Kernel-checked refutations: results

The paper's known-false inputs (Section 6.3, "Known-false inputs."; Appendix B.6, Refutations):
invariant variants of suite benchmarks, each proved in the Lean kernel to admit no
certificate, which relcert must decline. Current state (`docs/refute/results.json`, the
experiment at the paper's state):

1193 mutants over the 50 suite benchmarks, **398 certified, 140 kernel-refuted, 655 open** (one
relcert ERROR, `lit_girard08_robot_m019`, counted open); by operator (certified / refuted /
open) RRO/SNO 40/69/177, MCO 131/23/133, ORO 227/48/345; refuted by kind C 36, B 103, A 1.
Kernel-refuted and certified: none; witness found but not kernel-refuted: none. The 140 come
from 19 benchmarks (the stop-line ladder alone 89: `stopline_drag` 54, `stopline_tyre` 21,
`stopline_friction` 9, `stopline_lag` 5). Decline check of the 140 mutant inputs (default
budget): **140/140 DECLINED** (`docs/refute/decline_default_budget.tsv`); the three negatives
DECLINED. `relcert-refute-verdicts`: **416/416 groups** over the 140 instances.

## The claim

> Of the 1193 Black-Okun-Yesha mutants of the 50 suite benchmarks, **140 are proved false in the
> Lean kernel** (a refutation of Theorem 3's claim for the mutated invariant), 398 are certified
> by relcert, and 655 are open. **relcert certifies none of the 140** (140/140 DECLINED).

The trust base of a refutation is the trust base of a certificate: the parser and lowering
(the instance quotes the parser-emitted IR of the mutant file), the query printer and Z3's
`unsat` answers (`z3_unsat_sound`, discharged by `relcert-refute-verdicts` with a declared
count), and the kernel. The witness finder is untrusted: it only proposes rational witnesses,
which the kernel re-checks.

## What is refuted

For a mutant with per-mode rows, `¬ keyedClaim IR n cX cov ⊤ 0 1 2 3 dt`; with one declared row,
`¬ windowClaim IR n cX cov ⊤ 0 1 2 dt` (the forms of the bridge instances, at the bridge dimension
`n` of the suite benchmark, `reg = ⊤`; the claims are the clocked ones, the right automaton `rightAutomatonBodyC` with the right clock `(Aux, 3)` resp. `(Aux, 2)`, and
`n` is the Assumption 1 lemma's dimension plus one, `RefRec.dim + 1` in
`InstancesV2/Refute/Table.lean`, the rule of `bridgeDimV2`). Each instance proves the refutation

* **for every cover record `cov`**, hence for every pruning: the proofs never use the right
  automaton's edges (kind C does not use the right run at all; kinds A and B bound the right
  run by a monotonicity argument over every mode's flow, and jumps change no coordinate the
  component reads);
* **at the model's cut certificate `cX`** (`Oracle.<bench>_cutsV2X`): the tool computes the
  kept cut atoms from the model alone (`checkedCutX` runs per mode with the mode's guard,
  evolve and field, no invariant input), and every instance proves `same_model`
  (`IR.L = <bench>_IRv2.L ∧ IR.R = <bench>_IRv2.R`, `rfl`). The witness satisfies the stored
  right mode's guard and its kept atoms;
* for every window length `dt ≥ 0` (kinds C, A) or `dt > 0` (kind B).

## Generic theorems (`RelCertifier/Proofs/Encoding/Emitted/`)

| Theorem | Statement (one line) |
|---|---|
| `refute_keyed_C` (`Refute.lean`) | `preOK` (kernel) ∧ no-partner `unsat` per right mode ⟹ `∀ cov, ¬ keyedClaimU … ⊤ … dt`, `dt ≥ 0` (the unclocked claim, right automaton `rightAutomatonBody`) |
| `refute_keyed_A` (`Refute.lean`) | `preOK` ∧ component `k` of the entered row `> 0` (kernel) ∧ rigidity `unsat` per right mode ⟹ same |
| `refute_keyed_B` (`RefuteFlow.lean`) | `preOK` ∧ `bQ` (interior of the left envelope, component `≥ 0`, left Lie derivative `> 0`) ∧ `namesOK` ∧ `cutsOK` ∧ rigidity ⟹ same, `dt > 0` |
| `refute_window_B` (`RefuteFlow.lean`) | `preOKW` ∧ `bQW` ∧ `rowsSame` ∧ `namesOK` ∧ `cutsOK` ∧ rigidity ⟹ `∀ cov, ¬ windowClaimU … ⊤ … dt`, `dt > 0` |
| `keyedClaim_to_unclocked` (`Refute.lean`), `windowClaim_to_unclocked` (`RefuteFlow.lean`) | `namesOK` ∧ `cutsOK` ∧ `reg.fv ⊆ range Rv` ∧ `d ≠ a` ⟹ the clocked claim implies the unclocked one (`t3_right_mono`, `Refute.lean`: Theorem 3's form is monotone in the right program up to a post-condition transport; `erase_right_clock`, `Refute.lean`, by `star_bodyC_to_body`) |
| `refute_keyed_C_clocked`, `refute_keyed_A_clocked` (`Refute.lean`), `refute_keyed_B_clocked` (`RefuteFlow.lean`), `refute_window_B_clocked` (`RefuteFlow.lean`) | the same hypotheses plus `namesOK`, `cutsOK`, `d : Fin n`, `d ≠ a` ⟹ `∀ cov, ¬ keyedClaim … ⊤ a b c d dt` resp. `¬ windowClaim … ⊤ a b d dt`, the clocked claims the bridge instances prove; these are what the generated instances conclude (`gen_refute.py`, `d = 3` keyed, `2` window) |
| `exit_run` (`RefuteExit.lean`) | short-time existence of the polynomial flow inside an open domain, with `G > 0` at the end when `G ≥ 0` and `Lie G > 0` at the start |
| `rigid_star` (`Refute.lean`) | a component no right field decreases on the right envelope never decreases along any run of the right automaton (any pruning) |

`#print axioms` of all four refutation theorems: `propext, Classical.choice, Quot.sound,
RelCertifier.z3_unsat_sound`. No `sorry`, no new axiom, no `native_decide`; witness facts are
`decide +kernel` on exact rationals (`ITerm.evalQ`, `IForm.evalQ_iff`).

Mechanism. The claim is eliminated once at a bi-state (`t3_elim`, `t3_elim'`). The left run is
one step of the left automaton (keyed: `?(u_L = u) ; ?guard_m ; u_L := m ; ?guard_m ; clock := 0 ;
flow_m`; window: the window of `m`), with a zero-duration flow (C, A, `sem_ode_zero`) or a flow
of positive duration `≤ dt` (B, `clocked_exit`). Right runs keep every left coordinate
(`rightStar_keepsL`), so the post-condition's entered row is read at the right end state itself.
Kind B uses the bi-state `(σ, σ')`, `σ'` the right copy carrying the left end values (the
antecedent reads only right coordinates there: `namesOK`, `cutsOK`).

The kinds: **C** no right state pairs with the witness's left values under the entered row
(one closed query per right mode, the left values fixed by equalities); **A** a component of the
entered row is already `> 0` and right-rigid; **B** a component is `≥ 0` on the boundary, the left
flow pushes it out to first order, right-rigid. **D** (projection exit, needs quantifier
elimination) is out of scope.

## Pipeline

1. `scripts/refute_dump.lean`: prints the claim's lowered pieces (guards, envelopes, kept cut
   atoms, row components, left Lie derivatives, the pinned rigidity queries) through the tool's
   own parser and lowering, as SMT-LIB.
2. `scripts/refute_finder.py` (untrusted): the mutants of the mutation enumeration (`scripts/black_mutation.py` on branch `mutation`,
   copied into the finder; labels identical), rational witnesses over exactly the dumped formulas (Z3 models; grid
   models `ℤ/den` when Z3's model is algebraic; quadric repair). Output
   `docs/refute/witnesses.jsonl`.
3. `scripts/gen_refute.py`: per witness, `benchmarks/refute_mutants/<id>/input.txt`, the
   parser-emitted IR (`relcert --emit-ir`) and the witness (`InstancesV2/Refute/Data/<id>.lean`),
   the instance (`InstancesV2/Refute/<Camel>.lean`), the runner table with its declared count.
4. `relcert-refute-verdicts` (`VerdictsV2/RunRefute.lean`): every group `refGroups` builds, the
   exact queries `RefVerdicts` reads, each group at the instance's dimension `RefRec.dim + 1`.
   Run: **416/416 groups unsat** over the 140 instances, against the declared total
   `expectedRefuteGroups` (`InstancesV2/Refute/Table.lean`).
5. `scripts/refute_experiment.py`: relcert on every mutant (this worktree's binary,
   `RELCERT_IMPLIED_CUT=1`; the default verdict includes the handoff check), the table below
   (`docs/refute/results.json`, `docs/refute/relcert.json`).

A mutant counts as kernel-refuted only if its instance builds (`lake build
RelCertifier.InstancesV2.Refute`: all 140 build; `lake build` builds them too) and the runner discharges all its groups.

## Results

`docs/refute/results.json`:

| Operator | Certified | Kernel-refuted | Open | Total |
|---|---|---|---|---|
| RRO/SNO | 40 | 69 | 177 | 286 |
| MCO | 131 | 23 | 133 | 287 |
| ORO | 227 | 48 | 345 | 620 |
| **all** | **398** | **140** | **655** | **1193** |

Kernel-refuted by kind: C 36, B 103, A 1. By operator: RRO/SNO B 45, C 23, A 1; ORO B 41, C 7;
MCO B 17, C 6. **Kernel-refuted and certified: none.** relcert's verdicts on the 1193 mutants:
794 DECLINED, 398 CERTIFIED, 1 ERROR (counted open); every kernel-refuted mutant is DECLINED.

## Not done

* Kind D (projection exit; it needs quantifier elimination).
* The optional `relcert --refute` mode (it would change `Main.lean`); the finder, the generator
  and the runner give the three outcomes outside the tool.

## Reproduce

```
lake build relcert relcert-refute-verdicts
python3 scripts/refute_finder.py --out docs/refute/witnesses.jsonl     # ~1.5 h, untrusted
python3 scripts/gen_refute.py
lake build RelCertifier.InstancesV2.Refute
.lake/build/bin/relcert-refute-verdicts > docs/refute/runner.log
python3 scripts/refute_experiment.py
```

One benchmark only: `python3 scripts/refute_finder.py --only <b>` replaces that benchmark's
records in `docs/refute/witnesses.jsonl` and keeps the others. `gen_refute.py` takes a mutant's
text only from the finder run that found its witness (the record's `sha256` against that run's
scratch file, or the committed `benchmarks/refute_mutants/<id>/input.txt`), checks that it is
mutant `idx` of the current suite file, and otherwise stops with an error before writing
anything. It lists every mutant input it writes and
every file no record produces.
