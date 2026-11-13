# The SOS oracle (`RELCERT_SOS_SECS`)

Branch `hyp-slicing`, phase 2 of the option-2 plan. A second, mechanized oracle for the flow
queries: when Z3 answers `unknown` on a level of a row's query (`docs/HYP-SLICING.md`), a
sum-of-squares (Putinar) certificate is searched numerically and then checked EXACTLY over the
rationals against the printed query; the oracle answers `unsat` only on the exact checker's
VERIFIED. Its soundness is one axiom beside Z3's, `sos_unsat_sound`, which enters the proof of
an instance only when that instance's records carry an SOS verdict. With the knob unset the
tool, the runners, the printed queries and the axiom audit are byte-identical to today's.

## Semantics

`RELCERT_SOS_SECS=S` (seconds, a natural number; unset = never called). For every joint flow
query (`OracleAPI.checkSeg`) and every right-only flow query (`OracleAPI.checkDynRepo`), at
every escalation level of the row's domain and for every route of that level, in the tool's
order: Z3 first (`Z3Session.check`, its `:timeout` and `:rlimit`); on `unknown` the level's
printed script is written to a file and `scripts/sos_oracle.py QUERY S` is run
(`Trusted/Sos.lean`, `oracleCheck`):

* `SOS unsat …` (the exact checker printed VERIFIED): the route is `unsat`, the component is
  certified at this level, the oracle tag is `sos`;
* `SOS rejected …` (a numerical certificate was found but did not check exactly), `SOS
  unknown …` (no certificate within the budget, the basis cap, or a solver failure), any other
  exit: the route stays `unknown` and the escalation continues exactly as without the knob.

`sat` from Z3 is never given to the SOS oracle (a `sat` on a sliced level escalates, on the full
level it is a FAIL, as before). A Z3 `error` or an over-long script is not given to it either.
The SOS call is not counted against the query budget (`RELCERT_MAX_QUERIES`); the time budget
is checked before each route as before, and the call itself is bounded by `S` (the solver's
time limit plus a hard alarm in the script). Not called: the mode-fact, stay, non-connection,
admissibility, handoff, progress and coverage queries (`checkedCutX`, `probeUnsat`, …), which
are Z3's alone. dReal is not called anywhere in the tool (the probe's proxy `z3sos.py` called it;
the tool never did), so the hook sits directly after Z3.

The log, on stderr, one line per SOS call (knob set only), after the slice lines of the level:

```
[sos secs=120 level=hop 0 1/3] joint comp#37 BRAKE->BRAKE λ=1: sos unsat cvars=8 qvars=15 hyps=27 basis0=45 maxres=1.15e-10 minpivot=9.00e-08 t=5.7s
[sos secs=120 level=full 2/2] right-only comp#4 STRAIGHT->TURN pre=true: sos unknown vars=20 basis=231 t=120.3s
[sos secs=120 level=hop 1 2/3] joint comp#12 TURN->TURN λ=1: sos rejected s0 Gram not PSD after absorbing the residual (max |residual| 2.27e+00): negative pivot -3.768e-06 at 8 t=9.1s
```

(the level as in the slice lines; the status `unsat` = verified exactly, `rejected`, `unknown`
or `error`; the certificate's variable count `cvars`, the query's `qvars`, the hypothesis count,
the size of the `s₀` basis, the largest rounding residual before absorption and the smallest
LDLᵀ pivot of `s₀` after it; the wall time of the call).

Environment: `RELCERT_PYTHON` (default `python3`; cvxpy, clarabel, z3, sympy, numpy and scipy
must import; `/Users/jxiang1/Develop/python3env/bin/python3` here), `RELCERT_SOS_SCRIPT`
(default `scripts/sos_oracle.py`, relative to the cwd), `RELCERT_SOS_MAXBASIS` (the `s₀` basis
cap, default 600 monomials, above it the call is `unknown` at once), `RELCERT_SOS_DEG` (the
relaxation degree, default `max(4, deg(ġ) rounded up to even)`), `RELCERT_SOS_DIR` /
`RELCERT_SOS_KEEP` (where the query files go, whether they are kept), `RELCERT_SOS_CERT_DIR`
(keep every verified certificate as `<query>.cert.json`).

## The prover (`scripts/sos_prove.py`, numerical evidence only)

The probe's program (`sos_query.py`, `sos_phase1.py`), on the tool's own printed level query
and without further slicing: the atoms are parsed with Z3's parser into exact rational
polynomials; the goal is the last conjunct (`ġ > 0` on routes A and C, `ġ ≥ 0` on route B
behind the boundary atom `g = 0`); the hypotheses are every other atom. The variables kept are
those of the goal and of the coupled (multi-variable) atoms; each one bounded on both sides by
single-variable atoms is rescaled to `[-1, 1]` (`x = c + w·y`, exact rationals), the others
shifted to their one bound or left alone. The SDP (cvxpy, Clarabel, `time_limit = S`) is

```
-ġ(y) - ε  =  s₀(y) + Σᵢ sᵢ(y)·hᵢ(y) + Σⱼ qⱼ(y)·eⱼ(y)
```

with `hᵢ` the coupled inequality atoms, the box products `(x - lo)(hi - x)` of the two-sided
variables and the single one-sided atoms, `eⱼ` the equality atoms, `sᵢ = bᵢᵀ Gᵢ bᵢ` Gram forms
over the monomial bases of degree `(D - deg hᵢ)/2`, `qⱼ` free; `ε = 10⁻⁷` on route B (`ġ ≥ 0`
needs `-ġ > 0`), `0` otherwise. Every Gram matrix is `Gᵢ = Qᵢ + t·I` with `Qᵢ ⪰ 0` and the
uniform margin `t ∈ [0, 1]` MAXIMIZED: a positive margin keeps the rounded matrices positive
definite, so the exact checker can absorb the rounding residual (the probe's feasibility-only
solve returns boundary solutions with eigenvalues around `-10⁻⁸`, which no exact check can
accept; see the Phase 1 results below). The certificate (JSON) carries the variables and their
affine maps, `ε`, `D`, the bases and Gram matrices, and for every multiplier its
JUSTIFICATION: the atom index, the pair of atom indices of a product, or the variable of a box.

## The exact checker (`scripts/sos_check.py`)

Input: the printed query and a certificate (`sos_prove.py`'s JSON, or the probe's Phase 1
directories `logs/sos_certs/<id>/` with `cert.npz`, `meta.json`, `query.smt2`, `--phase1`).
Output: one line, `VERIFIED …` with statistics or `REJECTED <reason>`.

1. The query is parsed exactly (Z3's parser; `/`, `-`, `*`, `+`, integer powers; a `not` flips
   the comparison); the goal is the last atom, the hypotheses the others, strict atoms `h > 0`
   taken as `h ≥ 0` (a weakening). The goal must be an inequality; if it is `≥`, `ε > 0` is
   required (`REJECTED goal is `>=` but eps = 0`).
2. The change of variables `x = c + w·y` is taken from the certificate (`w > 0`, exact). A
   variable the certificate maps to a point (`lo = hi`) is accepted only when the query's own
   single-variable atoms pin it there; its `y` is then instantiated at `0` (every basis monomial
   containing it is dropped, the Gram matrices restricted to the principal submatrix, a
   restriction of an SOS is an SOS). A query variable the certificate does not list stays
   itself (an extra `y`), so any residual in it is exposed.
3. Every multiplier's hypothesis is derived from the query, else the multiplier is DROPPED (not
   trusted): an atom index must name an inequality atom, a product two of them, a box variable
   must have EXACTLY the certificate's `[lo, hi]` as the tightest single-variable bounds of the
   query (`(x - lo)(hi - x) = w²(1 - y²)` is then the product of two atoms), the probe's
   polynomial strings must equal an inequality atom up to a positive factor; an equality
   multiplier must name an equality atom. Dropped multipliers are listed in the verdict line
   (`-v`); the identity must then still close through step 5.
4. Gram entries and coefficients are rounded to dyadic rationals (denominator `2⁴⁰`) after
   symmetrization. A multiplier Gram whose spectrum is slightly negative (above `-10⁻⁵`, the
   solver's tolerance) is first projected onto the PSD cone and shifted by `2⁻³⁰·I`; the change
   goes into the residual. Each multiplier Gram is then checked positive semidefinite by an
   exact rational LDLᵀ (a negative pivot, or a zero pivot with a nonzero column, is `REJECTED
   multiplier i Gram not PSD`).
5. The residual `r = (-ġ(y) - ε) - (s₀ + Σ sᵢhᵢ + Σ qⱼeⱼ)` is computed exactly over ℚ and
   absorbed into `s₀`'s Gram matrix: a monomial `m` of `r` that is a square `2·m_a` of a basis
   monomial goes to the diagonal entry `(a, a)`, one that is a product `m_a + m_b` of two
   distinct basis monomials is split over `(a, b)` and `(b, a)`; a monomial that is neither is
   `REJECTED residual monomial … outside the s0 basis products`. The corrected `s₀` Gram is
   checked positive semidefinite by the exact LDLᵀ (`REJECTED s0 Gram not PSD after absorbing
   the residual (max |residual| …): negative pivot …`). This is the standard trick: the margin
   on `s₀`'s diagonal pays for every rounding and projection error; when it is not available
   the certificate is rejected.
6. VERIFIED: the identity holds exactly with every multiplier justified. Soundness: on any real
   state satisfying the hypotheses, every `hᵢ ≥ 0`, every `eⱼ = 0`, the Gram forms are `≥ 0`, so
   `-ġ ≥ ε`, contradicting the goal atom (`ġ > 0`, or `ġ ≥ 0` with `ε > 0`); the change of
   variables is a bijection (or, for a pinned variable, a consequence of the hypotheses), so
   the identity in `y` is the identity in `x`. The query is unsatisfiable.

Rejection reasons, as printed: `goal atom is an equality`, `eps < 0`, `goal is `>=` but eps
= 0`, `certificate variable not in the query`, `box of v is empty`, `v mapped to the point … the
query does not pin it to`, `scale of v not positive`, `s0 Gram/basis size mismatch`, `multiplier
i Gram/basis size mismatch`, `multiplier i Gram not PSD (min eigenvalue …): …`, `equality
multiplier i size mismatch`, `residual monomial … outside the s0 basis products`, `s0 Gram not
PSD after absorbing the residual …`, `checker error: …` (a parse failure). A VERIFIED line with
`dropped=k > 0` means `k` multipliers were unjustified and ignored, and the identity closed
without them (the verdict is still exact).

Tested on the probe's zero-hop slices of `r2_f1a` (the two SOS discharges of the STRAIGHT cover,
queries 2017 and 2018 at 7 and 9 variables, routes A, and the route-B queries 944 and 1496 at 5
and 8 variables): all four VERIFIED from `sos_prove.py`'s certificates (`maxres` ≤ 1.2e-10,
`minpivot` 4.7e-8 and 9.0e-8 on the route-B ones with `ε = 10⁻⁷`, 2.8 and 0.76 on the route-A
ones); the same four from the probe's feasibility-only program were REJECTED (negative pivot
around `-3e-8` after absorption), which is what motivated the margin. Tampering: an `s₀` entry
moved by `10⁻³` is repaired by the absorption (VERIFIED, `maxres` 2e-3; the repaired certificate
is a valid one), a wrong atom index is dropped and the identity then fails (REJECTED), `ε = 0`
on a route-B query is REJECTED, a certificate checked against the wrong query is REJECTED
(residual monomials outside the basis).

**Phase 1 certificates seen so far** (`p20-ladder/logs/sos_certs/`, read only): `r1_f1t_q83_a`,
`r1_f1t_q84_a`, `r2_f1t_q73_a`, `r2_f1t_q74_a` (16 variables, degree 4, `s₀` basis 153, three
default boxes each), all REJECTED: their `Q0` has smallest eigenvalue `-1.2e-7` to `-2.1e-7`
and the multiplier Grams `-1.6e-8` to `-2.9e-8` (the solver stopped on the boundary, no margin),
so after projection and absorption `s₀` has a negative pivot (`-3.8e-6`, `-2.4e-5`); in two of
them multipliers 19/23/28 are also dropped (their `original` strings are in the `y`
variables, unjustifiable). Phase 1's prover should adopt the margin maximization of
`sos_prove.py` (`Gᵢ = Qᵢ + t·I`, maximize `t`) and bound every rescaled variable from the query
alone; the checker is then expected to verify its certificates as it does the four above.
`r2_f1w_q113_a`, seen at the start of the session, was removed by Phase 1 before it could be
checked.

## The mechanization

* **Two opaque oracles, two axioms** (`Trusted/Oracle.lean`): `z3solve` with `z3_unsat_sound`
  as before, and `sosCheck` with `sos_unsat_sound` of the same shape (`sosCheck q = unsat → ∀ σ,
  ¬ q.sat σ`): an axiom about the exact checker's answer on a printed query, exactly as Z3's is
  about Z3's. Operationally `sosCheck` is `Trusted/Sos.lean` (`sosRun`, `oracleCheck`).
* **Unsat oracles.** `UnsatOracle V` is a verdict function with its soundness field;
  `z3Oracle := ⟨z3solve, z3_unsat_sound⟩`, `sosOracle := ⟨sosCheck, sos_unsat_sound⟩`,
  `anyOracle` (`unsat` when Z3 or the checker is, both axioms), `OracleTag` (`z3 | sos`) with
  `OracleTag.oracle` and `anyOracle_of_tag`. The sliced verdict is `OracleUnsat O q := ∃ q', (q
  → q') ∧ O.solve q' = unsat`, its monotonicity lemma `oracleUnsat_sound` uses the oracle's own
  field and no axiom; `Z3Unsat q` is now the abbreviation `OracleUnsat z3Oracle q` (its lemmas
  `Z3Unsat.of_eq`, `Z3Unsat.of_weaker`, `z3Unsat_sound` kept).
* **The flow chain is oracle-generic.** The packs take the oracle as a last parameter with
  default `z3Oracle`, so every existing statement reads as before: `VerdXCore … O`
  (`Proofs/Encoding/CutRespond.lean`), `StrataVerdS … O` / `VerdXCoreS … O`
  (`Proofs/Flow/StratifiedBarrierStrict.lean`, `Proofs/Encoding/StrictCouple.lean`),
  `VerdDynCore … rg O` (`Proofs/Encoding/ReplayDyn.lean`), `modalVerdX`, `modalVerdXS`,
  `modalVerdDynX`, `JointVerd`, `DynVerd`, `JointVerdS`, `JointAll`, `DynAll`, `JointAllS`
  and the structures `Verdicts … O`, `VerdictsS … O` (`Proofs/Encoding/Emitted/{Anchor,
  Keyed, StrictAnchor, StrictKeyed}.lean`); the theorems consuming them are generic in
  `{O : UnsatOracle (Var n)}` (inferred from the hypothesis) and apply `oracleUnsat_sound`
  where they applied `z3Unsat_sound`. The record-level theorems have generic forms
  `theorem3_window_of_records_O`, `theorem3_keyed_of_records_O`, `theorem3_window_of_records_pl_O`,
  `theorem3_keyed_of_records_pl_O`, and the four audited names are their `z3Oracle` instances
  (statements unchanged). The strict ones `theorem3_keyed_strict_of_records`,
  `theorem3_window_strict_of_records` (and `_pl`) are generic in place.
* **The pins carry the oracle.** `OracleUnsat_of_level`, `OracleUnsat_of_sliced`
  (`Trusted/Slice.lean`; the Z3 forms kept as instances), `OracleUnsat_iflowQuery_of_level` and
  the B, C variants (`VerdictsV2/ModalX.lean`); the pin theorems `modalVerdX_of_queries`,
  `modalVerdXS_of_queries`, `modalVerdDynX_of_queries(Pre)` take `O.solve q.toHost = unsat` on a
  member per group and conclude the pack at `O`; `modalVerdX_of_tagged` is the tagged form
  (`∃ t : OracleTag, (t.oracle).solve q = unsat` per group, the runner's log) at `anyOracle`.
  `GroupsOK gs O` (`Proofs/Encoding/Emitted/Run.lean`, default `z3Oracle`), `GroupsOKT gs` (a
  tag per discharged member), `groupsOK_any_of_tagged`.
* **The bridge is split around the flow groups.** `bridgeGroups k = bridgeGroupsPre ++
  bridgeGroupsFlow k ++ bridgeGroupsPost` (stays and non-connection; the joint and right-only
  packs; admissibility, handoff, progress, coverage), the same list in the same order as before
  (`List.append` is associative), likewise `bridgeGroupsS k = bridgeGroupsPre ++
  bridgeGroupsFlowS k ++ bridgeGroupsPostS` (`StrictRun.lean`; `bridgeGroupsS_eq_of_noStrict`
  as before). `verdicts_of_groups_O` / `verdictsS_of_groups_O` take the three parts (the flow
  part at `O`, the others at Z3) and give `Verdicts … O`; `verdicts_of_groups` (Z3, the
  committed instances' `_bridge_run`) is their instance, and `verdicts_of_tagged` /
  `verdictsS_of_tagged` their `GroupsOKT` form at `anyOracle`. Only the flow groups ever see the
  SOS oracle: the stay, non-connection, admissibility, handoff, progress and coverage verdicts
  keep their `z3solve` statements.
* **The runners.** `relcert-bridge-verdicts` with the knob set sends the three parts in the
  tool's order, Z3 on the first and third, Z3-then-SOS on the flow part (`RunBridge.runGroups`),
  prints `UNSAT b (N groups, dim n, k by the SOS oracle)` and the per-member `[sos …] b
  group#i member#j: sos …` lines on stderr; without the knob it sends `bridgeGroupsS` as before.
  `--check-quick-v2`'s modal and reposition re-send phases (`RunV2`) are Z3-only (their records
  are `main`'s, all Z3-`unsat`; a knob-on record set would need the hook there too, open item).
* **The generator.** `scripts/gen_v2_data.py` runs the tool with the environment's knobs; with
  `RELCERT_SOS_SECS` set and at least one `: sos unsat` line on the run's stderr, the cover leaf
  `InstancesV2/BenchCovers/<b>.lean` gets the marker `-- oracles: z3 sos (N flow levels verified
  by the SOS oracle, RELCERT_SOS_SECS=S; docs/SOS-ORACLE.md)` under its header.
  `scripts/gen_bridge.py` reads it (`sos_used`) and emits the instance at `anyOracle`
  (`hv : Verdicts IR n cX cov prog ce anyOracle`, the `_O` record-level theorem) with the tagged
  `_bridge_run` (`bridgeGroupsPre/Flow/Post`, `GroupsOKT` on the flow part,
  `verdicts_of_tagged`); without the marker the emitted text is byte-identical to today's (checked
  on `watertank`). The committed leaves carry no marker (`main`'s records, Z3-only).

### The axiom audit

With the knob unset nothing changes: `AxiomCheck` 16 lines, 9 at the three standard axioms, 7
adding `z3_unsat_sound`, and the battery 78 lines (76 standard, 2 with `z3_unsat_sound`), both
textually identical to `main`'s (diffed, see the gate). No committed instance mentions
`sos_unsat_sound`: the generic chain carries no axiom, `z3Oracle` carries Z3's, and
`anyOracle` is named only by an instance whose records carry an SOS verdict.

An instance whose records contain an SOS verdict is stated at `anyOracle` and shows
`sos_unsat_sound` in its axiom line. `scripts/sos_axiom_check.lean` states `watertank`'s
theorem at `anyOracle` beside the committed Z3 one (`lake env lean scripts/sos_axiom_check.lean`):

```
AXIOMS_PLACEHOLDER
```

## The gate (this branch, 2026-11-13)

GATE_PLACEHOLDER

## Open items

OPEN_PLACEHOLDER
