> **HISTORY (moved to `docs/history/` on 2026-10-10).** A superseded record, kept for
> provenance; `docs/history/README.md` says what replaced it. Paths, file names and counts
> below describe the repository at the time of writing, not the current artifact.

# Cut composition — the declared invariant of the checked-cut benchmarks

Status: landed 2026-10-08, branch `cut-composition`. Five new leaves
`Instances/<Name>Declared.lean` plus the generic leaf
`Proofs/Encoding/CutComposition.lean`; base instances, `Proofs/` chain, benchmarks,
runner and pins untouched. Companion to `docs/PAPER-MAPPING.md` §2c.

**Suite deduplication (2026-10-08, branch `dedupe-suite`).** Three of the five were
duplicates and were removed afterwards: `arm_fidelity_high` and `plant_fan_high` are
byte-identical to `arm_chain_rung3` (§2a already records this), and `plant_fan_mid` is
`arm_fidelity_mid` with tolerance 0.3 instead of 0.25 (§2b). The surviving leaves are
`ArmChainRung3Declared.lean` and `ArmFidelityMidDeclared.lean`; the analysis below is
kept as written, since every statement about a removed name holds verbatim for its
surviving representative. `docs/SUITE-DEDUPE.md`.

## 1. The question

`arm_chain_rung3`, `arm_fidelity_high`, `arm_fidelity_mid`, `plant_fan_high` and
`plant_fan_mid` carry modal Theorem 3 instances whose loop invariant is
`region ∧ φ_declared`, where `region` is the right `Hold` mode's guard atom `θ_R ≥ 0.6`
and `φ_declared` is the file's row (`θ_L ≤ θ_R + 0.15`; `+ 0.25` for `arm_fidelity_mid`,
`+ 0.3` for `plant_fan_mid`). The region is the tool's **checked cut** for the `Hold`
pairing: `Trusted/OracleAPI.lean` `checkedCut` keeps a guard conjunct as a cut when it is
flow-invariant along the mode's own field (O2; O1 is syntactic — the atom *is* a guard
conjunct), and `andCuts` conjoins the kept cuts to every flow-query domain of that mode.
The instances were conditioned on the region at **every** right mode because the modal
chain's bookkeeping (`mvValidR`) had no per-mode slot for it, so the theorems read: *from
joint states where the right already satisfies `Hold`'s guard, the refinement is
maintained* (`README.md`, *Conditioning*; `docs/VERDICT-EVIDENCE-AUDIT.md` Part II).

The paper needs the **declared** invariant: `φ_declared → [|(L*, R*)⟩⟩ φ_declared` from
every state satisfying `φ_declared`.

## 2. Confirming the tool's reading

Measured with `RELCERT_DEBUG=1 relcert benchmarks/suite_uniform/<name>/input.txt`
(Z3 4.15.1, 2026-10-08) against the emitted covers (`Instances/BenchCovers/<name>.lean`,
flag order `jointOK, repoPre, repoPost, dynPre, dynPost`) and the emitted cut certificates
(`Instances/EvolStrengthenings/<name>.lean`). All five certify at λ = 1, budget 1.

*Note (2026-10-09).* The `repoPre`/`repoPost` columns below are the **static**
(zero-duration) reposition flags of the cover emitted on 2026-10-08. The static reposition
was removed from the certifier on 2026-10-09 (`docs/COVER-AUDIT.md`, note of that date);
the emitted flag order is now `jointOK, dynPre, dynPost`, and `arm_chain_rung3` and
`arm_fidelity_mid` still certify at λ = 1, budget 1 with the regenerated covers (their
right-only steps are dynamic repositions). The columns are kept as the record of the
earlier reading. The zero-duration hops into `Hold` described below belong to the two
composed `…_declared` theorems (`sem_bigSeq_identity` over the `⊤`-guarded right
program), not to the tool's cover; they are not affected by the removal.

### 2a. The high family — `arm_chain_rung3`, `arm_fidelity_high`, `plant_fan_high`

Byte-identical dynamics, guards and evolves (the three files differ only in their
`name`); right chain `ApproachA (θ' = 0.5) → ApproachB (0.35) → ApproachC (0.2) → Hold (0)`
with self-loops, `Hold`'s guard `0.6 ≤ θ < 1.15`, uniform right evolve `0 ≤ θ ≤ 1.2`,
left `0 ≤ θ ≤ 0.65`, `|v| ≤ 0.45`.

| right mode | checked cut (atom, O2 route) | jointOK (Accelerate / Brake) | repoPre (Acc / Brk) | repoPost (Acc / Brk) | dynPre | dynPost |
|---|---|---|---|---|---|---|
| `ApproachA` | `θ ≥ 0.0`, DI-strict (B) | **yes / yes** | no / no | no / no | yes | yes |
| `ApproachB` | `θ ≥ 0.35`, DI-strict (B) | no / no | yes / no | no / no | yes | yes |
| `ApproachC` | `θ ≥ 0.5`, DI-strict (B) | no / no | yes / yes | yes / yes | yes | yes |
| `Hold` | `θ ≥ 0.6`, **frozen** (θ' = 0, no Z3) | **yes / yes** (at the cut-narrowed domain) | yes / yes | yes / yes | yes | yes |

Only the lower-bound guard atoms survive O2 (every approach rate is positive, so the
upper bounds `θ ≤ 0.35` etc. are not flow-invariant). `Hold`'s joint certificate is the
one that needs its cut: on the bare domain the `Hold` queries are `sat` on all three
routes, with the cut `θ_R ≥ 0.6` routes B and C are `unsat` (the boundary `θ_L = θ_R +
0.15 ≥ 0.75` lies outside the left evolve `θ_L ≤ 0.65`). The cut is load-bearing for the
tool too: `RELCERT_NO_CUT=1` declines all three (at λ = 6 the three approach modes pass
and `Hold` fails; no λ in `[1, 6]` certifies `Hold` without the cut).

Cut probes issued by `--run-verdicts` (`Verdicts/RunCut.lean`, the O2 obligations of the
emitted atoms, three routes each, first `unsat` wins): per benchmark `R/ApproachA`,
`R/ApproachB`, `R/ApproachC` (B, strict) and `R/Hold` (A — the frozen atom is probed as
route A and is `unsat` there too). **12 of the 105 cut probes** belong to these three
benchmarks; the other 93 are the ten terrain/rollover benchmarks' (9 each, `rung3_6to8`
12).

**Right-only repositioning from each non-`Hold` mode.** With the left frozen,
`Lie(θ_L − θ_R − 0.15) = −θ_R' = −c_q ≤ 0` for `c_q ∈ {0.5, 0.35, 0.2}`: the declared bound
is preserved along any right-only flow in any approach mode (this is the tool's
`checkDynRepo` route-A fact, `dynPre = dynPost = true` at all four modes), `θ_R` increases
monotonically, stays in `[0, 1.2]` as long as the target is `≤ 1.2`, and reaches `Hold`'s
guard `θ_R = 0.6` from any `θ_R ∈ [0, 0.6)` in `(0.6 − θ_R)/c_q` time units of the mode's
own dynamics — within one right cycle, no mode change needed, since `0.6 ≤ 1.2`. Hops to
`Hold` along `q → … → Hold` are then zero-duration. `Hold`'s flow (`θ' = 0`) preserves
the region trivially. **Reading confirmed** for all three.

### 2b. The mid family — `arm_fidelity_mid`, `plant_fan_mid`

Right chain `ApproachFast (θ' = 0.5) → ApproachSlow (0.3) → Hold (θ' = ½(0.6 − θ))`,
`Hold`'s guard `0.6 ≤ θ < 1.15`, right evolve `0 ≤ θ ≤ 1.2`, left `−0.05 ≤ θ ≤ 0.65`,
`|v| ≤ 0.45`. The two files differ in the tolerance only (`0.25` vs `0.3`).

| right mode | checked cut (atom, O2 route) | jointOK (Acc / Brk) | repoPre | repoPost (Acc / Brk) | dynPre | dynPost |
|---|---|---|---|---|---|---|
| `ApproachFast` | `θ ≥ 0.0`, DI-strict (B) | **yes / yes** | no | no | yes | yes |
| `ApproachSlow` | `θ ≥ 0.35`, DI-strict (B) | no / no | yes | no / no (`arm_fidelity_mid`); yes / yes (`plant_fan_mid`) | yes | yes |
| `Hold` | `θ ≥ 0.6`, **shape** (contract `½(0.6 − θ)`, equilibrium on the safe side; `contract_stays`, no Z3) | **yes / yes** (cut-narrowed) | yes | yes | no | no |

`Hold`'s dynamic reposition fails here because `θ' = ½(0.6 − θ) < 0` above `0.6`: a
right-only `Hold` flow can *decrease* `θ_R`, so route A is `sat`. That is irrelevant to
the composition — the response never flows in `Hold` for positive duration — but it is
why `dynPre = dynPost = false` at `Hold`. These two benchmarks are **not** in
`Verdicts/RunCut.cutBenchmarks` (no cut probes): their only DI-route atoms are the two
approach lower bounds, and their `Hold` atom is discharged by the kernel-side shape
recognizer. Unlike the high family, the tool certifies them **without** cuts as well
(`RELCERT_NO_CUT=1`: `arm_fidelity_mid` at λ = 9/2, budget 5; `plant_fan_mid` at λ = 15/4,
budget 4 — `Instances/BenchCoversNC/`), so at the tool level the cut buys λ = 1, budget 1;
at the Lean level the λ = 1 instances need the region at `Hold` (route C), which is why
they were conditioned.

**Right-only repositioning**: `Lie(θ_L − θ_R − tol) = −c_q ≤ 0` in both approach modes
(`c ∈ {0.5, 0.3}`), `θ_R` reaches `0.6` within one right cycle of the start mode, hops to
`Hold` are zero-duration; `Hold`'s contraction never leaves `θ ≥ 0.6` (O2 by shape).
**Reading confirmed** for both.

## 3. The finding: the literal target is false; the honest target is the mode-region form

The target shape asked for — `rvalid (theorem3Form L R (φ_declared ∧ envLR ∧ mvValid))`,
the declared invariant from **every** state satisfying it, the right in **any** declared
mode — is **false** for all five, independently of any proof device:

**Countermodel (high family, every `dt > 0`).** Take `mv = Hold`, `θ_R = 0.3`,
`θ_L = 0.45`, `v_L = 0.3`. The state satisfies `φ_declared` (`0.45 ≤ 0.3 + 0.15`), both
evolve domains, and `mvValid`. Let the left run its `Accelerate` window
(`θ' = v, v' = −(θ − 0.5) − v`) for any `t ∈ (0, dt]`: `θ_L` rises at once (`θ_L' = 0.3`),
e.g. `θ_L(0.1) = 0.4787`, `θ_L(0.5) = 0.5684`, the run staying inside `θ ≤ 0.65`,
`|v| ≤ 0.45` (RK4, step 10⁻⁴). The right automaton from `mv = Hold` has exactly one
enabled step, `Hold`'s own (`next = [Hold]`), whose field is `θ' = 0`: every run of `R*`
leaves `θ_R = 0.3`. The postcondition needs `θ_L ≤ 0.45`; it fails by `0.0287` at
`t = 0.1`. No response exists.

**Countermodel (mid family).** `mv = Hold`, `θ_R = 0.3`, `θ_L = 0.55` (`arm_fidelity_mid`,
tolerance `0.25`) or `θ_L = 0.6` (`plant_fan_mid`, `0.3`), `v_L = 0.3`. `Hold`'s field
`½(0.6 − θ)` raises `θ_R` by at most `0.15·t` while the left rises by `≈ 0.3·t`:
`θ_L − θ_R − tol = +0.0136` resp. `+0.0134` at `t = 0.1` with the best possible right
response (flow in `Hold` for the whole window), and worse for longer windows.

The failing step, in the composition the task describes, is (a): *from any state
satisfying `φ_declared` with the right in any declared mode, a right-only execution
reaches `Hold`'s region*. From `Hold` itself, below its guard, there is no such execution
(`θ_R` is frozen, resp. contracts toward `0.6` too slowly and, on the far side, away from
it). From the approach modes the step holds. So the statement that is true — and the one
the cut certificate actually supports — carries the cut **at `Hold` and nowhere else**:

```
rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody Gr mv)
          (canonInvM g [] ∧ envLR domL domR ∧ mvRegionR mv regions Gr.modes.length))
   with  regions Hold = ⌊θ_R ≥ 0.6⌋,   regions q = ⊤  for the approach modes
```

`mvRegionR mv regions k = ⋁_q (mv = q ∧ regions q)` is the mode-region bookkeeping the
development already uses for `rung2c` and the terrain composites
(`Proofs/Encoding/EnvelopeChainR.lean`). With `⊤` at the approach modes it is exactly
`mvValid` there; at `Hold` it says the right entered through the guard and the guard's
lower bound has been kept — which is precisely what O1 (entry) and O2 (invariance) of the
checked cut compose to. The trust base's *guard-gated switching* item supplies the entry;
O2 (`frozen` resp. `shape`, both kernel-side) supplies the invariance.

This statement is strictly stronger than the five base theorems (which demand the region
at every mode) and is the strongest form of the declared invariant that is true of these
automata.

## 4. What was proved

Per benchmark a leaf `Instances/<Name>Declared.lean` (namespaces `ArmChainRung3Declared`,
`ArmFidelityHighDeclared`, `ArmFidelityMidDeclared`, `PlantFanHighDeclared`,
`PlantFanMidDeclared`), importing the base instance for its data (`fLA`, `fRA`, `domLA`,
`domRA`, `gA`, `regA`, `GrA`, side-splits, window family) and stating

```lean
theorem <name>_declared (dt : ℝ) (hdt : 0 ≤ dt) :
    RFormula.rvalid (theorem3Form (bigChoice (leftProgsA dt)) (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInvM gA []) (envLR domLA domRA))
        (mvRegionR mvA regionsA GrA.modes.length)))
```

with `regionsA q = if q = Hold then invLe regA else Formula.tt`. **No verdict
hypothesis** — `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all
five. The base theorems (`<name>_modal`, region at every mode, two `Verd3` packs each)
are kept unchanged.

**The response** (`respondA`, `HmultiA`): the `⟨…⟩` side of `faModal` runs after the left
window, so the right answers with a right-only flow (the catch-up device of
`WindowGrowth.lean`, as for the rover trio):

1. the left window ends inside its evolve domain (`windowSeg_end_domL`): `θ_L ≤ 0.65`;
   the right coordinates survive it (`windowSeg_mask`);
2. in the start mode `q` the right flows at its constant rate `c_q` for
   `τ = max(0, (0.6 − θ_R)/c_q)` along the explicit curve `rateCurve`
   (`sem_rightBlock_rate`, `Proofs/Encoding/CutComposition.lean`), reaching `θ_R ≥ 0.6`
   inside `[0, 1.2]`; from `Hold` the start region already gives `θ_R ≥ 0.6` and the
   run is the identity (`static_hop_existsR`). This is step (a) of the composition, the
   `checkDynRepo` fact, as a curve rather than a Z3 verdict;
3. zero-duration runs along the declared chain into `Hold` (`sem_bigSeq_identity`);
4. at the endpoint, `θ_L ≤ 0.65 ≤ 0.6 + tol ≤ θ_R + tol` closes `φ_declared`, the left
   domain is untouched, the right domain is the run's, and `Hold`'s region is `θ_R ≥
   0.6`. This is step (b): the `Hold` phase. It is the same arithmetic that makes the
   base instances' route-B/C `Hold` queries `unsat`, so the base coupling `coupleA` is
   not consumed and its `Verd3` hypotheses are not needed.

**Assembly**: `theorem3_faithful_multiR_LR` (the region-carrying top theorem) with
`hdis_multi` (plain windows), `hstep_assembled_multiR` (the provider receives the start
region and owes the landing region `regions (qfOf segs q)`, `= regions Hold` for every
chain), and the new `hddF_multiR_plain` — `hddF_multiE`'s plain-window side with
`hddF_multiR`'s postcondition side (the existing `hddF_multiR` is for guard-gated
windows).

**Guards.** The witness enters `Hold` with `θ_R ≥ 0.6`, the lower bound of `Hold`'s guard,
always. The statement's automaton has `⊤` edge guards like every other modal instance
(`docs/COVER-AUDIT.md`, the ⊤-guard note), so the intermediate hops (`A → B → C` at
`θ_R ≥ 0.6`, say) are not guard-tested, and `Hold`'s upper bound `θ < 1.15` is not
either (states with `θ_R ∈ [1.15, 1.2]` are in the invariant set and are handled by the
same response).

## 5. Per-benchmark summary

| benchmark | strategy confirmed (tool) | cut (atom, route; load-bearing for the tool?) | cut probes in `--run-verdicts` | literal `mvValid` form | declared theorem landed | file | axioms |
|---|---|---|---|---|---|---|---|
| `arm_chain_rung3` | yes: jointOK at `ApproachA`, `Hold`; static/dyn repositions at `B`, `C`; right-only reach of `0.6` from any approach mode | `Hold: θ ≥ 0.6`, frozen; yes (`NO_CUT` declines) | 4 (`A/B/C` B-strict, `Hold` A) | **false** (countermodel §3) | `arm_chain_rung3_declared`, mode-region form | `Instances/ArmChainRung3Declared.lean` | std 3 |
| `arm_fidelity_high` | same (identical system) | same | 4 | false | `arm_fidelity_high_declared` | **removed 2026-10-08** (duplicate of `arm_chain_rung3`) | — |
| `plant_fan_high` | same (identical system) | same | 4 | false | `plant_fan_high_declared` | **removed 2026-10-08** (duplicate of `arm_chain_rung3`) | — |
| `arm_fidelity_mid` | yes: jointOK at `ApproachFast`, `Hold`; right-only reach from `Fast`/`Slow`; `Hold` dyn-repo off (contraction) | `Hold: θ ≥ 0.6`, shape; no for the tool (`NO_CUT` certifies at λ = 9/2), yes for the λ = 1 Lean instance | 0 (not in `cutBenchmarks`) | false | `arm_fidelity_mid_declared` | `Instances/ArmFidelityMidDeclared.lean` | std 3 |
| `plant_fan_mid` | same, tolerance `0.3` | same (λ = 15/4 without the cut) | 0 | false | `plant_fan_mid_declared` | **removed 2026-10-08** (near-duplicate of `arm_fidelity_mid`) | — |

Wiring: `Instances/ModalBattery.lean` imports the leaves and prints their axioms
(59 theorems in the battery at the time; 50 after the deduplication, with the two
surviving `…_declared` theorems). No `ModalSpecs` namespace, runner row, pin or coverage
change: the theorems carry no Z3 hypothesis, exactly as the rover trio's `*Handoff.lean`
leaves.

## 6. What is not done

* The countermodels of §3 are checked numerically (RK4) and by inspection of the
  automaton, not mechanized as `¬ rvalid …` theorems (the left is a damped oscillator;
  an explicit-solution falsification is possible but was not in scope).
* The base theorems' `Verd3` packs stay in the runner (`RunModal.modalTable` rows for the
  five, 2 × 2 queries each) because the base theorems stay; the new theorems add nothing
  to discharge.
* The response does not mirror the tool's cover literally: the tool answers from
  `ApproachA` with a joint piece there (`jointOK`), the Lean witness repositions to `Hold`
  from every start. Both are responses of the same automaton; the Lean one needs no
  existence certificate at `ApproachA` (whose constant drift exits `[0, 1.2]` in finite
  time, so an unbounded joint piece there would not exist anyway).
