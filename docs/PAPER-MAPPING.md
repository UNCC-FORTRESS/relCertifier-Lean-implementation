# Mapping the paper to the mechanization — and the verdict on `tooling_sound`

Status: ASSESSMENT (2026-07-19, against main = a93c711). Read this before claiming the
Lean development mechanizes the paper's Theorem 3.

---

## 1. What the paper asks for

The paper states its central obligation in the ∀∃ modality **over the `cpsProg`
programs themselves**, in three places:

- **Definition 1** (∀∃ Relational Invariance): `φInv → [|(L, R)⟩⟩ φInv`.
- **Eq. (mode-inv)**: `φInv → [|(P^L_{m_L}, Rsys)⟩⟩ φInv` — one left branch against the
  **full starred right program**.
- **Theorem 3** (Soundness of Synthesis) concludes exactly `φInv → [|(L,R)⟩⟩ φInv`.

So the target Lean shape is `rvalid (theorem3Form L R φ)` with `R` derived from the
automaton. That is the **modal** family (README, "Theorem families"), which today exists
for watertank (full) and rover_drag (a reduced pilot).

## 2. The top-level connection is already there, generically, and Emit-free

**This section corrects an earlier draft of this document**, which sent the reader to
`tooling_sound` as "the target shape". That was looking in the wrong place: the modern
chain already carries a paper-faithful top, and it is strictly better than
`tooling_sound` because it assumes no emission device.

**`theorem3Form`** (`Checker/Cover/Encoding.lean:51`) is the paper's Theorem 3 formula,
and its own docstring says so:

```lean
/-- The paper's **Theorem 3** relational formula: `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv` … -/
def theorem3Form (L R : Program V) (ϕinv : RFormula V) : RFormula V :=
  RFormula.imp ϕinv (faShape (Program.star L) (Program.star R) ϕinv)
```

It takes **loop bodies** and stars them itself, matching `cpsProg ≡ (⋃_m P_m)*` on both
sides.

**`theorem3_faithful_multiE_LR`** (`Proofs/Encoding/EnvelopeChain.lean:387`) mechanizes
the paper's §2.3 reduction. Its four hypotheses are `hψ` (the encoding identity), two
disjointness conditions `hd`/`hddF` (both with **generic dischargers** — `hdis_multi`,
`hddF_multiE`), and one substantive premise:

```lean
(hstep : ∀ σ, sat (phiInvE g (domL ∧ domR) mv k) σ →
   sat (faModal id (bigChoice leftProgs) (star (rightAutomatonBody G mv)) (phiInvE …)) σ)
```

Since `faModal ρ α β φ = [α]⟨ρβ⟩φ` (dL-rel `Modality.lean:16`, with
`sat_encode_faShape` tying the encoded relational modality to it), `hstep` reads: *for
every run of **one left body iteration**, there exists a run of the **starred right
automaton** preserving the invariant.* That is literally the paper's

> Eq. (relational-invariant): `φInv → [|(Lsysi, Rsys)⟩⟩ φInv`

The correspondence is element-for-element:

| paper | Lean |
|---|---|
| `cpsProg` L, R as starred loop bodies | `theorem3Form L R φ` stars both |
| **Definition 1**: `φInv → [|(L,R)⟩⟩ φInv` | the **conclusion** of `theorem3_faithful_multiE_LR` |
| **Eq. (relational-invariant)**: one-iteration preservation | the **hypothesis** `hstep` |
| *"Repeated application of this obligation then constructs a matching `Rsys` execution for every finite number of `Lsys` control cycles"* | `relational_loop_multi` — the loop induction inside the proof |
| **Eq. (mode-inv)**: decomposition per left mode | `bigChoice leftProgs`, one entry per left mode, with `hstep` quantifying over the choice |

So the paper's §2.3 — Definition 1 reduced to one-iteration preservation and then
decomposed per left mode — **is mechanized once, generically, with no `Emit*`
hypothesis**. What remains per benchmark is exactly `hstep`, i.e. the paper's
eq. (mode-inv) obligation, which is what the paper's §4 discharges via the
all-successors cover.

`watertank_modal` is that assembly in one line:

```lean
refine theorem3_faithful_multiE_LR GrW mvM gW domLW domRW (leftProgsW dt) (canonInv gW)
  (encode_canonInv gW) ?_ ?_ ?_
· exact hdis_multi …                              -- generic
· exact hstep_assembled_multiE … (HmultiW dt h00 … hES22)   -- per-benchmark: verdicts + existence
· exact hddF_multiE …                             -- generic
```

## 3. The verdict on `tooling_sound`: superseded, not the target

`Archive/GapThreeTask3.lean:63` has the automaton-parametric packaging — programs
**derived** from two `HybridAut`s via `graphOf_Gr` — and `rover_tooling_sound_full`
instantiates it **non-vacuously** (freshness with `mv`/`tg` in `Aux`, `hd`/`hddF` by side
split, `graphOf`, `RightProjAlign`, and `HExistSeg` all concrete; the
`ProbeMvHd.probe_hd_false` vacuity is fixed).

**But it cannot be cited for Theorem 3: it assumes the hard half.** Its residual
hypotheses are the Z3 leaf (fine — the oracle boundary) **and `hemit`/`hemit' :
EmitSegs`**, where `EmitSegs` (`Proofs/Encoding/RepositionDischarge.lean:359`) asserts:

> for every mode `q` and every state satisfying the invariant, **there exists** a chain
> of segments along declared edges whose total duration bounds any left evolution

which is the witness-existence conclusion Theorem 3 is meant to *establish from the
cover*. That is why R1 was scheduled.

**Net:** `tooling_sound` is superseded by §2's chain on the substance. Its one remaining
advantage is packaging — deriving the programs from a `HybridAut` rather than taking
`leftProgs`/`G` as given — which is a convenience worth borrowing if an
automaton-parametric statement is ever wanted, not a soundness matter.

## 3a. Two routes reach `theorem3Form` — and the settling route is generic

**Correction (second pass).** An earlier version of this section said "`hstep` has not
been assembled for the other 45". That is wrong, and it came from looking only at the
multiflow/modal route. There are **two** routes to `rvalid (theorem3Form …)`:

**Route A — settling / ε-cadenced. Generic, no per-benchmark proof.**
`settling_end_to_end` (`Proofs/Encoding/FvDischarge.lean:632`) is parametric in
`SettlingModel n` and concludes

```lean
rvalid (theorem3Form (clockedSeg (leftBlock fL) domL (Aux b) M.dt)
                     (rightAutomatonBodyC M.graph (Aux a) (Aux c) M.dt)
                     (ψpostG M.graph M.GdOf (Aux a) ϕinv))
```

Its hypotheses are `decideWellFormed M = true` (kernel `rfl` per benchmark), the
encoding identity, side-splits (generic dischargers), and the per-mode Z3 `BoxLe`
certificates. The settling analogue of `hstep` — `GuardSettlingH` — is discharged
**generically** by `wellformed_sound` + `FvDischarge`, which is why the family headers
say it outright: *"per-run Z3 certificates yields `GuardSettlingH` — hence
`theorem3_faithful_settling` — **with no per-benchmark proof**"*
(`Instances/SettlingInstances.lean:7`, `Instances/TerrainInstances.lean:8`).

Supporting this for all 46: `faithfulSettling … = true` by kernel `rfl` (the model *is*
the parsed file), and `GuardSettlingB_rescale` transporting the per-mode content to each
benchmark's real chart — the 46 `*_real` theorems in `Instances/RealInstances.lean`.

So `theorem3Form` is **available for all 46 with no per-benchmark proof**. The line is
actually written out at watertank (`Instances/EndToEnd.lean:49,107,152`, three variants)
and bundled at arm_refinement (`Instances/Mega.lean`); for the remaining 44 it is a
one-line application, not new mathematics. That is a packaging gap, not a mathematical
one.

**Route B — multiflow / reposition.** `theorem3_faithful_multiE_LR` (§2), instantiated
at watertank only.

**The real distinction is the witness shape, not coverage:**

| | route A (settling) | route B (multiflow) |
|---|---|---|
| conclusion | `rvalid (theorem3Form …)` | `rvalid (theorem3Form …)` |
| coverage | all 46, generic | watertank |
| witness | ε-cadenced, one right cycle per round, full-width | multi-step: several right cycles, mode changes, right-only reposition segments |
| paper content | Definition 1 / eq. (mode-inv) | Definition 1 **+ §4** (all-successors cover, budget, repositions) |
| status | R7 marked the cadenced chain DEPRECATED — retained until the modal form and cut lift reach parity | current |

So the honest position: **the paper's Theorem 3 conclusion shape holds for all 46**
(route A, generic); what is watertank-only is the **multi-step witness content of §4** —
the part that makes Theorem 3 more than one-cycle-per-round matching.

## 4. Residual modelling gaps, even after a re-basing

These are choices, not defects, but the paper must state them:

| paper `cpsProg` | mechanized | direction |
|---|---|---|
| left has guards, `mv`, clock | left is a flat `star (bigChoice leftProgs)`, guard-free | **stronger** — the left is ∀-quantified, so an over-approximation strengthens the claim (documented in `HybridAut.leftProgs`) |
| left is exactly the automaton | left `bigChoice` carries an extra frozen program | **stronger** — more left behaviours under the ∀ |
| `?guard_m(x)` on transitions | `e.guard = ⊤` | **permissive** — the "⊤-model", a documented Arc-1 decision (`HybridAut.edgesOf`: "the real guard is dissolved by the ⊤-model, as in the runtime `cgReal`"). Harmless because the cover is demonic over successors; see `docs/COVER-AUDIT.md` |
| `t := 0; {…, t' = 1 & t ≤ ε_R}` | right modes carry no clock (`modeW` has `dom := domRW`) | **permissive** — the witness's joint segments do respect `ε_R/λ`, but the statement does not record it |
| invariant `φInv` | `φInv ∧ mvValidR` | bookkeeping conjunct |
| jump-then-flow | flow-then-jump | rotation; see `docs/ROTATION-SCOPE.md` |

Two of the paper's own assumptions land well: **§ Well-formedness** (nonblocking +
successor-completeness) is exactly what `GuardSettlingB`'s final conjunct *proves* for
all 46 benchmarks, and **Limitations** already says resets are identities, matching the
mechanization.

Also faithful: **Definition 4 (All-Successors Cover)** maps cleanly onto
`Covered`/`decideCovered` — base case `B ≤ w(m_R, joint)`, successor case ∃kind
∀retained-edges, σ ↔ `SrcSetting`. One presentation detail: the paper's budgets are
real-valued (`B = ε_L`, `w = ε_R/λ`); the Lean uses an ℕ-discretization (`weight : ℕ`,
budget `⌈ε_L/δ_L⌉`).

## 5. Honest options

1. **Claim what is proven.** `rvalid (theorem3Form …)` available for all 46 by the
   generic settling route (written out at watertank and arm_refinement); the full
   multi-step §4 witness content instantiated at watertank, existence proven in-kernel;
   and the settling family *discharges* the paper's own well-formedness assumption.
   State the §4 modelling choices. Zero further work.

2. **Write out route A for the remaining 44** — one line each, no new mathematics, if
   you want 46 named `theorem3Form` theorems rather than a generic theorem plus the
   ingredients.

3. **Discharge route B's `hstep` beyond watertank** if the paper's §4 multi-step witness
   content (cover, budget, repositions) is to be mechanized per benchmark rather than
   demonstrated once. This is the real remaining arc.

4. Note that the paper currently describes `\toolname` as a SymPy + Z3 prototype and
   **does not mention Lean at all**. If the mechanization is meant to back this paper,
   §§1–4 above are what the bridging text has to say.
