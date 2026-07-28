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

## 3a. What is actually left, per benchmark

Only `hstep`. For watertank it is assembled from six route verdicts and six existence
facts. For the other 45, the cover machinery yields *preservation*
(`CoexecInvAllThroughoutG`, ∀ over reaches) and the existence residuals separately, but
the assembly into `hstep` has not been done. So:

- the paper's §2.3 reduction — **mechanized generically** ✓
- the paper's Theorem 3 at a benchmark — **done for watertank**, pending for 45
- an automaton-parametric version — would additionally need `hstep` discharged over
  `HybridAut` rather than at concrete data

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

1. **Claim what is proven.** Theorem 3 instantiated end-to-end for watertank (existence
   proven in-kernel, six named verdicts); invariant-preservation for all 46 via the
   settling and throughout families; and note that the settling family *discharges* the
   paper's own well-formedness assumption. State the §4 modelling choices. Zero further
   work.

2. **Discharge `hstep` for the remaining 45.** The generic top already holds; this is
   the only missing piece for a per-benchmark Theorem 3. Doing it *parametrically over
   `HybridAut`* (borrowing `tooling_sound`'s packaging) would cover the suite in one
   theorem rather than 45 instances. Sizing not attempted here.

3. Note that the paper currently describes `\toolname` as a SymPy + Z3 prototype and
   **does not mention Lean at all**. If the mechanization is meant to back this paper,
   §§1–4 above are what the bridging text has to say.
