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

## 2. The verdict on `tooling_sound`

`Archive/GapThreeTask3.lean:63` has exactly the right *shape* — automaton-parametric,
with the programs **derived** from two `HybridAut`s via `graphOf_Gr`:

```lean
theorem tooling_sound (L R : HybridAut n) … :
  rvalid (theorem3Form (bigChoice (L.leftProgs ++ [frozen]))
                       (rightAutomatonBody (graphOf_Gr R lam) mv)
                       (ϕinv ∧ mvValidR …))
```

and `Archive/GapThreeRoverTooling.lean:531` (`rover_tooling_sound_full`) instantiates it
**non-vacuously** at concrete rover data — freshness (`mv`/`tg` in `Aux`), the `hd`/`hddF`
disjointness (by side split), `graphOf`, `RightProjAlign`, and even `HExistSeg` all
discharged concretely. The vacuity that killed the earlier route
(`ProbeMvHd.probe_hd_false`, `mv` inside the left block) is fixed.

**But it cannot be cited for Theorem 3, because it assumes the hard half.** The residual
hypotheses of `rover_tooling_sound_full` are the Z3 leaf (`cert`, fine — that is the
oracle boundary) **and `hemit`/`hemit' : EmitSegs`**. And `EmitSegs`
(`Proofs/Encoding/RepositionDischarge.lean:359`) says:

> for every mode `q` and every state satisfying the invariant, **there exists** a chain
> of segments along declared edges, chained by `tgt = src`, whose total duration bounds
> any left evolution from that state

That is the witness-existence conclusion Theorem 3 is supposed to *establish from the
cover*. Citing `tooling_sound` for Theorem 3 would assume what is to be proved. This is
precisely why R1 was scheduled ("witness extraction replacing `EmitSegs`/`EmitWindows`").

**Verdict: right target statement, not a usable citation.**

## 3. The good news — the Emit-free top theorem already exists

`Proofs/Encoding/RepositionFinish.lean:27`:

```lean
theorem theorem3_faithful_multi (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n))
    (hψ  : encode (Equiv.refl _) ϕinv = invLe g)
    (hd  : Disjoint …)
    (hstep : ∀ σ, sat (phiInv g mv G.modes.length) σ → sat (faModal … ) σ)
    (hddF : Disjoint …) :
    rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
                         (ϕinv ∧ mvValidR mv G.modes.length))
```

**No `Emit*` hypothesis.** The substantive premise is `hstep` — one left residence
matched by a star of declared `G`-edges — which S1–S3 discharge for watertank from the
cover certificate plus the existence witnesses.

So the ingredients for a genuine automaton-level Theorem 3 are all present:

| piece | where | status |
|---|---|---|
| automaton-level packaging (`HybridAut`, `graphOf_Gr`, `leftProgs`) | `Archive/GapThree*` | exists, non-vacuous |
| Emit-free `theorem3Form` conclusion | `RepositionFinish.lean:27` | exists |
| discharging `hstep` from a cover + existence | S1/S2/S3, watertank | exists **at concrete data only** |

**The missing work is doing the `hstep` discharge parametrically over `HybridAut`**
rather than at one benchmark's concrete data. That is a re-basing of `tooling_sound`
onto the modern chain, not a new development — but it is not a re-typing either: the
Arc-1 chain and the modern chain have different segment shapes.

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

2. **Re-base `tooling_sound`.** Automaton-parametric `hstep` discharge onto
   `theorem3_faithful_multi`. Covers the suite in one theorem rather than 46 instances —
   the most economical route to a paper-faithful claim, and strictly better than the
   45-modal-instance arc. Sizing not attempted here.

3. Note that the paper currently describes `\toolname` as a SymPy + Z3 prototype and
   **does not mention Lean at all**. If the mechanization is meant to back this paper,
   §§1–4 above are what the bridging text has to say.
