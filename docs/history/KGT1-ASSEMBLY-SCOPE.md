> **COMPLETED — archived 2026-07-30.** The k > 1 window assembly landed as
> `Hmulti_windowR_prefixed` in `Proofs/Encoding/RepoPrefixR.lean` (and its list-invariant
> sibling `Hmulti_windowRF_prefixed` in `WindowRF.lean`). The "21 blocked benchmarks" this
> document opens with all carry modal Theorem 3 today. Note the resolution was *not* the
> one scoped here: rather than repairing `Hmulti_window_prefixed`'s unsatisfiable `hdisH`
> side condition, the right-only hop program derives disjointness instead of assuming it.

# Scope — the k>1 window assembly (multi-piece windows with reposition hops)

**Status: SCOPE ONLY. Nothing built.**

This is the last structurally-open item between the current state and Theorem 3 for
all 46 benchmarks. It blocks 21 of them (measured: emitted-cover budget > 1 and not
all-modes-joint). It does not block the other 25.

Evidence tags: **[VERIFIED]** read in the source; **[MEASURED]** computed from emitted
data; **[INFERRED]** reasoned from definitions, not built.

---

## 1. The blocker, exactly

`Hmulti_window_prefixed` ([EnvelopeChain.lean:252](../RelCertifier/Proofs/Encoding/EnvelopeChain.lean:252))
proves the k-piece window with a reposition-hop prefix. It carries

```lean
(hdisH : ∀ h ∈ hops, Disjoint (Program.vars (h.prog domL))
    (Program.vars (clockedSeg (leftBlock fL) domL ((Side.Aux, a) : Var n) dt)))
```

and `RepoHop.prog` ([RepoPrefix.lean:356](../RelCertifier/Proofs/Encoding/RepoPrefix.lean:356)) is

```lean
def RepoHop.prog (h : RepoHop n) (domL : Formula (Var n)) : Program (Var n) :=
  Program.ode (jointSys (fun _ => Term.const 0) h.fR h.lam) (Formula.and domL h.domR)
```

The frozen-left joint system **binds every left coordinate** (derivative 0), and the
domain conjoins `domL`. So `Program.vars (h.prog domL)` always meets the left clocked
segment's vars. `hdisH` is unsatisfiable for any nonempty hop list; the theorem is
vacuous exactly where it is needed. **[VERIFIED — the deprecation note at
[EnvelopeChain.lean:568](../RelCertifier/Proofs/Encoding/EnvelopeChain.lean:568) states
this as a recorded negative finding, kept under the never-delete rule.]**

`Hmulti_window1_prefixed` (k = 1) escapes because a single piece has nothing to commute
past — `faModalB_clockedSeg_iff` applies directly, no disjointness needed. That is why
watertank went through.

## 2. Why the hypothesis is there

It feeds `multiseg_clocked`, which composes k (left piece, right response) pairs into
the k-piece window. Disjointness is the frame condition that lets each right response
commute past the left segments it is not paired with.

The requirement is real; the problem is that the hop program was given the wrong shape.

## 3. The fix direction — make hops right-only

The same disjointness, in the same position, **is already satisfiable** for the uniform
route: `emitWindows_self` ([CoverExtract.lean:84](../RelCertifier/Proofs/Encoding/CoverExtract.lean:84))
carries

```lean
(hdis : ∀ q m, Gr.modeAt q = some m →
  Disjoint (Program.vars ((Program.ode m.sys m.dom).rename (Equiv.refl (Var n))))
    (Program.vars (clockedSeg (leftBlock fL0) domL0 tg dt)))
```

and it discharges, because a right automaton mode is `⟨sys := rightBlock fR lam,
dom := domR⟩` — right-only on both the field and the domain. **[VERIFIED]**

So the hop should be stated the same way:

```lean
def RepoHop.prog' (h : RepoHop n) : Program (Var n) :=
  Program.ode (rightBlock h.fR h.lam) h.domR
```

Two facts make this look like the right move rather than a workaround:

- **It is already the shape of the final response.** The segments handed to the
  statement are `Program.ode s.2.1.sys s.2.1.dom` over `Gr`'s modes — right-only. The
  watertank instance converts to it explicitly, via `sem_rightBlock_frozen_iff`
  ([RepoPrefix.lean:415](../RelCertifier/Proofs/Encoding/RepoPrefix.lean:415)) at
  [WatertankModal.lean:335](../RelCertifier/Instances/WatertankModal.lean:335). The
  joint-with-zero-left form is an internal artifact of the coupling proof, not
  something the statement wants. **[VERIFIED]**
- **Dropping `domL` from the hop domain is sound and matches the automaton.** The right
  automaton's mode domains are right-only (`modeW q .dom := domRW`). Conjoining `domL`
  only removes hop runs; the left state is unchanged across a hop, so `domL` already
  holds. **[INFERRED]**

### What this touches

| item | file | change |
|---|---|---|
| `RepoHop.prog` | RepoPrefix.lean:356 | restate right-only (or add `prog'` + an iff) |
| `faModalB_repoPrefix` | RepoPrefix.lean | single-hop core — reprove over the new shape |
| `faModalB_repoPath` | RepoPrefix.lean:363 | induction over the hop list; follows the core |
| `static_hop_exists` | EnvelopeChain.lean:624 | zero-duration witness; simpler right-only |
| `Hmulti_window_prefixed` | EnvelopeChain.lean:252 | `hdisH` now dischargeable by the L/R side split |
| `Hmulti_window1_prefixed` | EnvelopeChain.lean:580 | same hop shape; watertank's conversion step drops out |
| `WatertankModal` | Instances/ | `seg_hopW`'s `sem_rightBlock_frozen_iff` step becomes unnecessary |

### The risk in it

`faModalB_repoPrefix`'s proof (per the S1 design) turns on the frozen-left system
keeping left coordinates constant along the hop — a consequence of the zero left field.
With a right-only block the left coordinates are not bound at all, so constancy comes
from the program mask instead. That should be easier, but the supporting replay/patch
lemmas (`sem_ode_right_patch`, `plantT_right_patch`) may be stated for the joint form
and need restating. **[INFERRED — this is where the work actually lives.]**

## 4. What k>1 needs BEYOND this lemma

Fixing `hdisH` is necessary, not sufficient.

`Hmulti_window_prefixed` takes `pieces : List (Program (Var n))` with
`hcouple : ∀ Q ∈ pieces, ∀ σ, …` — one certified coupling per piece, from every
invariant anchor. For a k-piece window the pieces are k right-mode residences, and for
the blocked benchmarks they are **not** all the same mode.

- The all-joint route already handles any k, because `emitWindows_self` answers a
  k-piece window with k **self-loop** residences in one joint-certified mode.
  **[VERIFIED — it is parametric in k]**
- For the blocked 21 the piece sequence comes from the cover's `Covered` derivation.
  **No extraction from that derivation exists**: R1 shipped only the self-loop case.
  A general `emit_from_covered` — walk the `Covered` derivation, emit the mode
  sequence with its edges — is a second piece of work, and it is the one R1 was
  originally scoped for.

### MEASURED — the extraction is NOT needed

For all **21/21** blocked benchmarks, every left window has a right mode `q*` that is
simultaneously:

- joint-certified for that window (`jointOK`),
- carrying a **declared self-loop** edge, and
- **reachable by declared edges from every other right mode**.

**[MEASURED — emitted cover flags × the right `next` lists, all 21, no exceptions.]**

So the response for a k-piece window can always be: hop prefix to `q*`, then k self-loop
residences at `q*`. No mid-window mode change, one joint verdict per (window, `q*`) pair,
reused across all k pieces (the cert is a `BoxLe` over the joint ODE — duration-agnostic).

This is exactly the shape `emitWindows_self` already produces for the k pieces, and it is
free to choose: the witness need not be the response the tool's own cover walk used, only
a legal one backed by an existing joint certificate.

Consequence: **`Hmulti_window_prefixed`'s `hdisH` is the only thing blocking the 21.**
`emit_from_covered`-style derivation walking is not on the critical path.

## 5. Order of work

1. **Fix the hop shape** (§3) — restores `Hmulti_window_prefixed` for real hop lists.
   This is the whole critical path for the 21.
2. Per-benchmark instantiation (hop path ≤2 + k self-loops; same template as watertank,
   with `k` pieces instead of one).

Piece-sequence extraction from `Covered` is **not required** — see the measurement above.
It stays worth building only if a future benchmark breaks the `q*` property.

## 6. Relation to the other open item

Existence (`HExistSegB`) is orthogonal and applies to all 46 — see the viability route
in the reading guide. The k>1 assembly does not depend on it, and vice versa.
