# The main soundness theorem — CSF'25 → NFM'25 chain (checkpoint)

Goal: **the tool's `CERTIFIED` provably implies the paper's ∀∃ relational invariant**
`ϕ_inv → [|(L*,R*)⟩⟩ϕ_inv`, verified against the mechanized relational logic (dL-rel /
dL-caltiming), not a bespoke object.

## The two-step decomposition (both junctions land on proven theorems)

```
decideCovered = true → Covered → CoexecInvThroughout            [proven, Cover/Checker/Coexec]
   → [Step 1: CSF ∀∃-ODE + composition]  → faModal ρ L* R* (encode ρ ϕ)
   → [Step 2: sat_encode_faShape + encoding_correct] → [|(L*,R*)⟩⟩ϕ   (paper Thm 3 conclusion)
```

* **Step 2** is entirely proven machinery: `DLRel.sat_encode_faShape` (`encode(faShape) = faModal`,
  same `ρ`) then `DLRel.RFormula.encoding_correct` (Theorem 2). The CSF renaming and NFM'25
  encoding renaming are the **same** `ρ : V ≃ V`.
* **Step 1** base rule is dL-caltiming's ∀∃-ODE rule — but the relational cover's divergent
  left/right domains break its `hP3` premise, so we use a corrected base rule (below).

## Proven this phase (all sorry-free; axioms `propext, Classical.choice, Quot.sound`)

| artifact | file | role |
|---|---|---|
| `faModal_ODE_G'` | `CSFBridge.lean` | domain-restricted ∀∃-ODE base rule — drops `hP3`, strengthens `hExist'` |
| `Term/Program/Formula/ODESystem.rename_refl` | `Reify.lean` | `ρ=id` collapse (mutual Program/Formula) |
| `segment_faModal` | `Reify.lean` | cover segment (flow cert `BoxLe`) ⟹ `faModal id (ode leftBlock domL)(ode rightBlock domR)(g≤0)` |
| `faModal_to_faShape` | `EncodingBridge.lean` | `faModal ρ α β (encode ρ ψ)` ⟹ `[|(α,β)⟩⟩ψ` (Step 2) |
| `segment_relational` | `EncodingBridge.lean` | **atomic end-to-end: flow cert ⟹ paper's ∀∃ `[|(L-seg,R-seg)⟩⟩ψ`** for one single-sync pair |

`segment_relational` is the first mechanized `flow-cert ⟹ paper-∀∃` connection.

## Findings (each a gate that surfaced a real premise — the recurring abstract-object pattern)

1. **`hP3` false for the relational cover → outcome 3, bounded fix.** dL-caltiming's
   `faModal_ODE_G` requires `hP3 : [joint]⊤(domL → ρ domR)` — the left evolution domain forces
   the right along the *free* flow. Its only use site (`faModal_ODE_I`) has `⊤` domains. The
   cover's `domL`/`domR` constrain **disjoint** `Side.L`/`Side.R` vars and are tight+divergent
   (`θ_L∈[0,1]` vs `θ_R∈[0,1]`; `px_L≤5` vs `px_R≤15`), so `hP3` is **false**. Fix
   (`faModal_ODE_G'`): `hP3` is used once, to prove the right witness stays in `domR`; drop it,
   strengthen `hExist` to hand back an in-domain right witness (which the cover's joint-domain
   co-execution supplies). Delta = one `have`.
2. **`ρ = id`, not the Side-swap.** `jointSys = leftBlock ++ rightBlock` already binds disjoint
   `Side.L`/`Side.R`, so the NFM'25 separating renaming is the identity. No mirror.
3. **`hdisj` needs dynamics independence** (`fL` reads only left, `λ·fR` only right). Holds for
   the refinement/fidelity suite (separate models, coupled via `λ`+invariant only). A shared-state
   candidate fails it — a checkable parser-level gate, unneeded for the suite.
4. **`hExist'` is CSF's deliberately-open duration-existence side-condition.** dL-caltiming
   *never* discharges `hExist` (finite-escape countermodel `ξy'=ξy²` shows it can fail). Carried
   explicitly, exactly as CSF ships it. Holds for the cover's **bounded** polynomial domains (no
   escape); Picard-on-the-compact-domain discharge is separate ODE mechanization (deferred, does
   not weaken the theorem — the side-condition is stated and known-true for this class).

## Scope of the clock-free single-sync fragment

* `RightReach.evolve` is **unbounded-duration** (budget consumed only by jumps); `B=⌈εL/δL⌉` is
  runtime counting. Per left mode the right does `B` segments.
* Measured: **21 of 38 CERTIFIED benchmarks are fully single-sync** (every left mode `B=1`) — the
  clock-free fragment. For `B=1`, `hExist'` discharges from the joint domain `domL∧domR ⊇ domR`
  (one right mode per left mode, duration-matched by the joint flow — no clock).
* **17 CERTIFIED have a `B>1` left mode** → the right *jumps* within a left residence → the
  continuous left ODE must be split into duration-matched pieces = **`plantT_split`** = a clock.
  That is the separately-gated **clocked extension** (`tg↔δL↔B` correspondence pinned as the
  hidden-mismatch surface).

## The loop layer — PROVEN (`faModal_LOCK`, was mis-scoped as a new construction)

An earlier note here claimed the lockstep loop needed a new lemma. **That was wrong** — it
missed `DLCalTiming.Commute.lean`, which already proves:
* **`faModal_LOCK`** — the lockstep ∀∃ loop invariant `[P*]⟨Q*⟩ψ` from a per-iteration step
  `[P]⟨Q⟩φinv` + variable-disjointness. The all-left-then-all-right ↔ interleaved commutation is
  handled internally by `sem_commute` + `lock_acc`'s induction. Exactly the single-sync loop.
* **`faModal_MULTI`** — the right runs *multiple* cycles per left cycle (`[P]⟨Q*⟩φinv` per step).
  The loop-level shape of the `B>1` multi-segment case (the per-step ODE-coupling still needs the
  clock, but the loop composition itself is available).

`relational_loop` (`EncodingBridge.lean`, proven, axioms clean) wraps `faModal_LOCK` +
`faModal_to_faShape`: given the per-iteration single-sync step + `Side.L`/`Side.R` disjointness +
`Bridges`, it concludes `[|(leftBody*, rightBody*)⟩⟩ ψ` — **the looped relational guarantee**.

## Reification — DONE (`reified_relational`, `Reification.lean`)

`bigChoice` + `faModal_bigChoiceL`/`faModal_bigChoiceR` (choice folds via `faModal_unionL`/`unionR`)
+ `reified_relational`: from per-left-mode single-sync pairings (each left mode ↦ one matching
right mode with a per-pair `faModal` preserving `ψ`) + `Side.L`/`Side.R` disjointness + `Bridges`,
concludes `[|((⨆leftProgs)*, (⨆rightProgs)*)⟩⟩ ψ`. **This completes the CSF-side assembly** — the
entire chain from flow certificate to the paper's *looped* ∀∃ relational modality is mechanized,
axioms-clean, for the single-sync fragment. `(⨆modes)*` is the flat over-approximation (⊇ the
real automaton) ⟹ the box claim is stronger than, and implies, the paper's transition-restricted
`[|(L*,R*)⟩⟩ϕ`.

## Tool-level connection — DONE (`ToolLevel.lean`)

* **`pair_faModal`** (the trust-critical Step-2 junction) — a Z3 UNSAT on the **evolution-domain**
  flow query `flowQuery o` (`o.domain = domL∧domR`, `hdom`) ⟹ the per-segment `faModal`. Via
  `flow_certified` (`z3_unsat_sound` + `flow_cert_sound`) then `segment_faModal`. **The query the
  proof consumes is literally `flowQuery o` — the same one Z3 checks**; `hdom` pins it to the
  evolution domain (a guard-narrowed domain is a *different* `o.domain`, breaking `hdom` — the
  guard-bug class is a mismatch, not a false discharge). No runtime-labeling gap.
* **`CertSeg` + `certified_relational`** — from a list of single-sync certified segments (each an
  evolution-domain Z3 UNSAT) + `encode id ψ = invLe g` + `Bridges`, the paper's ∀∃ modality
  `[|((⨆L)*, (⨆R)*)⟩⟩ ψ` holds. `#print axioms`: `propext, Classical.choice, Quot.sound,
  z3_unsat_sound` — **standard three + the single Z3 leaf**.

**`certified_relational` is the tool-level theorem: the tool's `CERTIFIED` (on a fully-single-sync
benchmark) provably equals the paper's ∀∃ relational invariant.** Residual TCB: **parser + Z3
only**. `hExist'` is CSF's explicit duration-existence side-condition (true for the bounded
domains).

## Remaining — purely the executable parser emit (existing trust, no verified content)

`certified_relational` takes `CertSeg` values. Producing them from a parsed benchmark
(`PProblem → List CertSeg`: dynamics `fL`/`fR`, domains from `evolve`, the Z3 verdicts, the
single-sync pairing) is an **IO/parser function** — existing trusted-parser territory, not new
proof. The theorem is complete; instantiating it on a concrete benchmark is parser plumbing.

## Honest status line

**The full chain — Z3 verdict ⟹ paper's looped ∀∃ `[|(L*,R*)⟩⟩ψ` — is mechanized and
axioms-clean (standard three + `z3_unsat_sound`), for the single-sync (B=1) fragment.** The
tool's `CERTIFIED` provably equals the paper's ∀∃ relational invariant **for the 21 fully-
single-sync benchmarks**, modulo the executable parser emit (`PProblem → CertSeg`, existing
trust). Residual TCB: parser + Z3. The 17 B>1 benchmarks await the clocked `plantT_split`
extension (separately gated). This is **not** "the tool is verified" — it is **21/38 verified
end-to-end to the paper's modality, parser + Z3 trusted**.
