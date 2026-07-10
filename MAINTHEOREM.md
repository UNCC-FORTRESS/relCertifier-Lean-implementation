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

## Remaining for the full B=1 theorem — two real constructions (each gate-first)

1. **Lockstep ∀∃ loop invariant** `[L*]⟨R*⟩ϕ`. No library rule (`faModal_loopStar/N` are
   right-only; `sat_box_star_of_inv` is single-program). `seqL`/`seqR` advance the two sides
   *separately*; coupling them into lockstep (`[L^k]⟨R^k⟩ϕ`, then star-lift) is the construction,
   where a left/right iteration-count desync would hide. **Design the statement first.**
2. **Reification** `SearchGraph`/`decideCovered` → concrete `L*`/`R*` programs — the deferred
   structural bridge (the "third-instance" abstract-object surface).

## Honest status line

The two hardest junctions of the paper-∀∃ chain are mechanized and axioms-clean (the
domain-restricted base rule and the encoding bridge), and the **atomic single-sync relational
guarantee is proven end-to-end** (`flow-cert ⟹ paper-∀∃` for one segment pair). This is **not
yet** "the tool's `CERTIFIED` = the paper's ∀∃ for the 21 benchmarks" — that waits on the
lockstep loop + the reification. Stated at its true scope: the chain's endpoints and base rule
are proven; the single-sync automaton assembly is the remaining phase.
