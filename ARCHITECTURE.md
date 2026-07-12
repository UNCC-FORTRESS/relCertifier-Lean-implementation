# Verified architecture — and the finding that reshaped it

## The finding (must be stated plainly)

For most of this project "verified certifier" meant **verified functions beside an
untrusted runner that re-implements them**. Two facts, together, were the real gap:

1. `cover_sound` (and `cover_sound_throughout`) is **parametric in the ODE domain** — it is
   a *true* theorem for *any* domain, including a guard-narrowed one. No theorem-strengthening
   prevents a wrong-domain bug.
2. The runner (`Run.lean` / `OracleAPI.lean`) re-implements the cover (`dfsCov3` + direct Z3)
   and **never invokes** the verified functions or `cover_sound`. The proofs are real (about
   real Lean functions), but they **did not govern the tool's output**.

The guard bug lived exactly in that gap: a wrong domain in the untrusted runner, with a clean
`#print axioms` the whole time. **CERTIFIED was not backed by proof.** That honest
re-characterization is the finding — "verified" must not stand unqualified until CERTIFIED
provably flows through a verified checker.

## The fix — certified-checker architecture (runner proposes, checker validates)

Standard certified-checker design (à la certified SAT/proof checkers): untrusted search,
trusted checker.

* **Runner (untrusted).** Fast `dfsCov3` + Z3 search. It only **proposes** — its output is
  data, not a verdict.
* **Verified, computable checker (`Checker.lean`).**
  * `decideCovered : ℕ → Config → Bool` — **runs** (no `noncomputable`, no classical choice
    in the function); re-validates the runner's cover derivation (budget arithmetic,
    `0 < weight`, all-successors).
  * `decideCovered_sound : decideCovered … = true → Covered G cfg` — accepting implies the
    proof-level relation.
  * `decideSegDomain (segDom evolveDom : IForm n) : Bool := decide (segDom = evolveDom)` —
    the segment's flow-certificate domain must be the **evolution** domain; a guard-narrowed
    `evolve ∧ guard` is a different `IForm`, so it returns `false`. **The guard-bug class is a
    rejection, not a false certification** (verified `#eval`: `decideSegDomain (ev∧grd) ev =
    false`). (The check is over the `ℚ`-based IR, which has `DecidableEq`; the host `Formula`
    carries `ℝ` constants and cannot.)
* **`check_sound`** — the connection:
  ```
  check_sound (cert : CoverCert G g) (hchk : decideCovered G fuel cfg = true)
              (hinit : InvHolds g ν) : CoexecInvThroughout G g cfg ν
    := cover_sound_throughout G g cert cfg ν (decideCovered_sound … hchk) hinit
  ```
  `check_sound` is **defined as** an application of `cover_sound_throughout` — it cannot exist
  without it (kernel-enforced dependency, not a comment). Accepting (`decideCovered = true`)
  provably implies the semantic ∀∃-throughout invariant. A runner that proposes a bad
  derivation makes `decideCovered` return `false`, never reaching this conclusion.

## The semantic target (`cover_sound_throughout`, now load-bearing)

* `CoexecInvThroughout G g cfg ν := ∀ ω, RightReach G cfg ν ω → InvHolds g ω` — the
  **time-coupled** (left rate 1, right rate λ, via `jointSys`) co-execution, invariant
  **throughout** (every trajectory instant, not just endpoints).
* `sem_ode_prefix` — the ODE semantics is **prefix-closed**: every intermediate point `Φ t` of
  a segment is itself ODE-reachable, so the `RightReach`-reachable set already contains every
  trajectory point. Hence the endpoint-style quantifier of `CoexecInvThroughout` **is**
  "throughout" — provided the segment domain is the evolution domain (on a guard-narrowed
  domain the real flow leaves ψ and is not a `sem (ode sys ψ)` execution at all).
* `cover_sound_throughout : Covered G cfg → InvHolds g ν → CoexecInvThroughout G g cfg ν`.
  (a)–(d): **(b)** matching connecting states — `RightReach.jump` shares the state; **(a)**
  positive durations — the budget structure; **(d)** whole-evolution-domain preservation — the
  conclusion itself (via `sem_ode_prefix`); **(c)** left-stays-in-`mL` — explicit
  well-formedness (the cover fixes `mL`, so the joint field uses `fL` throughout; when the
  left is modeled separately it is an explicit hypothesis, surfaced, not silently assumed).

dL-rel's `faShape` is ∀∃ but over the **independent-product** biprogram, **endpoint-only** —
it cannot express the time-coupled, throughout co-execution the cover builds.
`CoexecInvThroughout` is that missing semantic object; it, not `faShape`, is the operative
target in `check_sound`.

`#print axioms` on `check_sound`, `decideCovered_sound`, `cover_sound_throughout`,
`sem_ode_prefix`: `propext, Classical.choice, Quot.sound` only.

## Residual trusted base (the honest TCB)

Once CERTIFIED flows through `check_sound`:

* **Parser** — reads the L/R models and sets each segment's `dom` = the model's **evolution
  domain** (irreducible input trust). But a wrong `dom` now makes `decideSegDomain`/the
  domain hypothesis of `check_sound` **reject**, not falsely certify — so parser bugs of the
  domain-narrowing class cause *declines*, never false CERTIFIED.
* **Z3 `unsat`** — the one solver leaf (`z3_unsat_sound`).
* **NOT trusted anymore:** the runner's `dfsCov3` search. As of Step 4 it does not even gate
  the verdict — `coverMode` certifies solely from the verified `decideCovered` over the
  coverable-fixpoint graph. `dfsCov3` remains only as a dead/aux search path (removable).

## Status (precise — no overclaim)

* **Proven and executable:** the verified checker — `decideCovered` (computable, tested),
  `decideCovered_sound`, `check_sound` (cites `cover_sound_throughout`), `decideSegDomain`
  (guard-narrowing → reject, tested), `cover_sound_throughout` + `sem_ode_prefix` (the
  throughout semantic core). Axioms clean (`propext, Classical.choice, Quot.sound`).

### Step 4 — the executable's CERTIFIED now flows through `decideCovered`

`OracleAPI.coverMode` no longer certifies from `dfsCov3`. It:

1. Z3-checks each segment on the **evolution-domain** query the tool constructs itself
   (`segParts` builds `domL ∧ domR` from `mL.evolve`/`mR.evolve` — **checker-constructed, not
   runner-labeled**; a guard-narrowed query would require `segParts` to read `.guard`, which
   it does not).
2. Computes the **coverable fixpoint** `coverableSet` — the greatest set of right modes that
   certify AND whose declared successors are all coverable. **Every mode in it certifies, and
   (by the fixpoint) no real edge leaves it** — so a `SearchGraph` over it admits a full
   `CoverCert` (`check_sound`'s precondition) with no dropped obligation.
3. Builds that `SearchGraph (Var n)` and calls the **verified `decideCovered`**. CERTIFIED iff
   `decideCovered = true`. `decideCovered_sound → Covered`; `CoverCert` from (1); `check_sound`
   ⟹ the ∀∃-throughout invariant. A runner/search bug can only make `decideCovered` reject.

**Result (this Step-4 checkpoint): 38/46 CERTIFIED, all backed by `check_sound`; deterministic.**
(Current suite: **46/47 CERTIFIED**, 1 inconclusive-Z3 ERROR — see README; the recovery to 46 was
sound spec/cover work, not an architecture change.) The CoverCert-discharge junction is
checker-constructed (the tool builds the evolution-domain query from `dom`; Z3 validates the tool's
query, over exactly the domain `check_sound`'s conclusion quantifies).

### The second fidelity bug: `Covered` did not implement Definition 4's base case

A first wiring of Step 4 gave 31/46, not 38 — seven **single-sync** covers (`watertank`,
`arm_fidelity_*`, `plant_fan_*`, `arm_chain_rung3`, `refinement_ladder_rover_rung2c_6dof`) were
declined. Root cause: the mechanized `Covered`/`RightReach` **did not match the paper's
Definition 4** — the same *Lean-object-≠-paper-object* class as the guard bug, not a
completeness knob.

Definition 4 has two cases: a **base case** (joint certified ∧ `B ≤ w(mR)` → the single
residence closes the budget, **terminate — do not recurse into successors**) and a **successor
case**. The old `Covered` had only `closed : Covered ⟨q,0⟩` (base at `B = 0`) and
`RightReach.jump` gated on `0 < B`. So a single-segment cover could not terminate at
`B ≤ w`; instead `RightReach.evolve` (ungated) kept evolving into a closed-leaf successor the
base case should have excluded, forcing `segPres` on modes outside the residence. The missing
`0 < B`/`B ≤ w` termination *was* Definition 4's base case, absent from the mechanization.

**The correction (make Lean `Covered` = paper `Covered`):**

* `Covered.base m hm (hle : B ≤ m.weight)` — budget closed, terminate; **no** successor
  obligation. `Covered.step m hm (hlt : m.weight < B) (∀ retained succ, covered at B - w)`.
* `RightReach.jump` gated on `m.weight < B` (Def-4 step condition), so a `base` config admits
  no jump — its right response is a *prefix of the one certified segment* (`evolve`/`refl`),
  never entering a successor. `cover_sound` re-proven on this structure (the jump case shows
  the config must be `step`, `base` contradicting the gate).
* `decideCovered` is now literally Def 4's two-case function: `if B ≤ m.weight then true` (base)
  `else (retainedSucc).all (decideCovered … (B - m.weight))` (step). `decideCovered_sound`
  re-proven.
* Runtime: `B = ⌈εL/δL⌉` segments, weight 1; `coverVisit` runs Def 4 (certified-aware) to get
  the visited set; the `SearchGraph` is built over exactly it. A base cover visits only the
  start ⟹ `CoverCert` ranges over `{start}` ⟹ closed-leaf successors need not certify. By Def 4
  a `step` node's successors are all visited ⟹ no real edge dropped.

`#eval`: `decideCovered` accepts a base config (`B ≤ weight`) **without** examining an
uncertified successor; the 7 recover; all 38 flow through `check_sound`; axioms unchanged
(`propext, Classical.choice, Quot.sound`); guard-narrowing still `decideSegDomain = false`.

**This is a fidelity correction, documented as such — not "optional completeness."** The Lean
`Covered` now transcribes Definition 4 directly, base case included.
