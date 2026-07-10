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
* **NOT trusted anymore:** the runner's `dfsCov3` search — it only proposes; the verified
  `decideCovered` / `check_sound` validate.

## Status (precise — no overclaim)

* **Proven and executable:** the verified checker — `decideCovered` (computable, tested),
  `decideCovered_sound`, `check_sound` (cites `cover_sound_throughout`), `decideSegDomain`
  (guard-narrowing → reject, tested), `cover_sound_throughout` + `sem_ode_prefix` (the
  throughout semantic core). Axioms clean.
* **Remaining integration:** routing the *executable tool's* CERTIFIED fully through
  `decideCovered` — the runner must build the abstract `SearchGraph`/budget from the parsed
  model and call `decideCovered` in place of the structural half of `dfsCov3`, discharging the
  per-mode `CoverCert` from the evolution-domain Z3 verdicts. Until that wiring lands, the
  running tool's CERTIFIED is still the untrusted runner's; the verified checker exists and is
  the mechanism, and this is stated rather than glossed.
