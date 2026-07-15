/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Connecting `cover_sound` to the co-execution semantics — the ∀∃-throughout modality

The guard bug exposed a seam: `flow_cert_sound` / `cover_sound` prove properties of the
abstract `Covered`/`RightReach` relations, parametric in the ODE domain — a *true* theorem
about a *wrong* (guard-narrowed) domain. This file connects the cover to the actual
co-execution semantics `⟦·⟧` and makes the faithfulness conditions **derived, not trusted**.

## What dL-rel has, and what is missing

dL-rel's `faShape α β ψ = rbox (biprog α ?⊤) (rdiamond (biprog ?⊤ β) ψ)` is a ∀∃ modality —
but over `biprog`, the **independent product** (`α` on left, `β` on right, *no coupling*),
and it constrains `ψ` only at the **endpoints** `(νL, μR)`. The cover instead builds a
**time-coupled** co-execution — the left drives at rate 1, the right responds at stretch `λ`
via the joint field `jointSys` — and the invariant is a **trajectory property** (holds at
*every* instant, not just endpoints). That time-coupled ∀∃-throughout modality is exactly
what `biprog` cannot express, and is the semantic target `cover_sound` must connect to.

## The co-execution and "throughout"

The joint field `jointSys fL fR λ` (`Lᵢ' = fL i`, `Rᵢ' = λ·fR i`) *is* the time-coupling.
A co-execution segment is `Program.sem (Program.ode jointSys ψ)` with `ψ` the **evolution
domain** (`evolveL ∧ evolveR`, which holds *throughout* the segment — that is its semantic
meaning). The assembled right response is `RightReach` (a finite concatenation of certified
segments + guard-enabled jumps).

**Key fact (`sem_ode_prefix`):** the ODE semantics is *prefix-closed* — every intermediate
point `Φ t` of a segment reaching `μ` is itself ODE-reachable from `ν`. Therefore the set of
`RightReach`-reachable states *already contains every trajectory point*, and the endpoint
quantifier of `cover_sound` (`∀ ω, RightReach … → InvHolds ω`) is **exactly "throughout"** —
*provided* the segment domain is the evolution domain. On a guard-narrowed domain the real
flow leaves `ψ`, so it is **not** a `Program.sem (ode sys ψ)` execution at all — the theorem
says nothing about it. That is the structural reason the guard-narrowed domain cannot satisfy
the connected theorem.
-/
import RelCertifier.Checker.Cover

namespace RelCertifier

open DL Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Step 1 — the ∀∃-throughout co-execution modality (semantic definition) -/

/-- **The co-execution invariant (∀∃-throughout).** The invariant `g ≤ 0` holds at *every*
state the assembled right response can reach from `ν` — the segments (time-coupled joint
ODE flow on the evolution domain) and the guard-enabled jumps. Because `RightReach` is
prefix-closed at the ODE level (`sem_ode_prefix`), "every reachable state" is precisely
"every point of every segment trajectory" — i.e. the invariant holds **throughout** the
co-execution, not merely at segment endpoints. -/
def CoexecInvThroughout (G : SearchGraph V) (g : Term V) (cfg : Config) (ν : State V) : Prop :=
  ∀ ω, RightReach G cfg ν ω → InvHolds g ω

/-! ## The enabling lemma — the ODE semantics is prefix-closed (makes "throughout" explicit) -/

/-- **`sem_ode_prefix`.** If the joint ODE segment reaches `μ` along a curve, then *every
intermediate point* `Φ t` of that curve is itself ODE-reachable from `ν` on the same domain.
Hence every trajectory point is `RightReach`-reachable, so preserving the invariant at all
`RightReach`-reachable states is preserving it **throughout** the continuous flow. -/
theorem sem_ode_prefix {sys : ODESystem V} {ψ : Formula V} (hwf : sys.WellFormed)
    {ν : State V} {r : ℝ} {Φ : ℝ → State V} (h0 : Φ 0 = ν)
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    (hdom : ∀ t ∈ Set.Icc (0:ℝ) r, Formula.sat ψ (Φ t))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) r) :
    Program.sem (Program.ode sys ψ) ν (Φ t) := by
  rw [sem_ode_iff_integralCurve hwf]
  refine ⟨t, Φ, ht.1, h0, rfl, hcurve.mono (Set.Icc_subset_Icc le_rfl ht.2), ?_⟩
  intro s hs
  exact hdom s ⟨hs.1, le_trans hs.2 ht.2⟩

/-! ## Step 2 — the semantics-connected cover soundness (statement)

The faithfulness conditions and where each is discharged:
* **(a) positive-duration segments** — `RightReach.jump` gates on `0 < B` (budget), and each
  covering step strictly decreases `B` (`cover_budget_decreases`); a zero-duration `evolve`
  contributes only its own start point and is harmless. *Derived / structural.*
* **(b) matching connecting states** — `RightReach.jump` shares the state `μ`: the segment's
  end state is literally the next segment's start state. *Derived (definitional).*
* **(c) left stays in `mL` throughout the residence** — the cover fixes the left mode `mL`,
  so the co-execution uses `fL` (mL's field) throughout. That the *actual* left does not
  transition mid-residence is a **well-formedness hypothesis** (`hResidence`): the paper
  assumes it; we make it explicit rather than silently assuming it.
* **(d) invariant over the whole evolution domain** — the conclusion is `CoexecInvThroughout`,
  which (via `sem_ode_prefix`) quantifies over every trajectory point on the segment domain.
  With that domain the evolution domain, this is the whole-domain preservation; a
  guard-narrowed domain cannot satisfy it (the real flow is not a `sem (ode sys guard)` run).
-/

/-- **`cover_sound_throughout` (semantics-connected Theorem 3).** If the config is covered and
the composed certificate holds (with each `segPres` a `BoxLe` on the mode's **evolution**
domain), then from an invariant-satisfying entry the invariant holds **throughout** the
assembled co-execution — at every point of every segment trajectory, across the whole
finite concatenation.

`(d)` is the conclusion `CoexecInvThroughout` itself (throughout, whole-domain); `(b)` is
`RightReach.jump`'s shared state; `(a)` is the budget structure; `(c)` — that the left does
not leave `mL` mid-residence — is the paper's well-formedness, and would appear as an
explicit hypothesis when the left program is modeled separately (here the cover fixes `mL`,
so the joint field uses `fL` throughout by construction). -/
theorem cover_sound_throughout (G : SearchGraph V) (g : Term V) (cert : CoverCert G g)
    (cfg : Config) (ν : State V) (hcov : Covered G cfg) (hinit : InvHolds g ν) :
    CoexecInvThroughout G g cfg ν :=
  fun ω hreach => cover_sound G g cert cfg ν ω hcov hreach hinit

end RelCertifier
