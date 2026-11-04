/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `cover_sound` over the co-execution semantics: the ∀∃-throughout reading

`cover_sound` (in `Cover.lean`) speaks about the relations `Covered` and `RightReach`,
parametric in each mode's ODE domain. This file states what that conclusion means for the
co-execution semantics `⟦·⟧`: the invariant holds at every point of every segment, provided
the segment domain is the evolution domain.

## Time coupling versus dL-rel's `faShape`

dL-rel's `faShape α β ψ = rbox (biprog α ?⊤) (rdiamond (biprog ?⊤ β) ψ)` is a ∀∃ modality over
`biprog`, the independent product (`α` on the left, `β` on the right, no coupling), and it
constrains `ψ` only at the endpoints `(νL, μR)`. A joint segment instead runs the joint product
program of Eq. (14): the left at rate 1, the right at stretch `λ`, through `jointSys`, and the
flow certificate (Definition 5) keeps the invariant at every instant of the run.

## The co-execution and "throughout"

The joint field `jointSys fL fR λ` (`Lᵢ' = fL i`, `Rᵢ' = λ·fR i`) is the time coupling. A
co-execution segment is `Program.sem (Program.ode jointSys ψ)` with `ψ` the evolution domain
(`evolveL ∧ evolveR`), which holds throughout the segment. The assembled right response is
`RightReach`, a finite concatenation of certified segments and guard-enabled jumps.

**Key fact (`sem_ode_prefix`):** the ODE semantics is prefix-closed: every intermediate point
`Φ t` of a segment reaching `μ` is itself ODE-reachable from `ν`. So the `RightReach`-reachable
states contain every trajectory point, and the endpoint quantifier of `cover_sound`
(`∀ ω, RightReach … → InvHolds ω`) is "throughout", provided the segment domain is the evolution
domain. On a domain narrowed to a guard, the real flow can leave `ψ` and is then not a
`Program.sem (ode sys ψ)` execution, so the theorem says nothing about it; this is why the
segment domain must be the evolution domain.
-/
import RelCertifier.Checker.Cover

namespace RelCertifier

open DL Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Step 1 — the ∀∃-throughout co-execution modality (semantic definition) -/

/-- **The co-execution invariant (∀∃-throughout).** The invariant `g ≤ 0` holds at every
state the assembled right response can reach from `ν`, through segments (time-coupled joint
ODE flow on the evolution domain) and guard-enabled jumps. Because the ODE semantics is
prefix-closed (`sem_ode_prefix`), "every reachable state" includes every point of every segment
trajectory, so the invariant holds throughout the co-execution, not only at segment
endpoints. -/
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

/-! ## Step 2 — cover soundness, throughout

The conditions that make the co-execution a faithful matching, and where each is discharged:
* **(a) budget** — `RightReach.jump` fires only when `m.weight < B` (the continue case of
  Definition 8), and each covering step strictly decreases `B` (`cover_budget_decreases`); a
  zero-duration `evolve` contributes only its own start point. *Structural.*
* **(b) matching connecting states** — `RightReach.jump` shares the state `μ`: a segment's
  end state is the next segment's start state. *Definitional.*
* **(c) the left stays in `mL` during its cycle** — the cover fixes the left mode `mL`, so the
  co-execution uses `fL` (the field of `mL`) throughout. A left mode change happens only
  between cycles, where Theorem 2 (Composition) and the handoff condition Eq. (13) take over.
* **(d) invariant over the whole evolution domain** — the conclusion is `CoexecInvThroughout`,
  which (via `sem_ode_prefix`) quantifies over every trajectory point on the segment domain.
  With that domain the evolution domain, this is preservation over the whole domain; a domain
  narrowed to a guard cannot satisfy it (the real flow is not a `sem (ode sys guard)` run).
-/

/-- **`cover_sound_throughout`.** If the configuration is covered and the composed certificate
holds (each `segPres` a `BoxLe` on the mode's evolution domain), then from an
invariant-satisfying entry the invariant holds throughout the assembled co-execution: at every
point of every segment trajectory, across the whole finite concatenation. It is `cover_sound`
restated as `CoexecInvThroughout`.

`(d)` is the conclusion `CoexecInvThroughout` itself; `(b)` is `RightReach.jump`'s shared
state; `(a)` is the budget structure; `(c)` holds by construction, since the cover fixes `mL`
and the joint field uses `fL` throughout. -/
theorem cover_sound_throughout (G : SearchGraph V) (g : Term V) (cert : CoverCert G g)
    (cfg : Config) (ν : State V) (hcov : Covered G cfg) (hinit : InvHolds g ν) :
    CoexecInvThroughout G g cfg ν :=
  fun ω hreach => cover_sound G g cert cfg ν ω hcov hreach hinit

end RelCertifier
