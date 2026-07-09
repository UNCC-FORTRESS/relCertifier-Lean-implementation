/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

Stage 2 — the verified non-connection certificate (Nagumo forward-invariance barrier).

Functionality target: the Python relCertifier.v1 non-connection pruning
(`test_two_edge_graph/barrier_reach.py`, paper §V.A). A declared right transition
`qR → qR'` is pruned when its successor guard `x OP c` is scalar and two Z3 checks
both pass:
  (a) source-side: no valid source state already satisfies the guard;
  (b) flow-away on the threshold: the right flow moves `x` off the guard.

If both hold, the safe side is forward-invariant ⟹ the guard is never reached ⟹ the
edge cannot fire ⟹ prune. One-sided: pruned only when both UNSAT.

## Soundness route (the Stage-2 analogue of the Stage-1 finding)

Python's check (b) asserts `evolve ∧ x=c ∧ ẋ>0` UNSAT, i.e. `ẋ ≤ 0` on the threshold
`{x = c}` **only** — a boundary-only non-strict check, the same shape dL-lean proves
unsound in general (`nonstrict_boundary_insufficient`, the `t²` counterexample). A
scalar-threshold guard has regular boundary (`∇(x−c) = eₓ ≠ 0`), so the pruning is
*mathematically* sound, but dL-lean cannot cite it without the missing subtangency
lemma. The design doc itself says "strictly away".

So the verified barrier takes the **strict route**: `barrierCheck = domain ∧ g=0 ∧
ẋ≥0` UNSAT ⟹ `ẋ < 0` on the threshold ⟹ dL-lean `DI_strict`. Boundary-shaped like
Python, strict like the design doc, sound, no new axiom. It declines only the
measure-zero case `ẋ = 0` exactly on the threshold, where Python's non-strict check
would (unsoundly, in general) prune.

Scope: scalar-threshold guards only; non-scalar guards conservatively retained
(incompleteness, not unsoundness). The barrier proves the guard's **strict** side
`{g > 0}` unreachable; a closed guard `x ≥ c` needs boundary exclusion (retained).
-/
import RelCertifier.FlowCert

namespace RelCertifier

open DL

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Lie derivative along an arbitrary ODE system (generalises Stage-1 `lieDeriv`) -/

/-- Syntactic Lie derivative of `g` along `sys`: `Σ_{(v,θ)∈sys} ∂g/∂v · θ`.
The non-connection barrier is left-independent, so `sys` is the right flow alone
(left variables absent from `sys` ⟹ held fixed by `odeField`). -/
def lieAlong (g : Term V) (sys : ODESystem V) : Term V :=
  sumTerm (sys.map (fun p => Term.binop .mul (tderiv g p.1) p.2))

/-- `lieAlong` denotes dL-lean's semantic `Lie`. Cites `tderiv_fderiv`. -/
theorem lieAlong_correct (g : Term V) (sys : ODESystem V) (ω : State V) :
    Term.eval (lieAlong g sys) ω = Lie sys (fun ν => Term.eval g ν) ω := by
  rw [lieAlong, eval_sumTerm, Lie, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp [Term.eval, AOp.interp, tderiv_fderiv, Function.comp_def]

/-! ## The non-connection obligation and its two checks -/

/-- A non-connection obligation for a declared right transition `qR → qR'`.
* `g`      — safe-side term; the invariant maintained is `g ≤ 0`, and the successor
             guard is `{g > 0}` (built scalar via `scalarUpper`/`scalarLower`).
* `guard`  — the successor guard formula `G` to prove unreachable.
* `sysR`   — the right flow (an `ODESystem V`; left vars absent ⟹ held fixed).
* `domain` — the right evolution domain `ψ`.
* `source` — the entry over-approximation of `qR` (its guard ∧ evolve), where the
             co-evolution starts. -/
structure NonConnObligation (V : Type*) where
  g      : Term V
  guard  : Formula V
  sysR   : ODESystem V
  domain : Formula V
  source : Formula V

/-- **Check (a), source-side.** `source ∧ guard`. UNSAT ⟹ no source state satisfies
the guard ⟹ the co-evolution starts strictly safe (`g ≤ 0` at entry). -/
def sourceCheck (o : NonConnObligation V) : Formula V :=
  Formula.and o.source o.guard

/-- **Check (b), flow-away on the threshold (strict route).** `domain ∧ g=0 ∧ ẋ≥0`.
UNSAT ⟹ `ẋ < 0` on `{g=0} ∩ domain` — the strict boundary hypothesis of `DI_strict`
(`ẋ = lieAlong g sysR` denotes `Lie sysR ⟦g⟧`). -/
def barrierCheck (o : NonConnObligation V) : Formula V :=
  Formula.and o.domain
    (Formula.and (Formula.cmp .eq o.g (Term.const 0))
      (Formula.cmp .ge (lieAlong o.g o.sysR) (Term.const 0)))

/-! ## Non-connection soundness -/

/-- **Non-connection certificate soundness.** If both checks are UNSAT (and the
guard is exactly the strict super-level `{g > 0}` of the safe-side term), then from
any entry state the successor guard is unreachable along the right co-evolution: no
represented execution reaches a state satisfying `guard`.

Cites dL-lean `DI_strict`: `sourceCheck` UNSAT gives `g ≤ 0` initially, `barrierCheck`
UNSAT (via `lieAlong_correct`) gives `Lie < 0` on `{g=0} ∩ domain`, so `g ≤ 0` is
forward-invariant (time-unbounded ⟹ any number of right cycles), hence `guard`
(`= {g>0}`) never holds. The single trusted leaf is the Z3 UNSAT verdicts. -/
theorem nonconn_sound (o : NonConnObligation V)
    (hwf : o.sysR.WellFormed)
    (hlink : ∀ ω, Formula.sat o.guard ω ↔ 0 < Term.eval o.g ω)
    {ν : State V} (hν : Formula.sat o.source ν)
    (hsrc : ∀ σ, ¬ Formula.sat (sourceCheck o) σ)
    (hbar : ∀ σ, ¬ Formula.sat (barrierCheck o) σ) :
    ∀ ω, Program.sem (Program.ode o.sysR o.domain) ν ω → ¬ Formula.sat o.guard ω := by
  -- entry is strictly safe: g ≤ 0 at ν
  have hinit : Term.eval o.g ν ≤ 0 := by
    by_contra h
    rw [not_le] at h
    exact hsrc ν ⟨hν, (hlink ν).mpr h⟩
  have hg : Differentiable ℝ (fun ω => Term.eval o.g ω) := term_differentiable o.g
  -- strict flow-away on the threshold: Lie < 0 on {g=0} ∩ domain
  have hbnd : ∀ x, Formula.sat o.domain x → (fun ω => Term.eval o.g ω) x = 0 →
      Lie o.sysR (fun ω => Term.eval o.g ω) x < 0 := by
    intro x hx hg0
    rw [← lieAlong_correct]
    by_contra h
    rw [not_lt] at h
    exact hbar x ⟨hx, hg0, h⟩
  have hbox := DI_strict hwf hg hbnd hinit
  intro ω hrun
  rw [hlink ω, not_lt]
  exact hbox ω hrun

/-! ## Scalar-threshold guard builders (the parser will target these) -/

/-- Upper scalar guard `x > c`: safe side `g = x − c ≤ 0`, guard `{g > 0}`. -/
def scalarUpper (x : V) (c : ℝ) (sysR : ODESystem V) (domain source : Formula V) :
    NonConnObligation V :=
  { g := Term.binop .sub (Term.var x) (Term.const c)
    guard := Formula.cmp .gt (Term.var x) (Term.const c)
    sysR := sysR, domain := domain, source := source }

/-- The `guard = {g > 0}` link for an upper scalar guard, discharging `hlink`. -/
theorem scalarUpper_link (x : V) (c : ℝ) (sysR : ODESystem V) (domain source : Formula V)
    (ω : State V) :
    Formula.sat (scalarUpper x c sysR domain source).guard ω
      ↔ 0 < Term.eval (scalarUpper x c sysR domain source).g ω := by
  simp [scalarUpper, Formula.sat, CompOp.interp, Term.eval, AOp.interp, sub_pos]

/-- Lower scalar guard `x < c`: safe side `g = c − x ≤ 0`, guard `{g > 0}`. -/
def scalarLower (x : V) (c : ℝ) (sysR : ODESystem V) (domain source : Formula V) :
    NonConnObligation V :=
  { g := Term.binop .sub (Term.const c) (Term.var x)
    guard := Formula.cmp .lt (Term.var x) (Term.const c)
    sysR := sysR, domain := domain, source := source }

theorem scalarLower_link (x : V) (c : ℝ) (sysR : ODESystem V) (domain source : Formula V)
    (ω : State V) :
    Formula.sat (scalarLower x c sysR domain source).guard ω
      ↔ 0 < Term.eval (scalarLower x c sysR domain source).g ω := by
  simp [scalarLower, Formula.sat, CompOp.interp, Term.eval, AOp.interp, sub_pos]

end RelCertifier
