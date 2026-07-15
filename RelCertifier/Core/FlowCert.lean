/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

Stage 1 — the verified flow certificate (the Lie-derivative heart).

The Lie-derivative check:  ġ = Σ_v [∂g/∂L_v · f_L(v) + ∂g/∂R_v · λ · f_R(v)]
and the flow obligation `g = 0 ∧ ġ > 0` UNSAT.

We verify what that tool trusts. Every soundness-critical lemma is anchored to
dL-lean (v0.1.0-DI): `Term`, `Formula`, `Term.eval`, `Formula.sat`, and the
semantic differential-invariant theorems `DI_strict` / `DI_nonstrict_domain`.
-/
import DLLean
import RelCertifier.Proofs.Flow.DISuperlevel

open DL

namespace RelCertifier

/-! ## (1) Representation — joint variable space, invariant, dynamics -/

/-- The two sides of the relational pair: `L`eft program, `R`ight program. -/
inductive Side | L | R | Aux
  deriving DecidableEq, Repr

instance : Fintype Side := ⟨{Side.L, Side.R, Side.Aux}, fun s => by cases s <;> simp⟩

/-- Joint variable space over `n` per-side coordinates: `Var n = Side × Fin n`.
`(L, i)` is the left copy of coordinate `i`, `(R, i)` the right copy. A concrete
`Fintype`/`DecidableEq` `V` — exactly what dL-lean's `Lie`/`DI` require. -/
abbrev Var (n : ℕ) := Side × Fin n

/-- Left coordinate `Lᵢ` as a dL variable/term. -/
abbrev Lv {n : ℕ} (i : Fin n) : Var n := (Side.L, i)
/-- Right coordinate `Rᵢ` as a dL variable/term. -/
abbrev Rv {n : ℕ} (i : Fin n) : Var n := (Side.R, i)
/-- Auxiliary coordinate `Aᵢ` (outside `Lv`/`Rv`) — the clock/control slot. -/
abbrev Av {n : ℕ} (i : Fin n) : Var n := (Side.Aux, i)

/-- Data of a single relational flow obligation.
* `g`      — the invariant component; the invariant is `g ≤ 0`.
* `fL i`   — left dynamics: the term giving `Lᵢ' = fL i`.
* `fR i`   — right dynamics (unstretched): `Rᵢ' = fR i`.
* `lam`    — the time-stretch factor λ (a constant term).
* `domain` — the evolution-domain formula ψ (left guard ∧ right guard …). -/
structure FlowObligation (n : ℕ) where
  g      : Term (Var n)
  fL     : Fin n → Term (Var n)
  fR     : Fin n → Term (Var n)
  lam    : Term (Var n)
  domain : Formula (Var n)

/-! ## (2) Verified symbolic differentiation `tderiv`

Syntactic ∂/∂x on polynomial terms: const→0, var→1-or-0, +→+, −→−, ·→product rule. -/

/-- Syntactic partial derivative `∂t/∂x` of a term. -/
def tderiv {V : Type*} [DecidableEq V] : Term V → V → Term V
  | .var y,          x => if y = x then .const 1 else .const 0
  | .const _,        _ => .const 0
  | .binop .add a b, x => .binop .add (tderiv a x) (tderiv b x)
  | .binop .sub a b, x => .binop .sub (tderiv a x) (tderiv b x)
  | .binop .mul a b, x => .binop .add (.binop .mul (tderiv a x) b)
                                      (.binop .mul a (tderiv b x))

/-- **THE load-bearing new proof (statement).** The syntactic derivative denotes
the analytic partial derivative: as a function of the single coordinate `x`
(all others frozen), `⟦t⟧` has derivative `⟦tderiv t x⟧` at `ω x`.

Proved by induction on `t`, anchored to Mathlib's `HasDerivAt` lemmas
(`hasDerivAt_const`, `HasDerivAt.add/sub/mul`, and the coordinate projection). -/
theorem tderiv_correct {V : Type*} [Fintype V] [DecidableEq V]
    (t : Term V) (x : V) (ω : State V) :
    HasDerivAt (fun r : ℝ => Term.eval t (Function.update ω x r))
      (Term.eval (tderiv t x) ω) (ω x) := by
  induction t with
  | var y =>
    by_cases h : y = x
    · subst h
      have hf : (fun r : ℝ => Term.eval (Term.var y) (Function.update ω y r)) = id := by
        funext r; simp [Term.eval, Function.update_self]
      have hv : Term.eval (tderiv (Term.var y) y) ω = 1 := by simp [tderiv, Term.eval]
      rw [hf, hv]; exact hasDerivAt_id (ω y)
    · have hf : (fun r : ℝ => Term.eval (Term.var y) (Function.update ω x r)) = fun _ => ω y := by
        funext r; simp [Term.eval, Function.update_of_ne h]
      have hv : Term.eval (tderiv (Term.var y) x) ω = 0 := by simp [tderiv, if_neg h, Term.eval]
      rw [hf, hv]; exact hasDerivAt_const (ω x) (ω y)
  | const c =>
    have hf : (fun r : ℝ => Term.eval (Term.const c) (Function.update ω x r)) = fun _ => c := by
      funext r; simp [Term.eval]
    have hv : Term.eval (tderiv (Term.const c) x) ω = 0 := by simp [tderiv, Term.eval]
    rw [hf, hv]; exact hasDerivAt_const (ω x) c
  | binop op a b iha ihb =>
    cases op with
    | add => exact iha.add ihb
    | sub => exact iha.sub ihb
    | mul =>
      have hm := iha.mul ihb
      rw [Function.update_eq_self] at hm
      exact hm

/-- Every term denotes a (globally) differentiable function of the state — the
polynomial-total-differentiability companion `tderiv_correct` needs to feed the
chain rule in dL-lean's `hasDeriv_g_along_flow`. -/
theorem term_differentiable {V : Type*} [Fintype V] [DecidableEq V]
    (t : Term V) : Differentiable ℝ (fun ν : State V => Term.eval t ν) := by
  induction t with
  | var y =>
    have hf : (fun ν : State V => Term.eval (Term.var y) ν) = fun ν => ν y := by
      funext ν; simp [Term.eval]
    rw [hf]; exact differentiable_pi.mp differentiable_id y
  | const c =>
    exact differentiable_const c
  | binop op a b iha ihb =>
    cases op with
    | add => exact iha.add ihb
    | sub => exact iha.sub ihb
    | mul => exact iha.mul ihb

/-- **Partial-derivative (fderiv) corollary** — the exact shape `Lie` consumes:
the directional derivative of `⟦t⟧` along the unit `Pi.single x 1` equals
`⟦tderiv t x⟧`. Bridges `tderiv_correct` (single-variable slice) to dL-lean's
`fderiv`-based `Lie`. -/
theorem tderiv_fderiv {V : Type*} [Fintype V] [DecidableEq V]
    (t : Term V) (x : V) (ω : State V) :
    fderiv ℝ (fun ν : State V => Term.eval t ν) ω (Pi.single x 1)
      = Term.eval (tderiv t x) ω := by
  have hg : Differentiable ℝ (fun ν : State V => Term.eval t ν) := term_differentiable t
  -- The line `r ↦ update ω x r` has derivative the unit vector `Pi.single x 1`.
  have hl : HasDerivAt (fun r : ℝ => Function.update ω x r) (Pi.single x 1) (ω x) := by
    rw [hasDerivAt_pi]
    intro i
    by_cases h : i = x
    · rw [h]
      have hf : (fun r : ℝ => Function.update ω x r x) = id := by
        funext r; simp [Function.update_self]
      rw [hf, Pi.single_eq_same]; exact hasDerivAt_id (ω x)
    · have hf : (fun r : ℝ => Function.update ω x r i) = fun _ => ω i := by
        funext r; simp [Function.update_of_ne h]
      rw [hf, Pi.single_eq_of_ne h]; exact hasDerivAt_const (ω x) (ω i)
  -- Chain rule: `r ↦ g(update ω x r)` has derivative `fderiv g ω (Pi.single x 1)`.
  have hpt : (fun r : ℝ => Function.update ω x r) (ω x) = ω := Function.update_eq_self x ω
  have hg' : HasFDerivAt (fun ν : State V => Term.eval t ν)
      (fderiv ℝ (fun ν => Term.eval t ν) ω) ((fun r : ℝ => Function.update ω x r) (ω x)) := by
    rw [hpt]; exact (hg ω).hasFDerivAt
  have hcomp := hg'.comp_hasDerivAt (ω x) hl
  exact (HasDerivAt.unique (tderiv_correct t x ω) hcomp).symm

/-! ## (3) Relational Lie derivative -/

/-- Fold a list of terms into their syntactic sum (`Σ`, right-associated, `0` base). -/
def sumTerm {V : Type*} : List (Term V) → Term V
  | []      => .const 0
  | t :: ts => .binop .add t (sumTerm ts)

/-- `⟦Σ ts⟧ = Σ ⟦ts⟧`. -/
theorem eval_sumTerm {V : Type*} (ts : List (Term V)) (ω : State V) :
    Term.eval (sumTerm ts) ω = (ts.map (fun t => Term.eval t ω)).sum := by
  induction ts with
  | nil => simp [sumTerm, Term.eval]
  | cons a t ih => simp [sumTerm, Term.eval, AOp.interp, ih]

/-- `(Σ f) + (Σ g) = Σ (f + g)` over a list. -/
theorem sum_map_add {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map f).sum + (l.map g).sum = (l.map (fun a => f a + g a)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ← ih]; ring

/-- The λ-stretched joint ODE system consumed by dL-lean's `DI`:
`Lᵢ' = fL i`,  `Rᵢ' = λ · fR i`, assembled as one `ODESystem (Var n)`.
`Lie` of `g` along this field is exactly the computed Lie derivative (`lieDeriv`). -/
def jointSys {n : ℕ} (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) :
    ODESystem (Var n) :=
  (List.finRange n).map (fun i => (Lv i, fL i)) ++
  (List.finRange n).map (fun i => (Rv i, Term.binop .mul lam (fR i)))

/-- Relational Lie derivative as a **syntactic term**:
`ġ = Σᵢ [ ∂g/∂Lᵢ · fL i  +  ∂g/∂Rᵢ · (λ · fR i) ]`. Matches `lie_derivative`. -/
def lieDeriv {n : ℕ} (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) : Term (Var n) :=
  sumTerm ((List.finRange n).map (fun i =>
    Term.binop .add
      (Term.binop .mul (tderiv g (Lv i)) (fL i))
      (Term.binop .mul (tderiv g (Rv i)) (Term.binop .mul lam (fR i)))))

/-- **`lieDeriv` denotes dL-lean's semantic `Lie`** along the stretched joint field
`jointSys`. This is the object `DI` consumes. Cites `tderiv_fderiv` (each syntactic
`∂g/∂v` = the `fderiv` directional derivative) and the `jointSys` construction
(its `Lie` list-sum reindexes to the per-coordinate `L`/`R` sum). -/
theorem lieDeriv_correct {n : ℕ} (g : Term (Var n))
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (ω : State (Var n)) :
    Term.eval (lieDeriv g fL fR lam) ω
      = Lie (jointSys fL fR lam) (fun ν => Term.eval g ν) ω := by
  rw [lieDeriv, eval_sumTerm, Lie, jointSys]
  -- LHS: Σᵢ ( ⟦∂g/∂Lᵢ⟧·⟦fLᵢ⟧ + ⟦∂g/∂Rᵢ⟧·(⟦λ⟧·⟦fRᵢ⟧) ) ;  RHS: Lie-sum over the L-list ++ R-list
  simp only [List.map_append, List.map_map, List.sum_append, Function.comp_def]
  -- unfold term evaluation and rewrite each `fderiv … (Pi.single · 1)` to the syntactic derivative
  simp only [Term.eval, AOp.interp, tderiv_fderiv]
  -- both sides are now list sums; combine the RHS two sums into one over `finRange n`
  rw [sum_map_add]

/-- `jointSys` is well-formed (each bound variable assigned once): the `L`/`R`
coordinate lists have `Nodup` keys and are disjoint. Needed by every `DI`/`Lie`
lemma. -/
theorem jointSys_wellFormed {n : ℕ} (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) : (jointSys fL fR lam).WellFormed := by
  have hLinj : Function.Injective (Lv (n := n)) := by
    intro a b h; simpa [Lv, Prod.ext_iff] using h
  have hRinj : Function.Injective (Rv (n := n)) := by
    intro a b h; simpa [Rv, Prod.ext_iff] using h
  unfold ODESystem.WellFormed jointSys
  simp only [List.map_append, List.map_map, Function.comp_def, Prod.fst]
  rw [List.nodup_append]
  refine ⟨(List.nodup_finRange n).map hLinj, (List.nodup_finRange n).map hRinj, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  obtain ⟨i, _, rfl⟩ := ha
  obtain ⟨j, _, rfl⟩ := hb
  simp [Lv, Rv, Prod.ext_iff] at hab

/-! ## (4) Boundary / flow query builder -/

/-- The domain-wide flow query whose UNSAT is the certificate:
`domain ∧ ġ > 0`. UNSAT ⟹ `ġ ≤ 0` on all of `domain` — precisely the hypothesis
of dL-lean's `DI_nonstrict_domain`.

NOTE (soundness, see gate report): the naive literal query is
`domain ∧ g = 0 ∧ ġ > 0` (boundary-only). That form is **unsound** without a
regular-boundary hypothesis — dL-lean's `nonstrict_boundary_insufficient` is the
`t²` counterexample. `flowQueryStrict` below is the boundary form that *is* sound
(strict, via `DI_strict`); this `flowQuery` is the domain form that is sound via
`DI_nonstrict_domain`. -/
def flowQuery {n : ℕ} (o : FlowObligation n) : Formula (Var n) :=
  Formula.and o.domain
    (Formula.cmp .gt (lieDeriv o.g o.fL o.fR o.lam) (Term.const 0))

/-- Strict boundary query: `domain ∧ g = 0 ∧ ġ ≥ 0`. UNSAT ⟹ `ġ < 0` on the
boundary `{g = 0} ∩ domain` — the hypothesis of `DI_strict`. -/
def flowQueryStrict {n : ℕ} (o : FlowObligation n) : Formula (Var n) :=
  Formula.and o.domain
    (Formula.and (Formula.cmp .eq o.g (Term.const 0))
      (Formula.cmp .ge (lieDeriv o.g o.fL o.fR o.lam) (Term.const 0)))

/-! ## (5) Flow certificate soundness -/

/-- **Flow certificate soundness (domain form).** If the flow query
`domain ∧ ġ > 0` is unsatisfiable, then the invariant component `g ≤ 0` is
preserved along the λ-stretched co-evolution on `domain`.

Cites dL-lean `DI_nonstrict_domain`: `lieDeriv_correct` turns the SMT fact
`ġ ≤ 0 on domain` into `Lie (jointSys) ⟦g⟧ ≤ 0 on ψ`, which is exactly its
boundary hypothesis. No new trusted leaf — the Z3 UNSAT verdict is the only one,
in the IO shell. -/
theorem flow_cert_sound {n : ℕ} (o : FlowObligation n) {ν : State (Var n)}
    (hunsat : ∀ σ, ¬ Formula.sat (flowQuery o) σ)
    (hinit : Term.eval o.g ν ≤ 0) :
    BoxLe (Program.ode (jointSys o.fL o.fR o.lam) o.domain)
      (fun ω => Term.eval o.g ω) ν := by
  refine DI_nonstrict_domain (jointSys_wellFormed o.fL o.fR o.lam)
    (term_differentiable o.g) ?_ hinit
  -- boundary hypothesis of `DI_nonstrict_domain`: `Lie ≤ 0` on the whole domain `ψ`
  intro x hx
  rw [← lieDeriv_correct]
  by_contra hpos
  rw [not_le] at hpos
  exact hunsat x ⟨hx, by simpa [flowQuery, Formula.sat, CompOp.interp, Term.eval] using hpos⟩

/-- **Flow certificate soundness (strict boundary form).** If the strict boundary query
`domain ∧ g = 0 ∧ ġ ≥ 0` is unsatisfiable, then `g ≤ 0` is preserved along the
λ-stretched co-evolution on `domain`.

Cites dL-lean `DI_strict`: UNSAT gives `ġ < 0` on `{g=0} ∩ domain` (via
`lieDeriv_correct`), the strict boundary hypothesis. This is the route that certifies
offset invariants (`g = L_x − R_x − d`), whose Lie is negative only *on* the boundary —
the domain-wide `flow_cert_sound` cannot see them. Same soundness discipline: strict, no
new axiom, matches the design's "strictly away". -/
theorem flow_cert_sound_strict {n : ℕ} (o : FlowObligation n) {ν : State (Var n)}
    (hunsat : ∀ σ, ¬ Formula.sat (flowQueryStrict o) σ)
    (hinit : Term.eval o.g ν ≤ 0) :
    BoxLe (Program.ode (jointSys o.fL o.fR o.lam) o.domain)
      (fun ω => Term.eval o.g ω) ν := by
  refine DI_strict (jointSys_wellFormed o.fL o.fR o.lam)
    (term_differentiable o.g) ?_ hinit
  intro x hx hg0
  rw [← lieDeriv_correct]
  by_contra hpos
  rw [not_lt] at hpos
  exact hunsat x ⟨hx, hg0, by simpa [Formula.sat, CompOp.interp, Term.eval] using hpos⟩

/-- Superlevel (Lyapunov) query: `domain ∧ g ≥ 0 ∧ ġ > 0`. UNSAT ⟹ `ġ ≤ 0` on the
superlevel side `{g ≥ 0} ∩ domain` — the hypothesis of `DI_nonstrict_superlevel`. -/
def flowQuerySuperlevel {n : ℕ} (o : FlowObligation n) : Formula (Var n) :=
  Formula.and o.domain
    (Formula.and (Formula.cmp .ge o.g (Term.const 0))
      (Formula.cmp .gt (lieDeriv o.g o.fL o.fR o.lam) (Term.const 0)))

/-- **Flow certificate soundness (superlevel / Lyapunov form).** If `domain ∧ g ≥ 0 ∧ ġ > 0`
is unsatisfiable, then `g ≤ 0` is preserved along the λ-stretched co-evolution.

Cites `DI_nonstrict_superlevel`: UNSAT gives `ġ ≤ 0` on `{g ≥ 0} ∩ domain` (via
`lieDeriv_correct`), the Lyapunov-barrier hypothesis. This is the route that certifies the
marginal contraction/energy class (`ġ = −c·g ≤ 0` on `{g ≥ 0}`, `ġ = 0` on the boundary)
where both `flow_cert_sound` (domain-wide, fails on `{g<0}`) and `flow_cert_sound_strict`
(needs `ġ < 0`) decline. Sound with no regularity hypothesis; rejects the `t²` pathology
(interior positivity of `ġ`). No new axiom. -/
theorem flow_cert_sound_superlevel {n : ℕ} (o : FlowObligation n) {ν : State (Var n)}
    (hunsat : ∀ σ, ¬ Formula.sat (flowQuerySuperlevel o) σ)
    (hinit : Term.eval o.g ν ≤ 0) :
    BoxLe (Program.ode (jointSys o.fL o.fR o.lam) o.domain)
      (fun ω => Term.eval o.g ω) ν := by
  refine DI_nonstrict_superlevel (jointSys_wellFormed o.fL o.fR o.lam)
    (term_differentiable o.g) ?_ hinit
  intro x hx hge
  rw [← lieDeriv_correct]
  by_contra hpos
  rw [not_le] at hpos
  refine hunsat x ⟨hx, ?_, by simpa [Formula.sat, CompOp.interp, Term.eval] using hpos⟩
  simpa [Formula.sat, CompOp.interp, Term.eval] using hge

end RelCertifier
