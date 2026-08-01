/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `modalVerd` — the runner's query construction, at the host level, pinned

`Verdicts/RunModal.lean` rebuilds each instance's verdict queries from a hand-written
`RunInfo` (dimension, invariant row, λ, region, ceiling). Without a pin, a wrong field
makes the runner test the *wrong query* and report it green. That happened twice while
the runner was being built — a wrong λ and a wrong `invRow` — and both were caught only
because the wrong query came back `sat`. One that happens to be `unsat` would pass
silently.

`modalVerd` states, at the host level, exactly what the runner builds. Each instance
then carries a `rfl` pin, so a wrong field does not compile. With `ModalPins` (IR
rebuild denotes the host query) and `ModalSpecs.modal_from_spec` (argument set ties to
the theorem), the chain from *what the runner sends Z3* to *what the theorem assumes*
is kernel-checked end to end.

**On the proof form.** The pins are stated as a two-step `Eq.trans` through
`modalVerdCore` rather than a single `rfl`. Both steps reduce, but the one-step
unification does not reach the normal form the two-step chain does (a plain `rfl`, and
even `with_unfolding_all rfl`, fail on the composite). `pin_of` packages the two steps
so instances need only supply the arguments.
-/
import RelCertifier.Verdicts.ModalPins
import RelCertifier.Instances.BenchIR
import RelCertifier.Proofs.Encoding.CoverInstance

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.Parse DL

/-- Split a conjunctive invariant into its atoms, as the instances do. -/
def atomsOfM : PForm → List PForm
  | .and x y => atomsOfM x ++ atomsOfM y
  | f => [f]

/-- The shape an instance's `Verd` reduces to directly.

`pre` prepends a component ahead of the invariant's own (the ceiling head `R_c − k_m`
and the repaired `Hold` region `k − R₀` both sit there, so later components are
narrowed by them); `post` appends one behind them (`rover_rung2c`'s region face).
Both are `Option` rather than `List` on purpose: the `none` branch is syntactically
`base`, so it reduces without going through `[] ++ base`, which `whnf` does not
unfold through `HAppend`. -/
noncomputable def modalVerdCore (p : PProblem) (invRow n : ℕ) (order : List ℕ)
    (pre post : Option (Term (Var n))) (lIdx rIdx : ℕ) (lam : ℝ) : Prop :=
  let vars := p.L.stateVars; let dm : PMode := ⟨"",[],.tt,.tt,[]⟩
  let atoms := atomsOfM (p.invariants.getD invRow ("", PForm.tt)).2
  let base : List (Term (Var n)) := order.map (fun i =>
    ((Run.invToG vars n (atoms.getD i .tt)).map ITerm.toHost).getD (Term.const 0))
  let withPre : List (Term (Var n)) := match pre with
    | none => base
    | some t => t :: base
  let comps : List (Term (Var n)) := match post with
    | none => withPre
    | some t => withPre ++ [t]
  let fL := hostDyn vars n Side.L (p.L.modes.getD lIdx dm)
  let fR := hostDyn vars n Side.R (p.R.modes.getD rIdx dm)
  let dom := Formula.and (hostEvolve vars n Side.L (p.L.modes.getD 0 dm))
                         (hostEvolve vars n Side.R (p.R.modes.getD 0 dm))
  ∀ i (hi : i < comps.length),
    z3solve (flowQuery ⟨comps[i], fL, fR, Term.const lam,
      strataDomHost dom (comps.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨comps[i], fL, fR, Term.const lam,
      strataDomHost dom (comps.take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨comps[i], fL, fR, Term.const lam,
      strataDomHost dom (comps.take i)⟩) = Verdict.unsat

/-- **The runner's query, at the host level** — argument order matching `RunInfo`. -/
noncomputable def modalVerd (p : PProblem) (n invRow : ℕ) (order : List ℕ)
    (pre post : Option (Term (Var n))) (lam : ℝ) (l m : ℕ) : Prop :=
  modalVerdCore p invRow n order pre post l m lam

/-- The two are the same statement; this step reduces on its own. -/
theorem modalVerd_eq_core (p : PProblem) (n invRow : ℕ) (order : List ℕ)
    (pre post : Option (Term (Var n))) (lam : ℝ) (l m : ℕ) :
    modalVerdCore p invRow n order pre post l m lam
      = modalVerd p n invRow order pre post lam l m :=
  rfl

/-- **Pin helper.** Given that the instance's `Verd` reduces to `modalVerdCore`
(which it does, by `rfl`), conclude it equals the runner's `modalVerd`. -/
theorem pin_of {P : Prop} {p : PProblem} {n invRow : ℕ} {order : List ℕ}
    {pre post : Option (Term (Var n))} {lam : ℝ} {l m : ℕ}
    (h : P = modalVerdCore p invRow n order pre post l m lam) :
    P = modalVerd p n invRow order pre post lam l m :=
  h.trans (modalVerd_eq_core p n invRow order pre post lam l m)

/-! ### The one-component form

Eleven instances state their hypothesis as a bare three-route disjunction over the
whole invariant row rather than as a `∀` over a component list. That is the same
content the runner checks — its `comps` list for these has length one, so its loop
issues exactly these three queries — but it is a different *shape* of `Prop`, so it
needs its own pin. The remaining gap — that the runner's component list really is
the single row these name — is closed by a `modalComps … = [modalRowG …]` pin per
instance, so the runner still has only one route. -/

/-- The bare disjunction shape, over the whole invariant row. -/
noncomputable def modalVerd1Core (p : PProblem) (invRow n : ℕ) (lIdx rIdx : ℕ)
    (lam : ℝ) : Prop :=
  let vars := p.L.stateVars; let dm : PMode := ⟨"",[],.tt,.tt,[]⟩
  let g : Term (Var n) :=
    ((Run.invToG vars n (p.invariants.getD invRow ("", PForm.tt)).2).map
      ITerm.toHost).getD (Term.const 0)
  let fL := hostDyn vars n Side.L (p.L.modes.getD lIdx dm)
  let fR := hostDyn vars n Side.R (p.R.modes.getD rIdx dm)
  let dom := Formula.and (hostEvolve vars n Side.L (p.L.modes.getD 0 dm))
                         (hostEvolve vars n Side.R (p.R.modes.getD 0 dm))
  z3solve (flowQuery ⟨g, fL, fR, Term.const lam, dom⟩) = Verdict.unsat
  ∨ z3solve (flowQueryStrict ⟨g, fL, fR, Term.const lam, dom⟩) = Verdict.unsat
  ∨ z3solve (flowQuerySuperlevel ⟨g, fL, fR, Term.const lam, dom⟩) = Verdict.unsat

/-- `modalVerd1`, in `RunInfo` argument order. -/
noncomputable def modalVerd1 (p : PProblem) (n invRow : ℕ) (lam : ℝ) (l m : ℕ) : Prop :=
  modalVerd1Core p invRow n l m lam

theorem modalVerd1_eq_core (p : PProblem) (n invRow : ℕ) (lam : ℝ) (l m : ℕ) :
    modalVerd1Core p invRow n l m lam = modalVerd1 p n invRow lam l m := rfl

/-- Pin helper for the one-component form. -/
theorem pin1_of {P : Prop} {p : PProblem} {n invRow : ℕ} {lam : ℝ} {l m : ℕ}
    (h : P = modalVerd1Core p invRow n l m lam) :
    P = modalVerd1 p n invRow lam l m :=
  h.trans (modalVerd1_eq_core p n invRow lam l m)

/-- The component list the runner builds, split out so an instance can state as a
plain `List` equality that the runner's components are the ones its hypothesis
names. For the one-component instances this is `[modalRowG …]`, which is what makes
`modalVerd1` and the runner's loop the same three queries. -/
noncomputable def modalComps (p : PProblem) (invRow n : ℕ) (order : List ℕ)
    (pre post : Option (Term (Var n))) : List (Term (Var n)) :=
  let vars := p.L.stateVars
  let atoms := atomsOfM (p.invariants.getD invRow ("", PForm.tt)).2
  let base : List (Term (Var n)) := order.map (fun i =>
    ((Run.invToG vars n (atoms.getD i .tt)).map ITerm.toHost).getD (Term.const 0))
  let withPre : List (Term (Var n)) := match pre with
    | none => base
    | some t => t :: base
  match post with
  | none => withPre
  | some t => withPre ++ [t]

/-- The whole invariant row, lowered — the single component `modalVerd1Core` uses. -/
noncomputable def modalRowG (p : PProblem) (invRow n : ℕ) : Term (Var n) :=
  ((Run.invToG p.L.stateVars n (p.invariants.getD invRow ("", PForm.tt)).2).map
    ITerm.toHost).getD (Term.const 0)

end RelCertifier.Verdicts
