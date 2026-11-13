/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The trusted SMT leaf + top-level `flow_certified`

The IO boundary. The trusted assumptions of the whole tool live here and nowhere else:
Z3's `unsat` verdict is sound (paper, Appendix B.4, Trusted Base), and, for a run with the
SOS oracle on (`RELCERT_SOS_SECS`, `docs/SOS-ORACLE.md`), the exact SOS certificate checker's
VERIFIED is sound.

* `z3solve` is `opaque` (its real behaviour is the Z3 process in `Main`; opaque so
  the pure core never depends on it, and it is not itself an axiom).
* `z3_unsat_sound` is the one axiom of every Z3-only certification.
* `sosCheck` is `opaque` likewise (its real behaviour is `Trusted/Sos.lean`), and
  `sos_unsat_sound` its axiom: it enters only the proofs of instances whose records carry an SOS
  verdict (`anyOracle`); the flow chain is generic in an `UnsatOracle` and carries no axiom.

`#print axioms flow_certified` shows the standard three + `z3_unsat_sound`, plus
proof-dependency edges to `flow_cert_sound` (⟶ dL-lean `DI_nonstrict_domain`).
-/
import RelCertifier.Core.FlowCert
import RelCertifier.Checker.NonConn
import RelCertifier.Checker.Cover

namespace RelCertifier

open DL

/-- SMT solver verdict. -/
inductive Verdict where
  | unsat | sat | unknown
  deriving DecidableEq, Repr, Inhabited

/-- The SMT oracle as an opaque constant. Operationally realized by the Z3 process
in `Main`; kept opaque so the pure core is independent of it. -/
opaque z3solve {V : Type*} : Formula V → Verdict

/-- **THE SINGLE TRUSTED LEAF.** An `unsat` verdict is sound: the queried formula is
satisfied by no state. This is the only assumed fact beyond the kernel, and it lives
at the IO boundary, outside the pure core. Shared by every stage. -/
axiom z3_unsat_sound {V : Type*} {q : Formula V} :
    z3solve q = Verdict.unsat → ∀ σ, ¬ Formula.sat q σ

/-! ## The second oracle: an exactly checked SOS certificate (`docs/SOS-ORACLE.md`)

With `RELCERT_SOS_SECS` set, a flow-query level Z3 answers `unknown` on is given to the SOS
oracle (`Trusted/Sos.lean`: `scripts/sos_oracle.py`, a numerical Putinar certificate from
`sos_prove.py` checked EXACTLY over the rationals by `sos_check.py`). The oracle's `unsat` is
the checker's VERIFIED on that printed query and nothing else. With the knob unset the oracle is
never called and no proof depends on its axiom. -/

/-- The exact SOS certificate checker as an opaque constant: `unsat` iff `sos_check.py` printed
VERIFIED for a certificate of the printed query. Operationally realized in `Trusted/Sos.lean`;
opaque like `z3solve`. -/
opaque sosCheck {V : Type*} : Formula V → Verdict

/-- **THE SECOND TRUSTED LEAF** (used only by instances whose records carry an SOS verdict). An
exactly verified SOS certificate for a printed query implies the query is satisfied by no state:
the checker's VERIFIED means the polynomial identity `-ġ - ε = s₀ + Σ sᵢ hᵢ + Σ qⱼ eⱼ` holds
over ℚ with positive semidefinite Gram matrices, so every state satisfying the hypotheses has
`-ġ ≥ ε`, contradicting the goal atom. An axiom about the checker's answer, exactly as
`z3_unsat_sound` is about Z3's. -/
axiom sos_unsat_sound {V : Type*} {q : Formula V} :
    sosCheck q = Verdict.unsat → ∀ σ, ¬ Formula.sat q σ

/-! ## Unsat oracles and the sliced verdict (`docs/HYP-SLICING.md`, `docs/SOS-ORACLE.md`)

A flow-query hypothesis set may be SLICED before it is sent (`RELCERT_SLICE_HOPS`,
`Trusted/Slice.lean`): the query the oracle sees keeps a subset of the domain's conjuncts, so it
is IMPLIED by the row's full query. `OracleUnsat O q` is the hypothesis shape the flow packs
assume, for an oracle `O` (`z3Oracle`: Z3 alone, the default of every pack; `anyOracle`: Z3 or
the SOS checker, the oracle of an instance whose records carry an SOS verdict): `O` answered
`unsat` on some query implied by `q` (the full query itself when the knob is unset,
`OracleUnsat.of_eq`; one of its escalation levels, a slice or the full query, when it is set,
`OracleUnsat_of_level`). The monotonicity lemma `oracleUnsat_sound` turns it back into
unsatisfiability of `q`, through the oracle's own soundness field alone: the proofs of the
flow chain are oracle-generic and carry no axiom of their own, the axiom enters with the
oracle the instance names (`z3Oracle` carries `z3_unsat_sound`, `anyOracle` both).
`Z3Unsat q` is `OracleUnsat z3Oracle q`. -/

/-- An unsat oracle: a verdict function with the soundness of its `unsat`. -/
structure UnsatOracle (V : Type*) where
  solve : Formula V → Verdict
  sound : ∀ {q : Formula V}, solve q = Verdict.unsat → ∀ σ, ¬ Formula.sat q σ

/-- Z3 alone (`z3_unsat_sound`). -/
def z3Oracle {V : Type*} : UnsatOracle V := ⟨z3solve, fun h => z3_unsat_sound h⟩

/-- The exact SOS certificate checker alone (`sos_unsat_sound`). -/
def sosOracle {V : Type*} : UnsatOracle V := ⟨sosCheck, fun h => sos_unsat_sound h⟩

/-- Which oracle answered a level (the runners' log and the tagged pins). -/
inductive OracleTag where
  | z3 | sos
  deriving DecidableEq, Repr, Inhabited

def OracleTag.oracle {V : Type*} : OracleTag → UnsatOracle V
  | .z3 => z3Oracle
  | .sos => sosOracle

instance : ToString OracleTag := ⟨fun | .z3 => "z3" | .sos => "sos"⟩

/-- Either oracle: `unsat` when Z3 or the checker answers `unsat` (both axioms). The oracle of
an instance whose records carry an SOS verdict. -/
def anyOracle {V : Type*} : UnsatOracle V where
  solve q := if z3solve q = Verdict.unsat then Verdict.unsat else sosCheck q
  sound := fun {q} h σ => by
    by_cases hz : z3solve q = Verdict.unsat
    · exact z3_unsat_sound hz σ
    · rw [if_neg hz] at h
      exact sos_unsat_sound h σ

theorem anyOracle_of_z3 {V : Type*} {q : Formula V} (h : z3solve q = Verdict.unsat) :
    (anyOracle (V := V)).solve q = Verdict.unsat := by
  simp [anyOracle, h]

theorem anyOracle_of_sos {V : Type*} {q : Formula V} (h : sosCheck q = Verdict.unsat) :
    (anyOracle (V := V)).solve q = Verdict.unsat := by
  by_cases hz : z3solve q = Verdict.unsat <;> simp [anyOracle, hz, h]

/-- A tagged answer is an answer of `anyOracle`. -/
theorem anyOracle_of_tag {V : Type*} {q : Formula V} (t : OracleTag)
    (h : (t.oracle (V := V)).solve q = Verdict.unsat) :
    (anyOracle (V := V)).solve q = Verdict.unsat := by
  cases t with
  | z3 => exact anyOracle_of_z3 h
  | sos => exact anyOracle_of_sos h

/-- `O` answered `unsat` on a formula implied by `q` (a sub-conjunction of `q`'s hypotheses, or
`q` itself). -/
def OracleUnsat {V : Type*} (O : UnsatOracle V) (q : Formula V) : Prop :=
  ∃ q' : Formula V, (∀ σ, Formula.sat q σ → Formula.sat q' σ) ∧ O.solve q' = Verdict.unsat

/-- The unsliced verdict: `unsat` on `q` itself. -/
theorem OracleUnsat.of_eq {V : Type*} {O : UnsatOracle V} {q : Formula V}
    (h : O.solve q = Verdict.unsat) : OracleUnsat O q :=
  ⟨q, fun _ hs => hs, h⟩

/-- `unsat` on any formula implied by `q`. -/
theorem OracleUnsat.of_weaker {V : Type*} {O : UnsatOracle V} {q q' : Formula V}
    (hw : ∀ σ, Formula.sat q σ → Formula.sat q' σ) (h : O.solve q' = Verdict.unsat) :
    OracleUnsat O q :=
  ⟨q', hw, h⟩

/-- **Monotonicity of the sliced verdict**: an `unsat` answer on a query implied by `q` makes
`q` itself unsatisfiable (the sliced hypothesis set is a subset of the full one). No axiom:
the oracle's own soundness field. -/
theorem oracleUnsat_sound {V : Type*} {O : UnsatOracle V} {q : Formula V} (h : OracleUnsat O q) :
    ∀ σ, ¬ Formula.sat q σ := by
  intro σ hs
  obtain ⟨q', hw, hz⟩ := h
  exact O.sound hz σ (hw σ hs)

/-- A verdict of `z3Oracle` is a verdict of `anyOracle` (an instance's Z3-only hypothesis
implies its either-oracle one). -/
theorem OracleUnsat.any_of_z3 {V : Type*} {q : Formula V} (h : OracleUnsat z3Oracle q) :
    OracleUnsat anyOracle q :=
  let ⟨q', hw, hz⟩ := h
  ⟨q', hw, anyOracle_of_z3 hz⟩

/-- Z3's sliced verdict: Z3 answered `unsat` on a formula implied by `q`. -/
abbrev Z3Unsat {V : Type*} (q : Formula V) : Prop := OracleUnsat z3Oracle q

/-- The unsliced verdict: `unsat` on `q` itself. -/
theorem Z3Unsat.of_eq {V : Type*} {q : Formula V} (h : z3solve q = Verdict.unsat) :
    Z3Unsat q :=
  ⟨q, fun _ hs => hs, h⟩

/-- `unsat` on any formula implied by `q`. -/
theorem Z3Unsat.of_weaker {V : Type*} {q q' : Formula V}
    (hw : ∀ σ, Formula.sat q σ → Formula.sat q' σ) (h : z3solve q' = Verdict.unsat) :
    Z3Unsat q :=
  ⟨q', hw, h⟩

/-- Z3's monotonicity lemma: `oracleUnsat_sound` at `z3Oracle`. The only axiom used is
`z3_unsat_sound`. -/
theorem z3Unsat_sound {V : Type*} {q : Formula V} (h : Z3Unsat q) :
    ∀ σ, ¬ Formula.sat q σ :=
  oracleUnsat_sound h

/-- **`flow_certified`** — top-level composition. If Z3 reports `unsat` on the flow
query, and `g ≤ 0` initially, then the invariant component `g ≤ 0` is preserved along
the joint product program at stretch λ (paper Eq. (14)) on `domain`: one component
of a flow certificate (Definition 5) by the Lie conditions (Lemma 2).

Pure assembly: `z3_unsat_sound` supplies unsatisfiability; `flow_cert_sound`
(⟶ dL-lean `DI_nonstrict_domain`, via `lieDeriv_correct`/`tderiv_correct`) turns that
into the invariance. No new mathematics. -/
theorem flow_certified {n : ℕ} (o : FlowObligation n) {ν : State (Var n)}
    (hz3 : z3solve (flowQuery o) = Verdict.unsat)
    (hinit : Term.eval o.g ν ≤ 0) :
    BoxLe (Program.ode (jointSys o.fL o.fR o.lam) o.domain)
      (fun ω => Term.eval o.g ω) ν :=
  flow_cert_sound o (z3_unsat_sound hz3) hinit

/-- **`nonconn_certified`** — non-connection IO boundary (paper Definition 6). If Z3
reports `unsat` on both the source check and the barrier check, the successor guard is
unreachable along the right flow. `#print axioms` shows the standard three + `z3_unsat_sound` (⟶ dL-lean
`DI_strict` via `nonconn_sound`). -/
theorem nonconn_certified {V : Type*} [Fintype V] [DecidableEq V]
    (o : NonConnObligation V) (hwf : o.sysR.WellFormed)
    (hlink : ∀ ω, Formula.sat o.guard ω ↔ 0 < Term.eval o.g ω)
    {ν : State V} (hν : Formula.sat o.source ν)
    (hsrc : z3solve (sourceCheck o) = Verdict.unsat)
    (hbar : z3solve (barrierCheck o) = Verdict.unsat) :
    ∀ ω, Program.sem (Program.ode o.sysR o.domain) ν ω → ¬ Formula.sat o.guard ω :=
  nonconn_sound o hwf hlink hν (z3_unsat_sound hsrc) (z3_unsat_sound hbar)

/-! ## Cover IO boundary — z3 UNSAT discharges the cover's certificate fields -/

/-- A `SegPreserves` field of `CoverCert`, discharged by a trusted Z3 UNSAT on the
mode's flow query (⟶ `flow_cert_sound`, Lemma 2). -/
theorem segPreserves_certified {n : ℕ} (o : FlowObligation n) (m : RMode (Var n))
    (hsys : m.sys = jointSys o.fL o.fR o.lam) (hdom : m.dom = o.domain)
    (hz3 : z3solve (flowQuery o) = Verdict.unsat) :
    SegPreserves o.g m :=
  segPreserves_of_flow o m hsys hdom (z3_unsat_sound hz3)

/-- A pruned edge's unreachable-guard obligation, discharged by trusted Z3 UNSATs on
the two non-connection checks (⟶ `nonconn_sound`, Definition 6). -/
theorem prune_certified {V : Type*} [Fintype V] [DecidableEq V]
    (o : NonConnObligation V) (m : RMode V)
    (hsys : m.sys = o.sysR) (hdom : m.dom = o.domain)
    (hwf : o.sysR.WellFormed) (hlink : ∀ ω, Formula.sat o.guard ω ↔ 0 < Term.eval o.g ω)
    {ν : State V} (hν : Formula.sat o.source ν)
    (hsrc : z3solve (sourceCheck o) = Verdict.unsat)
    (hbar : z3solve (barrierCheck o) = Verdict.unsat) :
    ∀ μ, Program.sem (Program.ode m.sys m.dom) ν μ → ¬ Formula.sat o.guard μ :=
  prune_of_nonconn o m hsys hdom hwf hlink hν (z3_unsat_sound hsrc) (z3_unsat_sound hbar)

end RelCertifier
