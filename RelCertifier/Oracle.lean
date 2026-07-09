/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The trusted SMT leaf + top-level `flow_certified`

The IO boundary. The single trusted assumption of the whole tool lives here and
nowhere else: Z3's `unsat` verdict is sound.

* `z3solve` is `opaque` (its real behaviour is the Z3 process in `Main`; opaque so
  the pure core never depends on it, and it is not itself an axiom).
* `z3_unsat_sound` is the one axiom.

`#print axioms flow_certified` shows the standard three + `z3_unsat_sound`, plus
proof-dependency edges to `flow_cert_sound` (⟶ dL-lean `DI_nonstrict_domain`).
-/
import RelCertifier.FlowCert
import RelCertifier.NonConn
import RelCertifier.Cover

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

/-- **`flow_certified`** — top-level composition. If Z3 reports `unsat` on the flow
query, and `g ≤ 0` initially, then the invariant component `g ≤ 0` is preserved along
the λ-stretched co-evolution on `domain`.

Pure assembly: `z3_unsat_sound` supplies unsatisfiability; `flow_cert_sound`
(⟶ dL-lean `DI_nonstrict_domain`, via `lieDeriv_correct`/`tderiv_correct`) turns that
into the invariance. No new mathematics. -/
theorem flow_certified {n : ℕ} (o : FlowObligation n) {ν : State (Var n)}
    (hz3 : z3solve (flowQuery o) = Verdict.unsat)
    (hinit : Term.eval o.g ν ≤ 0) :
    BoxLe (Program.ode (jointSys o.fL o.fR o.lam) o.domain)
      (fun ω => Term.eval o.g ω) ν :=
  flow_cert_sound o (z3_unsat_sound hz3) hinit

/-- **`nonconn_certified`** — Stage-2 IO boundary. If Z3 reports `unsat` on both the
source check and the barrier check, the successor guard is unreachable along the right
co-evolution. `#print axioms` shows the standard three + `z3_unsat_sound` (⟶ dL-lean
`DI_strict` via `nonconn_sound`). -/
theorem nonconn_certified {V : Type*} [Fintype V] [DecidableEq V]
    (o : NonConnObligation V) (hwf : o.sysR.WellFormed)
    (hlink : ∀ ω, Formula.sat o.guard ω ↔ 0 < Term.eval o.g ω)
    {ν : State V} (hν : Formula.sat o.source ν)
    (hsrc : z3solve (sourceCheck o) = Verdict.unsat)
    (hbar : z3solve (barrierCheck o) = Verdict.unsat) :
    ∀ ω, Program.sem (Program.ode o.sysR o.domain) ν ω → ¬ Formula.sat o.guard ω :=
  nonconn_sound o hwf hlink hν (z3_unsat_sound hsrc) (z3_unsat_sound hbar)

/-! ## Stage-3 IO boundary — z3 UNSAT discharges the cover's certificate fields -/

/-- A `SegPreserves` field of `CoverCert`, discharged by a trusted Z3 UNSAT on the
mode's flow query (⟶ Stage-1 `flow_cert_sound`). -/
theorem segPreserves_certified {n : ℕ} (o : FlowObligation n) (m : RMode (Var n))
    (hsys : m.sys = jointSys o.fL o.fR o.lam) (hdom : m.dom = o.domain)
    (hz3 : z3solve (flowQuery o) = Verdict.unsat) :
    SegPreserves o.g m :=
  segPreserves_of_flow o m hsys hdom (z3_unsat_sound hz3)

/-- A pruned edge's unreachable-guard obligation, discharged by trusted Z3 UNSATs on
the two non-connection checks (⟶ Stage-2 `nonconn_sound`). -/
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
