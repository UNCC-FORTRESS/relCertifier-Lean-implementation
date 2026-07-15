/-
Assemble the per-left-mode `hstep_single`s into the loop step (single-flow bridge, unit 2) for the flat
left body `bigChoice leftProgs` against the fixed right automaton `rightAutomatonBody G mv`.

`faModal_bigChoiceL` composes over the left modes; the right mode `q` is *read off* the state
via `mvValid` (the strengthened loop invariant `φinv' = invLe g ∧ mvValid` guarantees `σ mv` is
a valid mode index `q`, and dispatches to mode `q`'s per-pair certificate). The per-`(P,q)` pair
data + certificate is taken as a hypothesis `Hpair`, discharged by the cover in unit 5.
-/
import RelCertifier.Proofs.Encoding.BridgeUnit1
import RelCertifier.Proofs.Encoding.Reification

namespace RelCertifier
open DL DLCalTiming Function

variable {n : ℕ}

/-- The strengthened loop invariant carried through `faModal_LOCK`: the encoded relational
invariant `invLe g` together with mode-validity `mvValid`. -/
def phiInv (g : Term (Var n)) (mv : Var n) (numModes : ℕ) : Formula (Var n) :=
  Formula.and (invLe g) (mvValid mv numModes)

/-- **Unit 2 — the assembled loop step.** For the flat left body `bigChoice leftProgs` against
the right automaton `rightAutomatonBody G mv`, the per-iteration `faModal` guarantee holds at
every `φinv'`-state. The right mode `q` is dispatched from `σ mv` (valid by `mvValid`), and each
left mode `P ∈ leftProgs` discharges via `hstep_single` on mode `q`'s pair certificate. -/
theorem hstep_assembled (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (hg : mv ∉ g.fv)
    (Hpair : ∀ P ∈ leftProgs, ∀ (q : ℕ) (m : RMode (Var n)), G.modeAt q = some m →
      ∃ (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (domL domR : Formula (Var n))
        (e : REdge (Var n)),
        P = Program.ode (leftBlock fL) domL ∧ mv ∉ (leftBlock fL).bound ∧
        m.sys = rightBlock fR lam ∧ m.dom = domR ∧
        e ∈ G.edgesFrom q ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length ∧
        -- invariant-CONDITIONAL: `segment_faModal`/`SegPreserves` supply the per-pair faModal only
        -- at invariant states (a segment preserves `g ≤ 0`, it cannot restore a violated one). This
        -- is exactly the state `hstep` is invoked at (`φinv' ⊢ invLe g`), so conditioning loses
        -- nothing — and the unconditional form was unsound to assume.
        (∀ s, Formula.sat (invLe g) s → Formula.sat (faModal (Equiv.refl (Var n))
          (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) (invLe g)) s)) :
    ∀ σ, Formula.sat (phiInv g mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs) (rightAutomatonBody G mv)
        (phiInv g mv G.modes.length)) σ := by
  intro σ hφ'
  -- read the current right mode q off the state (mvValid guarantees validity)
  obtain ⟨q, hqlt, hmvq⟩ := sat_mvValid.mp hφ'.2
  -- q is in range, so it names a declared mode
  have hm : G.modeAt q = some (G.modes[q]'hqlt) := by
    simp only [SearchGraph.modeAt, List.getElem?_eq_getElem hqlt]
  set m := G.modes[q]'hqlt with hmdef
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (rightAutomatonBody G mv)
    (phiInv g mv G.modes.length) σ leftProgs ?_
  intro P hP
  obtain ⟨fL, fR, lam, domL, domR, e, hPeq, hmvL, hsys, hdom, hef, hetg, hetv, hcert⟩ :=
    Hpair P hP q m hm
  rw [hPeq]
  exact hstep_single G mv q m g fL fR lam domL domR hg hmvL hm hsys hdom hef hetg hetv hmvq
    (hcert σ hφ'.1)

end RelCertifier
