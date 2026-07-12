/-
Part B units 3+4 — the transition-faithful loop close.

`relational_loop` (EncodingBridge) hardcodes `φinv = ψ = encode ψ` (its `faModal_LOCK` call
passes `(fun _ h => h)` as `hpost`), so it CANNOT carry the strengthened loop invariant
`φinv' = invLe g ∧ mvValid`. We therefore inline the two exposed, proven lemmas directly:

  unit 3: `faModal_LOCK` with `φinv := phiInv g mv numModes`, `ψ := invLe g`, `hpost := .1`
          → `faModal id (star leftBody) (star rightBody) (invLe g)` at ν
  unit 4: `faModal_to_faShape` → bi-state `faShape (star leftBody) (star rightBody) ψ`

`star (rightAutomatonBody G mv) = R_real G mv` definitionally, so the right side is the
transition-faithful automaton, not the flat over-approximation. `encode id ψ = invLe g`
(`hψ`, from `psi_ignores_mv`) bridges `faModal_LOCK`'s `invLe g` postcondition to
`faModal_to_faShape`'s `encode id ψ` requirement. The var-disjointness / Bridges side
conditions are carried as hypotheses, exactly as `reified_relational` does.
-/
import RelCertifier.BridgeUnit2
import RelCertifier.EncodingBridge

namespace RelCertifier
open DL DLCalTiming DLRel Function

variable {n : ℕ}

/-- **Units 3+4 — transition-faithful loop close.** From the assembled loop step (unit 2,
carrying `φinv' = invLe g ∧ mvValid`), close the `faModal_LOCK` loop against the real right
automaton `star (rightAutomatonBody G mv) = R_real G mv` and lift to the bi-state `faShape`.
The strengthened invariant projects to `invLe g = encode id ψ` at the exit (`hpost := .1`). -/
theorem relational_loop_faithful (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (ψ : RFormula (Var n))
    (ν : State (Var n)) (bs : BiState (Var n))
    (hψ : encode (Equiv.refl (Var n)) ψ = invLe g)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hinv : Formula.sat (invLe g) ν)
    (hmvν : Formula.sat (mvValid mv G.modes.length) ν)
    (hstep : ∀ σ, Formula.sat (phiInv g mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs) (rightAutomatonBody G mv)
        (phiInv g mv G.modes.length)) σ)
    (hdd : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) ψ).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) ψ).varsR))
    (hb : Bridges (Equiv.refl (Var n))
        (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) ψ).varsL
        (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) ψ).varsR bs ν) :
    RFormula.sat (faShape (Program.star (bigChoice leftProgs))
      (Program.star (rightAutomatonBody G mv)) ψ) bs := by
  refine faModal_to_faShape (Equiv.refl (Var n)) (Program.star (bigChoice leftProgs))
    (Program.star (rightAutomatonBody G mv)) ψ ν bs hdd hb ?_
  rw [hψ]
  exact faModal_LOCK (Equiv.refl (Var n)) (bigChoice leftProgs) (rightAutomatonBody G mv)
    (phiInv g mv G.modes.length) (invLe g) ν hd ⟨hinv, hmvν⟩ hstep (fun _ h => h.1)

end RelCertifier
