/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Step (3) — CSF `faModal` ⟹ the NFM'25 ∀∃ relational modality `[|(L,R)⟩⟩ϕ`

The last arrow of the main chain, built from two **proven** theorems:
* `DLRel.sat_encode_faShape` : `encode ρ (faShape α β ψ) ≡ faModal ρ α β (encode ρ ψ)` — the
  dL-caltiming ∀∃-modality *is* the host encoding of the dL-rel ∀∃ relational modality
  `faShape α β ψ = [|(α,?⊤)|]⟨⟨(?⊤,β)⟩⟩ψ = [|(α,β)⟩⟩ψ`. **Same renaming `ρ`.**
* `DLRel.RFormula.encoding_correct` (Theorem 2) : bi-state truth of a rel formula ≡ host truth
  of its encoding at a bridged join state.

Composing: a CSF `faModal ρ L* R* (encode ρ ϕ)` at the join state `σ` gives the **bi-state**
∀∃ relational invariant `[|(L*,R*)⟩⟩ϕ`. This is the paper's Theorem-3 conclusion, on the
mechanized relational logic — not a bespoke object.

NOTE. `relational_loop` here hardcodes the loop invariant = postcondition = `encode ψ` (its
`faModal_LOCK` call passes `hpost := fun _ h => h`). The transition-faithful assembly needs a
*strengthened* loop invariant `invLe g ∧ mvValid` (mode-validity), so it inlines `faModal_LOCK` +
`faModal_to_faShape` directly in `BridgeUnit3.relational_loop_faithful` rather than reusing this
wrapper. `faModal_to_faShape` itself is reused unchanged.
-/
import RelCertifier.CSFBridge
import RelCertifier.Reify
import DLRel

namespace RelCertifier

open DL DLCalTiming DLRel

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`faModal` ⟹ `[|(L,R)⟩⟩ϕ`.** If the CSF ∀∃-modality `faModal ρ α β (encode ρ ψ)` holds at
a join state `σ` bridging the bi-state `bs`, then the NFM'25 ∀∃ relational modality
`faShape α β ψ` (`= [|(α,β)⟩⟩ψ`) holds at `bs`. Pure composition of the two proven bridges. -/
theorem faModal_to_faShape (ρ : V ≃ V) (α β : Program V) (ψ : RFormula V)
    (σ : State V) (bs : BiState V)
    (hd : Disjoint (faShape α β ψ).varsL (ρ '' (faShape α β ψ).varsR))
    (hb : Bridges ρ (faShape α β ψ).varsL (faShape α β ψ).varsR bs σ)
    (h : Formula.sat (faModal ρ α β (encode ρ ψ)) σ) :
    RFormula.sat (faShape α β ψ) bs := by
  rw [RFormula.encoding_correct ρ (faShape α β ψ) hd bs σ hb, sat_encode_faShape]
  exact h

/-- **Atomic single-sync relational guarantee (end-to-end, one segment pair).** From the flow
certificate (`hcert`, a `BoxLe` on the joint evolution domain — discharged by `flow_cert_sound`)
and the CSF duration-existence side-condition `hExist` (`= faModal_ODE_G'`'s `hExist'`; carried
explicitly exactly as dL-caltiming ships it — it holds for the cover's bounded polynomial
domains, no finite escape), the paper's ∀∃ **relational** modality
`[|(ode leftBlock domL, ode rightBlock domR)⟩⟩ ψ` holds at the bi-state `bs`, where `ψ` is the
relational invariant whose (identity-)encoding is `g ≤ 0` (`hψ`). `ρ = id` throughout. -/
theorem segment_relational {n : ℕ}
    (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (ν : State (Var n)) (bs : BiState (Var n))
    (ψ : RFormula (Var n))
    (hdisj : Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
                      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (hcert : BoxLe (Program.ode (jointSys fL fR lam) (Formula.and domL domR))
        (fun ω => Term.eval g ω) ν)
    (hExist : ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
        (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ p ∈ leftBlock fL,
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Set.Icc 0 s) t) →
        (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock fL).bound → ΦL t x = ν x) →
        (∀ t ∈ Set.Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
        ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Set.Icc 0 s) t) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) s, Formula.sat domR (ΦR t)))
    (hψ : encode (Equiv.refl (Var n)) ψ = invLe g)
    (hd : Disjoint (faShape (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) ψ).varsL
        (Equiv.refl (Var n) '' (faShape (Program.ode (leftBlock fL) domL)
          (Program.ode (rightBlock fR lam) domR) ψ).varsR))
    (hb : Bridges (Equiv.refl (Var n))
        (faShape (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) ψ).varsL
        (faShape (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) ψ).varsR bs ν) :
    RFormula.sat (faShape (Program.ode (leftBlock fL) domL)
      (Program.ode (rightBlock fR lam) domR) ψ) bs := by
  refine faModal_to_faShape (Equiv.refl (Var n)) (Program.ode (leftBlock fL) domL)
    (Program.ode (rightBlock fR lam) domR) ψ ν bs hd hb ?_
  rw [hψ]
  exact segment_faModal g fL fR lam domL domR ν hdisj hφL hφR hcert hExist

/-- **Looped single-sync relational guarantee (the loop composition).** Given the per-iteration
single-sync step (`hstep` : from a state where the invariant `ψ` holds, one `(leftBody,rightBody)`
cycle re-establishes it — discharged per left mode by `segment_faModal` + the choice rules) and
left/right variable disjointness (`hd`, the `Side.L`/`Side.R` independence the lockstep needs to
commute the all-left-then-all-right ordering), the NFM'25 ∀∃ relational modality over the **looped**
automata `[|(leftBody*, rightBody*)⟩⟩ ψ` holds at the bi-state `bs`.

Composition of two proven theorems: `DLCalTiming.faModal_LOCK` (the lockstep loop invariant —
`lock_acc` + `sem_commute` handle the commutation internally) and `faModal_to_faShape` (Step 2).
`ρ = id`. This is the loop layer of the single-sync end-to-end chain; only the per-iteration
`hstep` (atomic, from `segment_faModal`) and the reification of `leftBody`/`rightBody` from the
model remain. -/
theorem relational_loop {n : ℕ} (leftBody rightBody : Program (Var n))
    (ψ : RFormula (Var n)) (ν : State (Var n)) (bs : BiState (Var n))
    (hd : Disjoint (Program.vars leftBody) (Program.vars (rightBody.rename (Equiv.refl (Var n)))))
    (hinv : Formula.sat (encode (Equiv.refl (Var n)) ψ) ν)
    (hstep : ∀ σ, Formula.sat (encode (Equiv.refl (Var n)) ψ) σ →
        Formula.sat (faModal (Equiv.refl (Var n)) leftBody rightBody
          (encode (Equiv.refl (Var n)) ψ)) σ)
    (hdd : Disjoint (faShape (Program.star leftBody) (Program.star rightBody) ψ).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star leftBody) (Program.star rightBody) ψ).varsR))
    (hb : Bridges (Equiv.refl (Var n))
        (faShape (Program.star leftBody) (Program.star rightBody) ψ).varsL
        (faShape (Program.star leftBody) (Program.star rightBody) ψ).varsR bs ν) :
    RFormula.sat (faShape (Program.star leftBody) (Program.star rightBody) ψ) bs := by
  refine faModal_to_faShape (Equiv.refl (Var n)) (Program.star leftBody)
    (Program.star rightBody) ψ ν bs hdd hb ?_
  exact faModal_LOCK (Equiv.refl (Var n)) leftBody rightBody
    (encode (Equiv.refl (Var n)) ψ) (encode (Equiv.refl (Var n)) ψ) ν hd hinv hstep (fun _ h => h)

/-- **Looped relational guarantee, MULTI (B>1 mode-switching).** As `relational_loop`, but the
per-left-cycle hypothesis couples the left mode with the **right star** (multiple right modes per
left cycle — discharged by `hstep_multiseg_het`), via the proven `faModal_MULTI`. Same
`faModal_to_faShape` close. -/
theorem relational_loop_multi {n : ℕ} (leftBody rightBody : Program (Var n))
    (ψ : RFormula (Var n)) (ν : State (Var n)) (bs : BiState (Var n))
    (hd : Disjoint (Program.vars leftBody) (Program.vars (rightBody.rename (Equiv.refl (Var n)))))
    (hinv : Formula.sat (encode (Equiv.refl (Var n)) ψ) ν)
    (hstep : ∀ σ, Formula.sat (encode (Equiv.refl (Var n)) ψ) σ →
        Formula.sat (faModal (Equiv.refl (Var n)) leftBody (Program.star rightBody)
          (encode (Equiv.refl (Var n)) ψ)) σ)
    (hdd : Disjoint (faShape (Program.star leftBody) (Program.star rightBody) ψ).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star leftBody) (Program.star rightBody) ψ).varsR))
    (hb : Bridges (Equiv.refl (Var n))
        (faShape (Program.star leftBody) (Program.star rightBody) ψ).varsL
        (faShape (Program.star leftBody) (Program.star rightBody) ψ).varsR bs ν) :
    RFormula.sat (faShape (Program.star leftBody) (Program.star rightBody) ψ) bs := by
  refine faModal_to_faShape (Equiv.refl (Var n)) (Program.star leftBody)
    (Program.star rightBody) ψ ν bs hdd hb ?_
  exact faModal_MULTI (Equiv.refl (Var n)) leftBody rightBody
    (encode (Equiv.refl (Var n)) ψ) (encode (Equiv.refl (Var n)) ψ) ν hd hinv hstep (fun _ h => h)

end RelCertifier
