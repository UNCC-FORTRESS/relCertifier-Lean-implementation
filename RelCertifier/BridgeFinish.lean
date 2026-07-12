/-
The single-flow transition-faithful Theorem 3 (`rvalid` form) — the base case GAP 1-3 lift.

`rvalid` quantifies over ALL bi-states, including ones whose fresh mode variable `mv` holds an
undeclared index. The relational invariant `ϕinv` never mentions `mv`, so at such a bi-state the
right automaton's first `test(mode=q)` matches nothing, the ∃-right can only take the empty run,
and a `ϕinv`-breaking left move goes unmatched — `faShape` false while `ϕinv` true. Hence
`rvalid(theorem3Form L_flat R_real' ϕinv)` with a BARE `ϕinv` is **false**.

The sound target carries mode-validity in `theorem3Form`'s `ϕinv`:

    rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv) (ϕinv ∧ mvValidR))

read: "for initial states where the reasoning automaton is in a declared mode, the finer system
refines the coarser within tolerance." `mvValidR := ⌊mvValid⌋_R` (mode-validity read on the right
execution). `encode id mvValidR = mvValid`, so the encoded precondition is exactly the loop
invariant `phiInv = invLe g ∧ mvValid` (unit 2/3), and the `rvalid` lift bridges every bi-state to
its canonical join (`exists_bridge`) where `relational_loop_faithful` (units 1-4) applies.

Var-disjointness / the Z3 cert-family (`hstep`) enter as hypotheses, exactly as
`certified_relational` (the flat pipeline) leaves them — same trust boundary, transition-faithful.
-/
import RelCertifier.BridgeUnit3
import RelCertifier.Cover.Encoding

namespace RelCertifier
open DL DLCalTiming DLRel Function

/-- `RFormula` implication unfolds to the classical arrow at the bi-state. -/
theorem RFormula_sat_imp {V : Type*} (a b : RFormula V) (bs : BiState V) :
    RFormula.sat (RFormula.imp a b) bs ↔ (RFormula.sat a bs → RFormula.sat b bs) := by
  classical
  simp only [RFormula.imp, RFormula.or, RFormula.sat]
  tauto

variable {n : ℕ}

/-- Mode-validity as a right-projection rel formula: the reasoning (right) execution's mode
variable holds a declared index. -/
def mvValidR (mv : Var n) (numModes : ℕ) : RFormula (Var n) :=
  RFormula.proj DLRel.Side.R (mvValid mv numModes)

/-- The right-projection of `mvValid` encodes (`ρ = id`) to the host `mvValid`. -/
theorem encode_mvValidR (mv : Var n) (k : ℕ) :
    encode (Equiv.refl (Var n)) (mvValidR mv k) = mvValid mv k := by
  unfold encode mvValidR
  simp only [RFormula.renameR, RFormula.enc, Formula.rename_refl]

/-- Encoding distributes over the strengthened precondition `ϕinv ∧ mvValidR`, giving the loop
invariant `phiInv = invLe g ∧ mvValid` whenever `ϕinv` encodes to `invLe g`. -/
theorem encode_and_mvValidR {ϕinv : RFormula (Var n)} {g : Term (Var n)} {mv : Var n} {k : ℕ}
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g) :
    encode (Equiv.refl (Var n)) (RFormula.and ϕinv (mvValidR mv k)) = phiInv g mv k := by
  have hdist : encode (Equiv.refl (Var n)) (RFormula.and ϕinv (mvValidR mv k))
      = Formula.and (encode (Equiv.refl (Var n)) ϕinv)
          (encode (Equiv.refl (Var n)) (mvValidR mv k)) := by
    unfold encode; simp only [RFormula.renameR, RFormula.enc]
  rw [hdist, hψ, encode_mvValidR]; rfl

/-- `ϕ.varsL ⊆ (faShape α β ϕ).varsL`: the postcondition's left variables lie inside the shape's. -/
theorem varsL_subset_faShape (α β : Program (Var n)) (ϕ : RFormula (Var n)) :
    ϕ.varsL ⊆ (faShape α β ϕ).varsL := by
  simp only [faShape, RFormula.rdiamond, RFormula.varsL, RProgram.varsL]
  intro x hx; exact Or.inr (Or.inr hx)

/-- `ϕ.varsR ⊆ (faShape α β ϕ).varsR`. -/
theorem varsR_subset_faShape (α β : Program (Var n)) (ϕ : RFormula (Var n)) :
    ϕ.varsR ⊆ (faShape α β ϕ).varsR := by
  simp only [faShape, RFormula.rdiamond, RFormula.varsR, RProgram.varsR]
  intro x hx; exact Or.inr (Or.inr hx)

/-- **Unit 5 — transition-faithful Theorem 3, `rvalid` form.** With mode-validity carried in the
invariant, the checker's positive verdict (packaged as the loop-step hypothesis `hstep`, the
var-disjointness `hd`, and the shape disjointness `hddF`) yields the paper's ∀∃ refinement
modality over the *real* automaton `R_real G mv = star (rightAutomatonBody G mv)`, valid at every
bi-state. -/
theorem theorem3_faithful (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hstep : ∀ σ, Formula.sat (phiInv g mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs) (rightAutomatonBody G mv)
        (phiInv g mv G.modes.length)) σ)
    (hddF : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv)) (RFormula.and ϕinv (mvValidR mv G.modes.length))).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (rightAutomatonBody G mv))
            (RFormula.and ϕinv (mvValidR mv G.modes.length))).varsR)) :
    RFormula.rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody G mv)
      (RFormula.and ϕinv (mvValidR mv G.modes.length))) := by
  set k := G.modes.length
  set ψpost := RFormula.and ϕinv (mvValidR mv k) with hψpost
  set Lp := Program.star (bigChoice leftProgs)
  set Rp := Program.star (rightAutomatonBody G mv)
  have hencψ : encode (Equiv.refl (Var n)) ψpost = phiInv g mv k := encode_and_mvValidR hψ
  intro bs
  -- theorem3Form = imp ψpost (faShape Lp Rp ψpost); unfold the implication
  rw [theorem3Form]
  refine (RFormula_sat_imp _ _ bs).mpr ?_
  intro hpre
  -- canonical join state bridging bs on the whole shape's variables
  obtain ⟨ν, hbdg⟩ := exists_bridge (Equiv.refl (Var n))
    (faShape Lp Rp ψpost).varsL (faShape Lp Rp ψpost).varsR hddF bs
  -- restrict the bridge / disjointness to ψpost's own variables
  have hbψ : Bridges (Equiv.refl (Var n)) ψpost.varsL ψpost.varsR bs ν :=
    hbdg.mono (varsL_subset_faShape Lp Rp ψpost) (varsR_subset_faShape Lp Rp ψpost)
  have hdψ : Disjoint ψpost.varsL (Equiv.refl (Var n) '' ψpost.varsR) :=
    hddF.mono (varsL_subset_faShape Lp Rp ψpost)
      (Set.image_mono (varsR_subset_faShape Lp Rp ψpost))
  -- the encoded precondition holds at ν: this is the strengthened loop invariant
  have hInvν : Formula.sat (phiInv g mv k) ν := by
    rw [← hencψ]; exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  exact relational_loop_faithful G mv g leftProgs ψpost ν bs hencψ hd hInvν hstep hddF hbdg

end RelCertifier
