/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Cut composition — the declared invariant with the checked cut carried as a MODE REGION

Two benchmarks (`arm_chain_rung3`, `arm_fidelity_mid`) are certified by the tool at a CHECKED CUT: the right
`Hold` mode's flow certificate is discharged on the domain narrowed by `Hold`'s guard
atom `θ_R ≥ 0.6` (entry by O1, invariance by O2 — `Trusted/OracleAPI.lean`
`checkedCut`/`andCuts`). Their first modal statements carried that cut as a conjunct of
the invariant for EVERY right mode (`docs/VERDICT-EVIDENCE-AUDIT.md` Part II), which
reads: from states where the right is already inside `Hold`'s region.

The statement with the plain `mvValid` bookkeeping — the declared invariant from EVERY
state satisfying it, the right in any declared mode — is FALSE for these benchmarks:
at `(mv = Hold, θ_R < 0.6)` the right is frozen (`θ' = 0`) or decays (`θ' = ½(0.6 − θ)`)
while the left can still rise, so no response exists (`docs/CUT-COMPOSITION.md`,
countermodel). What IS true, and what the cut certificate supports, is the declared
invariant with the cut carried ONLY at the mode it was checked for: the mode-region
bookkeeping `mvRegion mv regions k` (`EnvelopeChainR.lean`) with `regions Hold = ⌊θ_R ≥
0.6⌋` and `regions q = ⊤` elsewhere. That is exactly the composition of the two cut
obligations: O1 says a switch INTO `Hold` lands in the region (the trust base's
guard-gated switching), O2 says `Hold`'s own flow keeps it — so the region is a sound
per-mode bookkeeping fact, and the declared invariant is unconditioned at the three
approach modes.

This leaf supplies the generic pieces the five `Instances/<Name>Declared.lean` leaves
compose:

* `hddF_multiR_plain` — the `hddF` discharger for the region-carrying postcondition
  over PLAIN (not guard-gated) left windows: `hddF_multiE`'s window side with
  `hddF_multiR`'s postcondition side. Both parents exist; this is their combination.
* `sem_bigSeq_identity` — a list of programs that each admit the identity run from any
  state in `domR` runs as a whole from such a state to itself (the zero-duration hops).
* `sem_rightBlock_rate` — the explicit witness for a right-only flow in a mode whose
  field is constant on one coordinate and zero elsewhere: the coordinate moves linearly
  for the chosen duration, every other coordinate is untouched. This is the response's
  REPOSITIONING phase in-kernel — the right-only (left frozen) flow the tool's
  `checkDynRepo` certifies by route A, written down as a curve rather than taken from
  Z3, so the composed theorems add NO verdict hypothesis.

New leaf over `EnvelopeChainR` and `UniformFvDischarge`; no upstream edits; the three
standard axioms.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainR
import RelCertifier.Proofs.Encoding.UniformFvDischarge

namespace RelCertifier
open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-! ## The `hddF` discharger — plain windows, region-carrying postcondition -/

/-- `hddF_multiE` with `mvRegionR` in place of `mvValidR`: plain clock-capped windows on
the left, the region conjunct on the right (regions read only right variables). -/
theorem hddF_multiR_plain (Gr : SearchGraph (Var n)) (a b : Fin n) (dt : ℝ)
    (leftData : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (regions : ℕ → Formula (Var n))
    (ϕinv : RFormula (Var n)) (domL domR : Formula (Var n)) (hab : a ≠ b)
    (htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt)
    (hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hL : ∀ d ∈ leftData, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv)
    (hreg : ∀ q < Gr.modes.length, (regions q).fv ⊆ range Rv)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv)
    (hdomLv : domL.fv ⊆ range Lv) (hdomRv : domR.fv ⊆ range Rv) :
    Disjoint (faShape (Program.star (bigChoice (leftData.map (fun d =>
          windowSeg (leftBlock d.1) d.2.1 ((Side.Aux, b) : Var n) dt d.2.2))))
        (Program.star (rightAutomatonBody Gr ((Side.Aux, a) : Var n)))
        (RFormula.and (RFormula.and ϕinv (envLR domL domR))
          (mvRegionR ((Side.Aux, a) : Var n) regions Gr.modes.length))).varsL
      (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (leftData.map (fun d =>
          windowSeg (leftBlock d.1) d.2.1 ((Side.Aux, b) : Var n) dt d.2.2))))
        (Program.star (rightAutomatonBody Gr ((Side.Aux, a) : Var n)))
        (RFormula.and (RFormula.and ϕinv (envLR domL domR))
          (mvRegionR ((Side.Aux, a) : Var n) regions Gr.modes.length))).varsR) := by
  rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by intro S; simp]
  refine sides_disjoint a b a hab.symm hab.symm ?_ ?_
  · rw [faShape_varsL', pvars_star']
    refine Set.union_subset ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_windowSegL_sub d.1 d.2.1 b dt d.2.2 (hL d hd).1 (hL d hd).2
    · intro v hv
      rcases ψmultiR_varsL_sub _ regions Gr.modes.length ϕinv domL domR hv with hv | hv
      · exact Or.inr (hinvL hv)
      · exact Or.inr (hdomLv hv)
  · rw [faShape_varsR', pvars_star']
    refine Set.union_subset ?_ ?_
    · intro v hv
      rcases vars_bodyU_sub Gr _ htt hRv hv with hv | hv
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
      · exact Or.inr hv
    · intro v hv
      rcases ψmultiR_varsR_sub _ regions Gr.modes.length ϕinv domL domR hreg hv
        with (hv | hv) | (hv | hv)
      · exact Or.inr (hinvR hv)
      · exact Or.inr (hdomRv hv)
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
      · exact Or.inr hv

/-! ## Zero-duration hops, glued -/

/-- Programs that each admit the identity run from every `domR` state run as a
sequence from such a state to itself. -/
theorem sem_bigSeq_identity (domR : Formula (Var n)) (ps : List (Program (Var n)))
    (hps : ∀ Q ∈ ps, ∀ μ : State (Var n), Formula.sat domR μ → Program.sem Q μ μ)
    (μ : State (Var n)) (hμ : Formula.sat domR μ) :
    Program.sem (bigSeq ps) μ μ := by
  induction ps with
  | nil =>
      simp only [bigSeq]
      rw [sem_test]; exact ⟨rfl, trivial⟩
  | cons Q rest ih =>
      simp only [bigSeq]
      exact ⟨μ, hps Q List.mem_cons_self μ hμ,
        ih (fun Q' hQ' => hps Q' (List.mem_cons_of_mem _ hQ'))⟩

/-! ## The constant-rate right-only flow, as an explicit curve -/

/-- The curve: coordinate `Rv i0` moves at rate `c` from `μ`, everything else frozen. -/
noncomputable def rateCurve (i0 : Fin n) (c : ℝ) (μ : State (Var n)) (t : ℝ) :
    State (Var n) :=
  fun x => if x = Rv i0 then μ (Rv i0) + c * t else μ x

theorem rateCurve_zero (i0 : Fin n) (c : ℝ) (μ : State (Var n)) :
    rateCurve i0 c μ 0 = μ := by
  funext x
  by_cases hx : x = Rv i0
  · subst hx; simp [rateCurve]
  · simp [rateCurve, if_neg hx]

theorem rateCurve_at (i0 : Fin n) (c : ℝ) (μ : State (Var n)) (t : ℝ) :
    rateCurve i0 c μ t (Rv i0) = μ (Rv i0) + c * t := by
  simp [rateCurve]

theorem rateCurve_other (i0 : Fin n) (c : ℝ) (μ : State (Var n)) (t : ℝ)
    {x : Var n} (hx : x ≠ Rv i0) : rateCurve i0 c μ t x = μ x := by
  simp [rateCurve, if_neg hx]

/-- **The right-only constant-rate run.** In a mode whose lowered right field is the
constant `c` on coordinate `i0` and `0` on every other coordinate, the right block (at
λ = 1) admits, from any `μ`, the run of duration `τ ≥ 0` along `rateCurve`, provided the
mode domain holds along it. The left is untouched (the right block binds only `Rv`s). -/
theorem sem_rightBlock_rate (fR : Fin n → Term (Var n)) (i0 : Fin n) (c : ℝ)
    (h0 : ∀ x : State (Var n), Term.eval (fR i0) x = c)
    (hj : ∀ j : Fin n, j ≠ i0 → ∀ x : State (Var n), Term.eval (fR j) x = 0)
    (domR : Formula (Var n)) (τ : ℝ) (hτ : 0 ≤ τ) (μ : State (Var n))
    (hdom : ∀ t ∈ Set.Icc (0:ℝ) τ, Formula.sat domR (rateCurve i0 c μ t)) :
    Program.sem (Program.ode (rightBlock fR (Term.const 1)) domR) μ
      (rateCurve i0 c μ τ) := by
  refine ⟨τ, rateCurve i0 c μ, hτ, rateCurve_zero i0 c μ, rfl, ?_, ?_, hdom⟩
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hi : i = i0
    · subst hi
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fR i))
          (rateCurve i c μ t) = c := by
        simp [Term.eval, AOp.interp, h0]
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => μ (Rv i) + c * u) (c * 1)
          (Set.Icc 0 τ) t :=
        ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)).const_mul c).const_add (μ (Rv i))
      rw [mul_one] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp [rateCurve]
      · simp [rateCurve]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fR i))
          (rateCurve i0 c μ t) = 0 := by
        simp [Term.eval, AOp.interp, hj i hi]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv i))) ?_ ?_
      · intro y _; simp [rateCurve, hi]
      · simp [rateCurve, hi]
  · intro t _ x hx
    have hx0 : x ≠ Rv i0 := by
      intro h; subst h
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨i0, List.mem_finRange i0, rfl⟩)
    simp [rateCurve, if_neg hx0]

end RelCertifier
