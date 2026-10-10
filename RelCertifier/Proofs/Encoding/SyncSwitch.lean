/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Synchronized responses that switch inside a window

A guarded right automaton may have to switch inside a left window (its band guard stops
holding while the left still flows). When the declared rows force the right to keep time with
the left (an equality or an energy row on coordinates both sides integrate at the same rate),
the response cannot run ahead: it follows the left window's own clock, and at the switch
points it changes mode. The certified couplings still apply piecewise: on every stretch where
the right stays in mode `q`, the joint trajectory (left coordinates from the left run, right
coordinates from the right run) is a run of the joint system of the pair `(l, q)`, along
which the pair's anchor (rows and both sides' kept cut atoms) is preserved.

* `couple_box_cutX`: the anchor of a certified pair is preserved along every run of the joint
  system (the first half of `couple_cutX`, without the existence part).
* `odeSol_shift`: a solution restricted to a sub-interval, re-based at its left end.
* `mergeLR`, `joint_of_sols`: a clocked left solution and a right solution of the same
  duration make a run of the joint system between the merged states (the clock and the other
  auxiliary variables frozen).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedClimb

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-- **The anchor of a certified pair is a box invariant of the joint flow.** Same premises as
`couple_cutX` without the existence part: along every run of the joint system (left field
`fL`, right field stretched by `λ`), from a state satisfying the rows and both sides' kept
atoms, the rows and atoms hold at the end. -/
theorem couple_box_cutX (g : Term (Var n)) (gs comps : List (Term (Var n)))
    (cL cR : List (CutAtomP n)) (fL fR : Fin n → Term (Var n)) (lamv : ℝ)
    (domL domR : Formula (Var n))
    (hsub1 : ∀ c ∈ comps, c ∈ g :: gs) (hsub2 : ∀ g' ∈ g :: gs, g' ∈ comps)
    (hiffL : AtomsIff cL) (hiffR : AtomsIff cR)
    (hstayL : AtomsStayC cL (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
    (hstayR : AtomsStayC cR (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
    (hverd : VerdXCore comps fL fR lamv (domCutX (Formula.and domL domR) cL cR)) :
    ∀ σ ω, Formula.sat (FM g (gs ++ atomTerms cL cR)) σ →
      Program.sem (Program.ode (jointSys fL fR (Term.const lamv)) (Formula.and domL domR)) σ ω →
      Formula.sat (FM g (gs ++ atomTerms cL cR)) ω := by
  intro σ ω hσ hω
  have hnarrow : SegPreservesAllOn comps (jointSys fL fR (Term.const lamv))
      (domCutX (Formula.and domL domR) cL cR) :=
    segPresAll_from_strata_verdicts' fL fR (Term.const lamv) _ comps hverd
  have hnarrow' : SegPreservesAllOn comps (jointSys fL fR (Term.const lamv))
      (Formula.and (Formula.and domL domR) (Formula.and (cutF cL) (cutF cR))) := by
    refine segPresAll_congr (fun x => ?_) hnarrow
    rw [sat_domCutX]
    simp only [Formula.sat, sat_cutF]
  have hlift := segPresAll_cut_liftX hiffL hiffR hstayL hstayR hnarrow'
  obtain ⟨hFσ, hatσ⟩ := (sat_FM_append g gs _ σ).mp hσ
  obtain ⟨hLσ, hRσ⟩ := (atomTerms_iff hiffL hiffR σ).mp hatσ
  have hcompsσ : ∀ c ∈ comps, Term.eval c σ ≤ 0 :=
    fun c hc => (sat_FM_iff g gs σ).mp hFσ c (hsub1 c hc)
  obtain ⟨hcω, hLω, hRω⟩ := hlift σ hLσ hRσ hcompsσ ω hω
  refine (sat_FM_append g gs _ ω).mpr ⟨(sat_FM_iff g gs ω).mpr ?_,
    (atomTerms_iff hiffL hiffR ω).mpr ⟨hLω, hRω⟩⟩
  intro g' hg'
  exact hcω g' (hsub2 g' hg')

/-- A solution restricted to `[a, b] ⊆ [0, r]`, re-based at `a`. -/
theorem odeSol_shift {sys : ODESystem (Var n)} {dom : Formula (Var n)} {ω : State (Var n)}
    {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom ω r Φ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ r) :
    ODESol sys dom (Φ a) (b - a) (fun t => Φ (a + t)) := by
  refine ⟨by linarith, by simp, ?_, ?_, ?_⟩
  · intro t ht p hp
    have hmem : a + t ∈ Icc (0 : ℝ) r := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc : HasDerivWithinAt (fun u : ℝ => a + u) 1 (Icc 0 (b - a)) t :=
      (hasDerivWithinAt_id t (Icc 0 (b - a))).const_add a
    have hmaps : MapsTo (fun u : ℝ => a + u) (Icc 0 (b - a)) (Icc 0 r) :=
      fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hcomp := (H.hder (a + t) hmem p hp).comp t hc hmaps
    rw [mul_one] at hcomp
    exact hcomp
  · intro t ht x hx
    have hmem : a + t ∈ Icc (0 : ℝ) r := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hamem : a ∈ Icc (0 : ℝ) r := ⟨ha, by linarith⟩
    change Φ (a + t) x = Φ a x
    rw [H.hmask (a + t) hmem x hx, H.hmask a hamem x hx]
  · intro t ht
    exact H.hdom (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The merged state: left coordinates from `a`, right coordinates from `b`, every other
variable from `ω₀`. -/
noncomputable def mergeLR (ω₀ a b : State (Var n)) : State (Var n) :=
  fun v => if v.1 = Side.L then a v else if v.1 = Side.R then b v else ω₀ v

theorem mergeLR_L (ω₀ a b : State (Var n)) (i : Fin n) : mergeLR ω₀ a b (Lv i) = a (Lv i) := by
  simp [mergeLR, Lv]
theorem mergeLR_R (ω₀ a b : State (Var n)) (i : Fin n) : mergeLR ω₀ a b (Rv i) = b (Rv i) := by
  simp [mergeLR, Rv]
theorem mergeLR_aux (ω₀ a b : State (Var n)) (i : Fin n) :
    mergeLR ω₀ a b ((Side.Aux, i) : Var n) = ω₀ ((Side.Aux, i) : Var n) := by
  simp [mergeLR]

/-- A formula over left and right coordinates has the same truth value at every state agreeing
on them. -/
theorem sat_of_agree {φ : Formula (Var n)} (hφ : φ.fv ⊆ range Lv ∪ range Rv)
    {x y : State (Var n)} (hL : ∀ i, x (Lv i) = y (Lv i)) (hR : ∀ i, x (Rv i) = y (Rv i)) :
    Formula.sat φ x ↔ Formula.sat φ y := by
  refine Formula.coincidence φ (fun v hv => ?_)
  rcases hφ hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact hL i
  · exact hR i

/-- **The joint run of two solutions of the same duration.** A clocked left solution and a
right solution (unit stretch) of the same duration `r` make a run of the joint system between
the merged states; the clock and the other auxiliary variables stay at `ω₀`. -/
theorem joint_of_sols {fL fR : Fin n → Term (Var n)} {domL domR : Formula (Var n)}
    (tg : Var n) (htgL : ∀ i, tg ≠ Lv i) (htgR : ∀ i, tg ≠ Rv i)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hfR : ∀ i, (fR i).fv ⊆ range Rv)
    (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
    {x y : State (Var n)} {r : ℝ} {ΦL ΦR : ℝ → State (Var n)}
    (hL : ODESol (clk tg (leftBlock fL)) domL x r ΦL)
    (hR : ODESol (rightBlock fR (Term.const 1)) domR y r ΦR) (ω₀ : State (Var n)) :
    Program.sem (Program.ode (jointSys fL fR (Term.const 1)) (Formula.and domL domR))
      (mergeLR ω₀ (ΦL 0) (ΦR 0)) (mergeLR ω₀ (ΦL r) (ΦR r)) := by
  refine ⟨r, fun t => mergeLR ω₀ (ΦL t) (ΦR t), hL.hr, rfl, rfl, ?_, ?_, ?_⟩
  · intro t ht p hp
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · -- a left row `(Lv i, fL i)`
      simp only [leftBlock, List.mem_map, List.mem_finRange, true_and] at hp
      obtain ⟨i, rfl⟩ := hp
      have hmem : ((Lv i : Var n), fL i) ∈ clk tg (leftBlock fL) := by
        simp only [clk, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
      have hd := hL.hder t ht _ hmem
      have hf : (fun u => mergeLR ω₀ (ΦL u) (ΦR u) (Lv i)) = fun u => ΦL u (Lv i) := by
        funext u; exact mergeLR_L ω₀ _ _ i
      have hval : Term.eval (fL i) (mergeLR ω₀ (ΦL t) (ΦR t)) = Term.eval (fL i) (ΦL t) := by
        refine Term.coincidence (fL i) (fun v hv => ?_)
        obtain ⟨j, rfl⟩ := hfL i hv
        exact mergeLR_L ω₀ _ _ j
      show HasDerivWithinAt (fun u => mergeLR ω₀ (ΦL u) (ΦR u) (Lv i))
        (Term.eval (fL i) (mergeLR ω₀ (ΦL t) (ΦR t))) (Icc 0 r) t
      rw [hf, hval]
      exact hd
    · -- a right row `(Rv i, 1 · fR i)`
      simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
      obtain ⟨i, rfl⟩ := hp
      have hmem : ((Rv i : Var n), Term.binop .mul (Term.const 1) (fR i)) ∈
          rightBlock fR (Term.const 1) := List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
      have hd := hR.hder t ht _ hmem
      have hf : (fun u => mergeLR ω₀ (ΦL u) (ΦR u) (Rv i)) = fun u => ΦR u (Rv i) := by
        funext u; exact mergeLR_R ω₀ _ _ i
      have hval : Term.eval (Term.binop .mul (Term.const 1) (fR i)) (mergeLR ω₀ (ΦL t) (ΦR t)) =
          Term.eval (Term.binop .mul (Term.const 1) (fR i)) (ΦR t) := by
        refine Term.coincidence _ (fun v hv => ?_)
        rcases hv with hv | hv
        · simp [Term.fv] at hv
        · obtain ⟨j, rfl⟩ := hfR i hv
          exact mergeLR_R ω₀ _ _ j
      show HasDerivWithinAt (fun u => mergeLR ω₀ (ΦL u) (ΦR u) (Rv i))
        (Term.eval (Term.binop .mul (Term.const 1) (fR i)) (mergeLR ω₀ (ΦL t) (ΦR t))) (Icc 0 r) t
      rw [hf, hval]
      exact hd
  · intro t _ v hv
    obtain ⟨sd, i⟩ := v
    cases sd with
    | L =>
        exfalso; apply hv
        simp [ODESystem.bound, jointSys, Lv]
    | R =>
        exfalso; apply hv
        simp [ODESystem.bound, jointSys, Rv]
    | Aux => simp [mergeLR]
  · intro t ht
    refine ⟨?_, ?_⟩
    · refine (Formula.coincidence domL (fun v hv => ?_)).mpr (hL.hdom t ht)
      obtain ⟨j, rfl⟩ := hdomL hv
      exact mergeLR_L ω₀ _ _ j
    · refine (Formula.coincidence domR (fun v hv => ?_)).mpr (hR.hdom t ht)
      obtain ⟨j, rfl⟩ := hdomR hv
      exact mergeLR_R ω₀ _ _ j

/-- **The joint run of two solutions, the right stretched by `λ > 0`.** A clocked left solution
of duration `r` and a right solution of duration `λ r` make a run of the joint system with the
right field stretched by `λ` (the right read at time `λ t`). -/
theorem joint_of_sols_lam {fL fR : Fin n → Term (Var n)} {domL domR : Formula (Var n)}
    (tg : Var n) (lam : ℝ) (hlam : 0 < lam)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hfR : ∀ i, (fR i).fv ⊆ range Rv)
    (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
    {x y : State (Var n)} {r : ℝ} {ΦL ΦR : ℝ → State (Var n)}
    (hL : ODESol (clk tg (leftBlock fL)) domL x r ΦL)
    (hR : ODESol (rightBlock fR (Term.const 1)) domR y (lam * r) ΦR) (ω₀ : State (Var n)) :
    Program.sem (Program.ode (jointSys fL fR (Term.const lam)) (Formula.and domL domR))
      (mergeLR ω₀ (ΦL 0) (ΦR 0)) (mergeLR ω₀ (ΦL r) (ΦR (lam * r))) := by
  have hmaps : Set.MapsTo (fun u : ℝ => lam * u) (Icc 0 r) (Icc 0 (lam * r)) :=
    fun u hu => ⟨mul_nonneg hlam.le hu.1, mul_le_mul_of_nonneg_left hu.2 hlam.le⟩
  refine ⟨r, fun t => mergeLR ω₀ (ΦL t) (ΦR (lam * t)), hL.hr, by simp, rfl, ?_, ?_, ?_⟩
  · intro t ht p hp
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · simp only [leftBlock, List.mem_map, List.mem_finRange, true_and] at hp
      obtain ⟨i, rfl⟩ := hp
      have hmem : ((Lv i : Var n), fL i) ∈ clk tg (leftBlock fL) := by
        simp only [clk, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
      have hd := hL.hder t ht _ hmem
      have hf : (fun u => mergeLR ω₀ (ΦL u) (ΦR (lam * u)) (Lv i)) = fun u => ΦL u (Lv i) := by
        funext u; exact mergeLR_L ω₀ _ _ i
      have hval : Term.eval (fL i) (mergeLR ω₀ (ΦL t) (ΦR (lam * t))) =
          Term.eval (fL i) (ΦL t) := by
        refine Term.coincidence (fL i) (fun v hv => ?_)
        obtain ⟨j, rfl⟩ := hfL i hv
        exact mergeLR_L ω₀ _ _ j
      show HasDerivWithinAt (fun u => mergeLR ω₀ (ΦL u) (ΦR (lam * u)) (Lv i))
        (Term.eval (fL i) (mergeLR ω₀ (ΦL t) (ΦR (lam * t)))) (Icc 0 r) t
      rw [hf, hval]
      exact hd
    · simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
      obtain ⟨i, rfl⟩ := hp
      have hmem : ((Rv i : Var n), Term.binop .mul (Term.const 1) (fR i)) ∈
          rightBlock fR (Term.const 1) := List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
      have hd := hR.hder (lam * t) (hmaps ht) _ hmem
      have hc : HasDerivWithinAt (fun u : ℝ => lam * u) lam (Icc 0 r) t := by
        simpa using (hasDerivWithinAt_id t (Icc (0:ℝ) r)).const_mul lam
      have hcomp := hd.comp t hc hmaps
      have hf : (fun u => mergeLR ω₀ (ΦL u) (ΦR (lam * u)) (Rv i)) =
          (fun u => ΦR u (Rv i)) ∘ (fun u => lam * u) := by
        funext u; exact mergeLR_R ω₀ _ _ i
      have hval : Term.eval (Term.binop .mul (Term.const lam) (fR i))
          (mergeLR ω₀ (ΦL t) (ΦR (lam * t))) =
          Term.eval (Term.binop .mul (Term.const 1) (fR i)) (ΦR (lam * t)) * lam := by
        have hco : Term.eval (fR i) (mergeLR ω₀ (ΦL t) (ΦR (lam * t))) =
            Term.eval (fR i) (ΦR (lam * t)) := by
          refine Term.coincidence (fR i) (fun v hv => ?_)
          obtain ⟨j, rfl⟩ := hfR i hv
          exact mergeLR_R ω₀ _ _ j
        simp only [Term.eval, AOp.interp, hco]
        ring
      show HasDerivWithinAt (fun u => mergeLR ω₀ (ΦL u) (ΦR (lam * u)) (Rv i))
        (Term.eval (Term.binop .mul (Term.const lam) (fR i))
          (mergeLR ω₀ (ΦL t) (ΦR (lam * t)))) (Icc 0 r) t
      rw [hf, hval]
      exact hcomp
  · intro t _ v hv
    obtain ⟨sd, i⟩ := v
    cases sd with
    | L =>
        exfalso; apply hv
        simp [ODESystem.bound, jointSys, Lv]
    | R =>
        exfalso; apply hv
        simp [ODESystem.bound, jointSys, Rv]
    | Aux => simp [mergeLR]
  · intro t ht
    refine ⟨?_, ?_⟩
    · refine (Formula.coincidence domL (fun v hv => ?_)).mpr (hL.hdom t ht)
      obtain ⟨j, rfl⟩ := hdomL hv
      exact mergeLR_L ω₀ _ _ j
    · refine (Formula.coincidence domR (fun v hv => ?_)).mpr (hR.hdom (lam * t) (hmaps ht))
      obtain ⟨j, rfl⟩ := hdomR hv
      exact mergeLR_R ω₀ _ _ j

end RelCertifier
