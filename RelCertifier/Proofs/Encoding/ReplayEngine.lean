/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Replaying an emitted cover over the guarded automata

The emitted cover of a left window `l` names, per right mode `q`, which certificates the tool
established at the window's stretch `λ`: the joint segment (`jointOK`, its flow facts the
pack `modalVerdX l q`) and the dynamic reposition (`dynPre`/`dynPost`, the pack
`modalVerdDynX l q`). Its derivation (`decideCovered`) answers a start `q` that is a joint node
with joint segments at nodes, each followed by a switch into a retained successor (all of
which are covered), and a start that is only a reposition node with a right-only flow of `q`
(the left frozen) into one of its exits, until a joint node is reached.

This file is the generic replay of such a derivation over the GUARDED right automaton,
after the left run (the response is chosen from the left run's end, `RRespP`):

* `replay_repo` (the pre-joint repositions): from a reposition node, a right-only run of the
  node's own flow ending where a retained exit's guard holds, the switch, and so on until a
  joint node; along every reposition the anchor of the pair `(l, q)` (rows and both sides'
  kept atoms) is preserved by the reposition pack (`hboxD`, from `couple_box_dyn`), the left
  held at the window's start.
* `replay_piece` (the joint segments of one clocked left piece): at a joint node the right
  keeps time with the left at the cover's stretch `λ` (a right run of duration `λ (b − a)`
  answers the left stretch `[a, b]`, `joint_of_sols_lam`), the anchor of `(l, q)` preserved by
  the joint pack (`hbox`, from `couple_box_cutX`); it switches into a retained successor where
  the instance's choreography `hmove` says (a higher-ranked joint node inside the window, any
  enabled successor at the piece's end).
* `replay_pieces` (the `k`-piece window), `replay_window` (repositions, then the pieces).

What the instance supplies is exactly what the cover does not: the existence of the right's
runs (explicit solutions allowed) and the legality of every switch against the entered mode's
guard (`hmove`, `hexit`); every preservation fact is a pack's.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.ReplayDyn

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-! ## Runs on merged states -/

/-- A right-only solution, lifted to merged states with the left part (and the auxiliaries)
held fixed. -/
theorem right_sol_merge {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hdomR : domR.fv ⊆ range Rv)
    {ρ : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ r Φ) (ω₀ y : State (Var n)) :
    ODESol (rightBlock fR (Term.const 1)) domR (mergeLR ω₀ y ρ) r
      (fun t => mergeLR ω₀ y (Φ t)) := by
  refine ⟨H.hr, by simp only [H.hΦ0], ?_, ?_, ?_⟩
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hmem : ((Rv i : Var n), Term.binop .mul (Term.const 1) (fR i)) ∈
        rightBlock fR (Term.const 1) := List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have hd := H.hder t ht _ hmem
    have hf : (fun u => mergeLR ω₀ y (Φ u) (Rv i)) = fun u => Φ u (Rv i) := by
      funext u; exact mergeLR_R ω₀ _ _ i
    have hval : Term.eval (Term.binop .mul (Term.const 1) (fR i)) (mergeLR ω₀ y (Φ t)) =
        Term.eval (Term.binop .mul (Term.const 1) (fR i)) (Φ t) := by
      refine Term.coincidence _ (fun v hv => ?_)
      rcases hv with hv | hv
      · simp [Term.fv] at hv
      · obtain ⟨j, rfl⟩ := hfR i hv
        exact mergeLR_R ω₀ _ _ j
    show HasDerivWithinAt (fun u => mergeLR ω₀ y (Φ u) (Rv i))
      (Term.eval (Term.binop .mul (Term.const 1) (fR i)) (mergeLR ω₀ y (Φ t))) (Icc 0 r) t
    rw [hf, hval]
    exact hd
  · intro t _ v hv
    obtain ⟨sd, i⟩ := v
    cases sd with
    | L => simp [mergeLR]
    | R =>
        exfalso; apply hv
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map, List.mem_finRange,
          true_and]
        exact ⟨i, rfl⟩
    | Aux => simp [mergeLR]
  · intro t ht
    refine (Formula.coincidence domR (fun v hv => ?_)).mpr (H.hdom t ht)
    obtain ⟨j, rfl⟩ := hdomR hv
    exact mergeLR_R ω₀ _ _ j

/-- A right-only solution at merged states is a frozen-left joint run (the left part in the
left envelope). -/
theorem right_sol_merge_joint {fR : Fin n → Term (Var n)} {domL domR : Formula (Var n)}
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hdomL : domL.fv ⊆ range Lv)
    (hdomR : domR.fv ⊆ range Rv)
    {ρ : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ r Φ) (ω₀ y : State (Var n))
    (hy : Formula.sat domL y) :
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (Formula.and domL domR)) (mergeLR ω₀ y ρ) (mergeLR ω₀ y (Φ r)) := by
  have hm := DLCalTiming.sem_ode_restrict (right_sol_merge hfR hdomR H ω₀ y) H.hr le_rfl
  refine hop_run_toJoint hfR (by simp [Term.fv]) hdomL ?_ hm
  refine (Formula.coincidence domL (fun v hv => ?_)).mpr hy
  obtain ⟨j, rfl⟩ := hdomL hv
  exact mergeLR_L ω₀ _ _ j

/-- Left coordinates of a right-only solution's end are its start's. -/
theorem right_sol_left {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    {ρ : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ r Φ) (i : Fin n) :
    Φ r (Lv i) = ρ (Lv i) := by
  refine H.hmask r ⟨H.hr, le_rfl⟩ _ (fun hb => ?_)
  obtain ⟨j, hj⟩ := rightBlock_bound_sub fR (Term.const 1) _ hb
  exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- **One synchronized stretch at stretch `λ`.** The anchor `A` of a joint node, a box
invariant of the pair's joint flow, at the merged state at left time `a` (right `ρ`) holds at
left time `b` with the right at the end of a run of duration `λ (b − a)`. -/
theorem joint_stretch {fL fR : Fin n → Term (Var n)} {domL domR : Formula (Var n)}
    (tg : Var n) (lam : ℝ) (hlam : 0 < lam)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hfR : ∀ i, (fR i).fv ⊆ range Rv)
    (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
    {x : State (Var n)} {r : ℝ} {ΦL : ℝ → State (Var n)}
    (hL : ODESol (clk tg (leftBlock fL)) domL x r ΦL) (ω₀ : State (Var n))
    (A : Formula (Var n))
    (hbox : ∀ σ ω, Formula.sat A σ →
      Program.sem (Program.ode (jointSys fL fR (Term.const lam)) (Formula.and domL domR)) σ ω →
      Formula.sat A ω)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ r) {ρ : State (Var n)}
    {ΦR : ℝ → State (Var n)}
    (hR : ODESol (rightBlock fR (Term.const 1)) domR ρ (lam * (b - a)) ΦR)
    (hA : Formula.sat A (mergeLR ω₀ (ΦL a) ρ)) :
    Formula.sat A (mergeLR ω₀ (ΦL b) (ΦR (lam * (b - a)))) := by
  have hLs := odeSol_shift hL ha hab hb
  have hj := joint_of_sols_lam tg lam hlam hfL hfR hdomL hdomR hLs hR ω₀
  have h0 : (fun t => ΦL (a + t)) 0 = ΦL a := by simp
  have h1 : (fun t => ΦL (a + t)) (b - a) = ΦL b := by simp
  have h2 : ΦR 0 = ρ := hR.hΦ0
  simp only [h0, h1, h2] at hj
  exact hbox _ _ hA hj

/-! ## The choreography the instance supplies -/

/-- **The instance's switching choreography for the joint segments.** From a joint node `q`
with the right at `ρ` (the instance's right-only precondition `Pre`), for every remaining right
duration `T ≥ 0`: either the right runs `q` for all of `T` and switches at the end into an
enabled successor whose entered state satisfies `E`, or it runs `q` for some `τ ≤ T` and
switches into an enabled successor that is a joint node of higher rank. -/
def HMove (G : SearchGraph (Var n)) (M : ℕ → RMode (Var n)) (J : ℕ → Prop) (rank : ℕ → ℕ)
    (Pre E : ℕ → State (Var n) → Prop) : Prop :=
  ∀ q, J q → ∀ ρ, Pre q ρ → ∀ T, 0 ≤ T →
    (∃ Φ, ODESol (M q).sys (M q).dom ρ T Φ ∧
      ∃ e ∈ G.edgesFrom q, SwitchLegal e (Φ T) ∧ E e.tgt (Φ T)) ∨
    (∃ τ, 0 ≤ τ ∧ τ ≤ T ∧ ∃ Φ, ODESol (M q).sys (M q).dom ρ τ Φ ∧
      ∃ e ∈ G.edgesFrom q, SwitchLegal e (Φ τ) ∧ J e.tgt ∧ rank q < rank e.tgt ∧
        Pre e.tgt (Φ τ))

/-- A switch test reads right coordinates only: legal at a right state iff at any merged state
with those right coordinates. -/
theorem switchLegal_merge {G : SearchGraph (Var n)} (hgR : GuardsRight G) {q : ℕ}
    {e : REdge (Var n)} (he : e ∈ G.edgesFrom q) (ω₀ y : State (Var n)) {ρ : State (Var n)} :
    SwitchLegal e (mergeLR ω₀ y ρ) ↔ SwitchLegal e ρ := by
  unfold SwitchLegal
  refine Formula.coincidence e.guard (fun v hv => ?_)
  obtain ⟨j, rfl⟩ := hgR q e he hv
  exact mergeLR_R ω₀ _ _ j

section Piece

variable (G : SearchGraph (Var n)) (M : ℕ → RMode (Var n)) (fR : ℕ → Fin n → Term (Var n))
  (domR : Formula (Var n)) (fL : Fin n → Term (Var n)) (domL : Formula (Var n)) (tg : Var n)
  (hgR : GuardsRight G)
  (hfL : ∀ i, (fL i).fv ⊆ range Lv)
  (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
  (lam : ℝ) (hlam : 0 < lam)
  (J : ℕ → Prop) (hfR : ∀ q, J q → ∀ i, (fR q i).fv ⊆ range Rv) (rank : ℕ → ℕ) (K : ℕ) (hrank : ∀ q, J q → rank q < K)
  (hmode : ∀ q, J q → G.modeAt q = some (M q))
  (hsys : ∀ q, J q → (M q).sys = rightBlock (fR q) (Term.const 1))
  (hdomM : ∀ q, J q → (M q).dom = domR)
  (A : ℕ → Formula (Var n))
  (hbox : ∀ q, J q → ∀ σ ω, Formula.sat (A q) σ →
    Program.sem (Program.ode (jointSys fL (fR q) (Term.const lam)) (Formula.and domL domR)) σ ω →
    Formula.sat (A q) ω)
  (hhand : ∀ q, J q → ∀ e ∈ G.edgesFrom q, ∀ y, Formula.sat (A q) y → SwitchLegal e y →
    Formula.sat (A e.tgt) y)

include hgR hfL hfR hdomL hdomR hlam hrank hmode hsys hdomM hbox hhand in
/-- **The joint segments of one clocked left piece.** From a joint node `q` at left time `a`
(right state `ρ` in `Pre`, the anchor of `q` at the merged state), the response keeps time with
the left at stretch `λ`, switching where the choreography says, and ends after the piece's end
`r` with a switch into a successor satisfying `E`, the anchor of the entered mode holding at the
merged state with the piece's end, and the left coordinates untouched. -/
theorem replay_piece (Pre E : ℕ → State (Var n) → Prop) (hmove : HMove G M J rank Pre E)
    {x : State (Var n)} {r : ℝ} {ΦL : ℝ → State (Var n)}
    (hL : ODESol (clk tg (leftBlock fL)) domL x r ΦL) (ω₀ : State (Var n)) :
    ∀ q, J q → ∀ a, 0 ≤ a → a ≤ r → ∀ ρ, Pre q ρ →
      Formula.sat (A q) (mergeLR ω₀ (ΦL a) ρ) →
      RRespP G q (fun q' μ => E q' μ ∧ Formula.sat (A q') (mergeLR ω₀ (ΦL r) μ) ∧
        ∀ i, μ (Lv i) = ρ (Lv i)) ρ := by
  intro q hq
  -- strong induction on `K − rank q`
  suffices H : ∀ k, ∀ q, J q → K - rank q = k → ∀ a, 0 ≤ a → a ≤ r → ∀ ρ, Pre q ρ →
      Formula.sat (A q) (mergeLR ω₀ (ΦL a) ρ) →
      RRespP G q (fun q' μ => E q' μ ∧ Formula.sat (A q') (mergeLR ω₀ (ΦL r) μ) ∧
        ∀ i, μ (Lv i) = ρ (Lv i)) ρ from H _ q hq rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro q hq hk a ha har ρ hPre hA
    have hT : 0 ≤ lam * (r - a) := mul_nonneg hlam.le (by linarith)
    rcases hmove q hq ρ hPre (lam * (r - a)) hT with
      ⟨Φ, hΦ, e, he, hleg, hE⟩ | ⟨τ, hτ0, hτT, Φ, hΦ, e, he, hleg, hJe, hrk, hPe⟩
    · -- the right runs to the piece's end, then the final switch
      have hΦ' : ODESol (rightBlock (fR q) (Term.const 1)) domR ρ (lam * (r - a)) Φ := by
        rw [← hsys q hq, ← hdomM q hq]; exact hΦ
      have hAend := joint_stretch tg lam hlam hfL (hfR q hq) hdomL hdomR hL ω₀ (A q) (hbox q hq)
        ha har le_rfl hΦ' hA
      have hstep := rrespP_step (P := fun q' μ => E q' μ ∧
          Formula.sat (A q') (mergeLR ω₀ (ΦL r) μ) ∧ ∀ i, μ (Lv i) = ρ (Lv i))
        (hmode q hq) he (DLCalTiming.sem_ode_restrict hΦ hΦ.hr le_rfl) hleg
      refine hstep (rrespP_stop ⟨hE, ?_, fun i => right_sol_left hΦ' i⟩)
      exact hhand q hq e he _ hAend ((switchLegal_merge hgR he ω₀ (ΦL r)).mpr hleg)
    · -- a switch inside the piece into a higher joint node
      set b : ℝ := a + τ / lam with hbdef
      have hτl : 0 ≤ τ / lam := div_nonneg hτ0 hlam.le
      have hab : a ≤ b := by linarith
      have hbr : b ≤ r := by
        have : τ / lam ≤ r - a := by
          rw [div_le_iff₀ hlam]; linarith
        linarith
      have hdur : lam * (b - a) = τ := by
        rw [hbdef]; field_simp; ring
      have hΦ' : ODESol (rightBlock (fR q) (Term.const 1)) domR ρ (lam * (b - a)) Φ := by
        rw [hdur, ← hsys q hq, ← hdomM q hq]; exact hΦ
      have hAb := joint_stretch tg lam hlam hfL (hfR q hq) hdomL hdomR hL ω₀ (A q) (hbox q hq)
        ha hab hbr hΦ' hA
      rw [hdur] at hAb
      have hAe := hhand q hq e he _ hAb ((switchLegal_merge hgR he ω₀ (ΦL b)).mpr hleg)
      have hlt : K - rank e.tgt < k := by
        have := hrank e.tgt hJe
        omega
      have hrest := ih _ hlt e.tgt hJe rfl b (by linarith) hbr (Φ τ) hPe hAe
      have hstep := rrespP_step (P := fun q' μ => E q' μ ∧
          Formula.sat (A q') (mergeLR ω₀ (ΦL r) μ) ∧ ∀ i, μ (Lv i) = ρ (Lv i))
        (hmode q hq) he (DLCalTiming.sem_ode_restrict hΦ hΦ.hr le_rfl) hleg
      refine hstep (rrespP_mono ?_ hrest)
      rintro q' μ ⟨hE, hA', hμL⟩
      refine ⟨hE, hA', fun i => ?_⟩
      rw [hμL i]
      have := right_sol_left hΦ' i
      rwa [hdur] at this

include hgR hfL hfR hdomL hdomR hlam hrank hmode hsys hdomM hbox hhand in
/-- **The joint segments of a window of `k + 1` clocked pieces.** Piece by piece; at every
piece boundary but the last the response switches into a joint node in `Pre` (`hmid`, needed
only when there is more than one piece), at the window's end into a successor satisfying
`Efin`. The anchor of the entered mode holds at the merged state with the window's end. -/
theorem replay_pieces (dt : ℝ) (Pre Efin : ℕ → State (Var n) → Prop)
    (hfin : HMove G M J rank Pre Efin)
    (hmid : ∀ k : ℕ, 0 < k → HMove G M J rank Pre (fun q' μ => J q' ∧ Pre q' μ))
    (hAfv : ∀ q, (A q).fv ⊆ range Lv ∪ range Rv)
    (htgL : ∀ i, tg ≠ Lv i) (ω₀ : State (Var n)) :
    ∀ (k : ℕ) (σ ν : State (Var n)),
      Program.sem (windowSeg (leftBlock fL) domL tg dt (k + 1)) σ ν →
      ∀ q, J q → ∀ ρ, Pre q ρ → Formula.sat (A q) (mergeLR ω₀ σ ρ) →
      RRespP G q (fun q' μ => Efin q' μ ∧ Formula.sat (A q') (mergeLR ω₀ ν μ) ∧
        ∀ i, μ (Lv i) = ρ (Lv i)) ρ := by
  intro k
  induction k with
  | zero =>
      intro σ ν hw q hq ρ hPre hA
      simp only [zero_add, windowSeg, List.replicate_one, bigSeq] at hw
      obtain ⟨mid, hseg, hrest⟩ := hw
      rw [sem_test] at hrest
      obtain ⟨rfl, -⟩ := hrest
      obtain ⟨r, ΦL, hL, hΦr, -⟩ := clockedSeg_sol hseg
      have hA0 : Formula.sat (A q) (mergeLR ω₀ (ΦL 0) ρ) := by
        refine (sat_of_agree (hAfv q) (y := mergeLR ω₀ σ ρ) (fun i => ?_) (fun i => ?_)).mpr hA
        · rw [mergeLR_L, mergeLR_L, hL.hΦ0, Function.update_of_ne (htgL i).symm]
        · rw [mergeLR_R, mergeLR_R]
      have h := replay_piece G M fR domR fL domL tg hgR hfL hdomL hdomR lam hlam J hfR rank K
        hrank hmode hsys hdomM A hbox hhand Pre Efin hfin hL ω₀ q hq 0 le_rfl hL.hr ρ hPre hA0
      rwa [hΦr] at h
  | succ k ih =>
      intro σ ν hw q hq ρ hPre hA
      have hw' : Program.sem (bigSeq (clockedSeg (leftBlock fL) domL tg dt ::
          List.replicate (k + 1) (clockedSeg (leftBlock fL) domL tg dt))) σ ν := hw
      obtain ⟨mid, hseg, hrest⟩ := hw'
      obtain ⟨r, ΦL, hL, hΦr, -⟩ := clockedSeg_sol hseg
      have hA0 : Formula.sat (A q) (mergeLR ω₀ (ΦL 0) ρ) := by
        refine (sat_of_agree (hAfv q) (y := mergeLR ω₀ σ ρ) (fun i => ?_) (fun i => ?_)).mpr hA
        · rw [mergeLR_L, mergeLR_L, hL.hΦ0, Function.update_of_ne (htgL i).symm]
        · rw [mergeLR_R, mergeLR_R]
      have h1 := replay_piece G M fR domR fL domL tg hgR hfL hdomL hdomR lam hlam J hfR rank K
        hrank hmode hsys hdomM A hbox hhand Pre (fun q' μ => J q' ∧ Pre q' μ)
        (hmid (k + 1) (Nat.succ_pos k)) hL ω₀ q hq 0 le_rfl hL.hr ρ hPre hA0
      rw [hΦr] at h1
      refine rrespP_bind' h1 ?_
      rintro q' μ ⟨⟨hJ', hPre'⟩, hA', hμL⟩
      have hrest' : Program.sem (windowSeg (leftBlock fL) domL tg dt (k + 1)) mid ν := hrest
      refine rrespP_mono ?_ (ih mid ν hrest' q' hJ' μ hPre' hA')
      rintro q'' μ' ⟨hE, hA'', hμ'L⟩
      exact ⟨hE, hA'', fun i => (hμ'L i).trans (hμL i)⟩

end Piece

/-! ## The repositions before the first joint segment -/

section Repo

variable (G : SearchGraph (Var n)) (M : ℕ → RMode (Var n)) (fR : ℕ → Fin n → Term (Var n))
  (domR domL gL : Formula (Var n)) (hgR : GuardsRight G)
  (hdomL : domL.fv ⊆ range Lv)
  (hdomR : domR.fv ⊆ range Rv) (hgL : gL.fv ⊆ range Lv)
  (J D : ℕ → Prop) (hfR : ∀ q, D q → ∀ i, (fR q i).fv ⊆ range Rv) (rankD : ℕ → ℕ)
  (hmodeD : ∀ q, D q → G.modeAt q = some (M q))
  (hsysD : ∀ q, D q → (M q).sys = rightBlock (fR q) (Term.const 1))
  (hdomD : ∀ q, D q → (M q).dom = domR)
  (A : ℕ → Formula (Var n))
  (hboxD : ∀ q, D q → ∀ σ ω, Formula.sat (A q) σ → Formula.sat gL σ →
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR q) (Term.const 1))
      (Formula.and domL domR)) σ ω → Formula.sat (A q) ω)
  (hhandD : ∀ q, D q → ∀ e ∈ G.edgesFrom q, ∀ y, Formula.sat (A q) y → SwitchLegal e y →
    Formula.sat (A e.tgt) y)

/-- **The instance's reposition exits.** From a reposition node `q` that is not a joint node,
with the right at `ρ` (`PreD`), a right-only run of `q` to a state where a retained exit `e` is
enabled, of lower reposition rank, entering a joint node in `Pre` or a reposition node in
`PreD`. -/
def HExit (G : SearchGraph (Var n)) (M : ℕ → RMode (Var n)) (J D : ℕ → Prop) (rankD : ℕ → ℕ)
    (Pre PreD : ℕ → State (Var n) → Prop) : Prop :=
  ∀ q, D q → ¬ J q → ∀ ρ, PreD q ρ → ∃ τ Φ, ODESol (M q).sys (M q).dom ρ τ Φ ∧
    ∃ e ∈ G.edgesFrom q, SwitchLegal e (Φ τ) ∧ e.tgt ≠ q ∧ rankD e.tgt < rankD q ∧
      ((J e.tgt ∧ Pre e.tgt (Φ τ)) ∨ (D e.tgt ∧ ¬ J e.tgt ∧ PreD e.tgt (Φ τ)))

include hgR hfR hdomL hdomR hgL hmodeD hsysD hdomD hboxD hhandD in
/-- **The pre-joint repositions.** From a joint node in `Pre` (no step) or a reposition node
in `PreD`, with the anchor at the merged state whose left part is the window's start `y` (in
the left guard and envelope), the right repositions alone along retained exits until a joint
node, the anchor preserved by every reposition pack. -/
theorem replay_repo (Pre PreD : ℕ → State (Var n) → Prop)
    (hexit : HExit G M J D rankD Pre PreD) (ω₀ y : State (Var n)) (hy : Formula.sat gL y)
    (hyL : Formula.sat domL y) :
    ∀ q ρ, ((J q ∧ Pre q ρ) ∨ (D q ∧ ¬ J q ∧ PreD q ρ)) →
      Formula.sat (A q) (mergeLR ω₀ y ρ) →
      RRespP G q (fun q' μ => J q' ∧ Pre q' μ ∧ Formula.sat (A q') (mergeLR ω₀ y μ) ∧
        ∀ i, μ (Lv i) = ρ (Lv i)) ρ := by
  intro q
  suffices H : ∀ k, ∀ q, rankD q = k → ∀ ρ, ((J q ∧ Pre q ρ) ∨ (D q ∧ ¬ J q ∧ PreD q ρ)) →
      Formula.sat (A q) (mergeLR ω₀ y ρ) →
      RRespP G q (fun q' μ => J q' ∧ Pre q' μ ∧ Formula.sat (A q') (mergeLR ω₀ y μ) ∧
        ∀ i, μ (Lv i) = ρ (Lv i)) ρ from H _ q rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro q hk ρ hcase hA
    rcases hcase with ⟨hJ, hPre⟩ | ⟨hD, hnJ, hPreD⟩
    · exact rrespP_stop ⟨hJ, hPre, hA, fun _ => rfl⟩
    · obtain ⟨τ, Φ, hΦ, e, he, hleg, -, hrk, hnext⟩ := hexit q hD hnJ ρ hPreD
      have hΦ' : ODESol (rightBlock (fR q) (Term.const 1)) domR ρ τ Φ := by
        rw [← hsysD q hD, ← hdomD q hD]; exact hΦ
      have hjoint := right_sol_merge_joint (hfR q hD) hdomL hdomR hΦ' ω₀ y hyL
      have hgLm : Formula.sat gL (mergeLR ω₀ y ρ) := by
        refine (Formula.coincidence gL (fun v hv => ?_)).mpr hy
        obtain ⟨j, rfl⟩ := hgL hv
        exact mergeLR_L ω₀ _ _ j
      have hAτ := hboxD q hD _ _ hA hgLm hjoint
      have hAe := hhandD q hD e he _ hAτ ((switchLegal_merge hgR he ω₀ y).mpr hleg)
      have hrest := ih _ (by omega) e.tgt rfl (Φ τ) hnext hAe
      have hstep := rrespP_step (P := fun q' μ => J q' ∧ Pre q' μ ∧
          Formula.sat (A q') (mergeLR ω₀ y μ) ∧ ∀ i, μ (Lv i) = ρ (Lv i))
        (hmodeD q hD) he (DLCalTiming.sem_ode_restrict hΦ hΦ.hr le_rfl) hleg
      refine hstep (rrespP_mono ?_ hrest)
      rintro q' μ ⟨h1, h2, h3, hμL⟩
      exact ⟨h1, h2, h3, fun i => (hμL i).trans (right_sol_left hΦ' i)⟩

end Repo

end RelCertifier

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-! ## The guarded step obligation of one gated window, by replay -/

/-- **One gated left window, answered by replaying the cover.** The window's own guard test
`gL` (the left program `?gL ; window`) puts the left in its guard at the window's start; from
the start configuration (`hstart`: a joint node in `Pre`, or a reposition node in `PreD`, and
the anchor of the pair), the right first repositions (pre-joint, `replay_repo`), then keeps
time with the window's `k + 1` pieces (`replay_pieces`); the instance turns the end condition
and the anchor at the window's end into the loop postcondition (`hpost`). -/
theorem replay_gresp (G : SearchGraph (Var n)) (M : ℕ → RMode (Var n))
    (fR : ℕ → Fin n → Term (Var n)) (domR : Formula (Var n)) (fL : Fin n → Term (Var n))
    (domL gL : Formula (Var n)) (b : Fin n)
    (hgR : GuardsRight G) (hfL : ∀ i, (fL i).fv ⊆ range Lv)
    (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv) (hgL : gL.fv ⊆ range Lv)
    (lam : ℝ) (hlam : 0 < lam)
    (J D : ℕ → Prop) (hfR : ∀ q, J q ∨ D q → ∀ i, (fR q i).fv ⊆ range Rv) (rank rankD : ℕ → ℕ) (K : ℕ) (hrank : ∀ q, J q → rank q < K)
    (hmode : ∀ q, J q ∨ D q → G.modeAt q = some (M q))
    (hsys : ∀ q, J q ∨ D q → (M q).sys = rightBlock (fR q) (Term.const 1))
    (hdomM : ∀ q, J q ∨ D q → (M q).dom = domR)
    (A : ℕ → Formula (Var n)) (hAfv : ∀ q, (A q).fv ⊆ range Lv ∪ range Rv)
    (hbox : ∀ q, J q → ∀ σ ω, Formula.sat (A q) σ →
      Program.sem (Program.ode (jointSys fL (fR q) (Term.const lam)) (Formula.and domL domR))
        σ ω → Formula.sat (A q) ω)
    (hboxD : ∀ q, D q → ∀ σ ω, Formula.sat (A q) σ → Formula.sat gL σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR q) (Term.const 1))
        (Formula.and domL domR)) σ ω → Formula.sat (A q) ω)
    (hhand : ∀ q, J q ∨ D q → ∀ e ∈ G.edgesFrom q, ∀ y, Formula.sat (A q) y →
      SwitchLegal e y → Formula.sat (A e.tgt) y)
    (Pre PreD Efin : ℕ → State (Var n) → Prop)
    (hPreR : ∀ q x y, (∀ i, x (Rv i) = y (Rv i)) → Pre q x → Pre q y)
    (hPreDR : ∀ q x y, (∀ i, x (Rv i) = y (Rv i)) → PreD q x → PreD q y)
    (hfin : HMove G M J rank Pre Efin)
    (hmid : ∀ k : ℕ, 0 < k → HMove G M J rank Pre (fun q' μ => J q' ∧ Pre q' μ))
    (hexit : HExit G M J D rankD Pre PreD)
    (dt : ℝ) (k : ℕ) (q : ℕ) (σ : State (Var n))
    (hstart : Formula.sat gL σ →
      ((J q ∧ Pre q σ) ∨ (D q ∧ ¬ J q ∧ PreD q σ)) ∧ Formula.sat (A q) σ)
    (hσL : Formula.sat domL σ)
    (post : ℕ → Formula (Var n))
    (hpost : ∀ ν, Program.sem (windowSeg (leftBlock fL) domL ((Side.Aux, b) : Var n) dt (k+1)) σ ν →
      ∀ q' μ, (∀ i, μ (Lv i) = ν (Lv i)) → Efin q' μ →
        Formula.sat (A q') (mergeLR σ ν μ) → Formula.sat (post q') μ) :
    GResp G q (gwindowSeg gL (leftBlock fL) domL ((Side.Aux, b) : Var n) dt (k+1)) post σ := by
  refine gresp_gate (fun hg => gresp_of_rresp (fun ν hwin => ?_))
  obtain ⟨hcase, hAσ⟩ := hstart hg
  set tg : Var n := ((Side.Aux, b) : Var n)
  have hP := vars_windowSegL_sub fL domL b dt (k+1) hfL hdomL
  have hR : ∀ i, ν (Rv i) = σ (Rv i) := by
    intro i
    refine (Program.bound_effect _ hwin (Rv i) ?_).symm
    intro hb
    rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
    · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
  have hA0 : Formula.sat (A q) (mergeLR σ σ ν) := by
    refine (sat_of_agree (hAfv q) (y := σ) (fun i => ?_) (fun i => ?_)).mpr hAσ
    · rw [mergeLR_L]
    · rw [mergeLR_R, hR i]
  have hcase' : (J q ∧ Pre q ν) ∨ (D q ∧ ¬ J q ∧ PreD q ν) := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, hPreR q σ ν (fun i => (hR i).symm) h2⟩
    · exact Or.inr ⟨h1, h2, hPreDR q σ ν (fun i => (hR i).symm) h3⟩
  have hrepo := replay_repo G M fR domR domL gL hgR hdomL hdomR hgL J D
    (fun q hq => hfR q (Or.inr hq)) rankD
    (fun q hq => hmode q (Or.inr hq)) (fun q hq => hsys q (Or.inr hq))
    (fun q hq => hdomM q (Or.inr hq)) A hboxD (fun q hq => hhand q (Or.inr hq)) Pre PreD hexit
    σ σ hg hσL q ν hcase' hA0
  have htgL : ∀ i, tg ≠ Lv i := fun i h => by simp [tg, Lv, Prod.ext_iff] at h
  refine rresp_of_rrespP (rrespP_bind' hrepo ?_)
  rintro q' μ ⟨hJ', hPre', hA', hμL⟩
  have hpieces := replay_pieces G M fR domR fL domL tg hgR hfL hdomL hdomR lam hlam J
    (fun q hq => hfR q (Or.inl hq)) rank K
    hrank (fun q hq => hmode q (Or.inl hq)) (fun q hq => hsys q (Or.inl hq))
    (fun q hq => hdomM q (Or.inl hq)) A hbox (fun q hq => hhand q (Or.inl hq)) dt Pre Efin
    hfin hmid hAfv htgL σ k σ ν hwin q' hJ' μ hPre' hA'
  refine rrespP_mono ?_ hpieces
  rintro q'' μ' ⟨hE, hA'', hμ'L⟩
  exact hpost ν hwin q'' μ' (fun i => (hμ'L i).trans (hμL i)) hE hA''

end RelCertifier
