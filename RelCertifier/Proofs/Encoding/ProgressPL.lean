/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Progress with a PRE-LANDING right-only flow certificate (opt-in `prelanding = true`)

`Progress.lean` discharges `RepoProgress` from the progress certificate and a WHOLE-DOMAIN
right-only flow certificate: its section premise `hboxD` keeps the anchor along every
frozen-left run. This file proves the same closers (`repoProgress_oneB`, `repoProgress_twoB`,
`repoProgress_one_downB`) from a weaker premise, `hboxB`: the anchor is kept along a right-only
run only while the run stays in a region `Bf` before its last instant (`∀ t ∈ [0, T), Bf (Φ t)`;
the end point itself may lie outside). The certificate's last stage supplies `Bf`: the
half-open region before its threshold (`x < θ` upward, `x > θ` downward), so the run may be
checked only BEFORE it lands.

The witness run changes in one place: the landing cycle stops at the FIRST entry into the
closed target `x ≥ θ` (`first_hit`, the `sInf` of the closed hitting set, the pattern of
`Flow/DIStrictOpen.lean`), not at an arbitrary crossing of the line (`hits_line`, the
intermediate value theorem). Before that instant the run is in `Bf`, so the anchor holds at
the stop point, where the line `x = θ` is reached and an exit is enabled (the land query); the
right ends that cycle early (a legal duration `≤ ε_R`). Every other cycle of the argument has
`x < θ` on its whole interval (it does not cross), so `Bf` holds throughout it.

`RepoProgress` and its consumers (`CoverResp`, `theorem3_of_coverX`) are untouched; the
whole-domain closers of `Progress.lean` are untouched too (this file is additive).
-/
import RelCertifier.Proofs.Encoding.Progress

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-! ## The first entry into a closed threshold set -/

/-- **The first hit, upward.** A coordinate that starts below `θ` and reaches `θ` within the
run reaches the line `x = θ` at a FIRST time `t'`: before `t'` it is strictly below. -/
theorem first_hit {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    {ρ : State (Var n)} {T : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ) (j : Fin n) (θ : ℝ)
    (h0 : ρ (Rv j) < θ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hθ : θ ≤ Φ t (Rv j)) :
    ∃ t' ∈ Icc (0 : ℝ) T, Φ t' (Rv j) = θ ∧ ∀ s ∈ Ico (0 : ℝ) t', Φ s (Rv j) < θ := by
  have hcont := H.coord_continuousOn j
  set S : Set ℝ := Icc (0 : ℝ) T ∩ (fun u => Φ u (Rv j)) ⁻¹' Ici θ with hSdef
  have hSclosed : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have htS : t ∈ S := ⟨ht, hθ⟩
  have hSbdd : BddBelow S := ⟨0, fun u hu => hu.1.1⟩
  have hsS : sInf S ∈ S := hSclosed.csInf_mem ⟨t, htS⟩ hSbdd
  have hlb : ∀ u ∈ S, sInf S ≤ u := fun u hu => csInf_le hSbdd hu
  set t' := sInf S with ht'
  have hbefore : ∀ s ∈ Ico (0 : ℝ) t', Φ s (Rv j) < θ := by
    intro s hs
    by_contra hcon
    have hsS' : s ∈ S := ⟨⟨hs.1, hs.2.le.trans hsS.1.2⟩, not_lt.mp hcon⟩
    exact absurd (hlb s hsS') (not_le.mpr hs.2)
  refine ⟨t', hsS.1, le_antisymm ?_ hsS.2, hbefore⟩
  -- the line is reached on `[0, t']` (intermediate value), and not before `t'`
  have hc' : ContinuousOn (fun u => Φ u (Rv j)) (Icc 0 t') :=
    hcont.mono (Icc_subset_Icc le_rfl hsS.1.2)
  obtain ⟨u, hu, hcu⟩ := intermediate_value_Icc hsS.1.1 hc'
    ⟨by simp only [H.hΦ0]; exact h0.le, hsS.2⟩
  have huS : u ∈ S := ⟨⟨hu.1, hu.2.trans hsS.1.2⟩, by simp [hcu]⟩
  have hut : u = t' := le_antisymm hu.2 (hlb u huS)
  rw [← hut]; exact hcu.le

/-- **The first hit, downward** (the mirror of `first_hit`). -/
theorem first_hit_down {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    {ρ : State (Var n)} {T : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ) (j : Fin n) (θ : ℝ)
    (h0 : θ < ρ (Rv j)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hθ : Φ t (Rv j) ≤ θ) :
    ∃ t' ∈ Icc (0 : ℝ) T, Φ t' (Rv j) = θ ∧ ∀ s ∈ Ico (0 : ℝ) t', θ < Φ s (Rv j) := by
  have hcont := H.coord_continuousOn j
  set S : Set ℝ := Icc (0 : ℝ) T ∩ (fun u => Φ u (Rv j)) ⁻¹' Iic θ with hSdef
  have hSclosed : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have htS : t ∈ S := ⟨ht, hθ⟩
  have hSbdd : BddBelow S := ⟨0, fun u hu => hu.1.1⟩
  have hsS : sInf S ∈ S := hSclosed.csInf_mem ⟨t, htS⟩ hSbdd
  have hlb : ∀ u ∈ S, sInf S ≤ u := fun u hu => csInf_le hSbdd hu
  set t' := sInf S with ht'
  have hbefore : ∀ s ∈ Ico (0 : ℝ) t', θ < Φ s (Rv j) := by
    intro s hs
    by_contra hcon
    have hsS' : s ∈ S := ⟨⟨hs.1, hs.2.le.trans hsS.1.2⟩, not_lt.mp hcon⟩
    exact absurd (hlb s hsS') (not_le.mpr hs.2)
  refine ⟨t', hsS.1, le_antisymm hsS.2 ?_, hbefore⟩
  have hc' : ContinuousOn (fun u => Φ u (Rv j)) (Icc 0 t') :=
    hcont.mono (Icc_subset_Icc le_rfl hsS.1.2)
  obtain ⟨u, hu, hcu⟩ := intermediate_value_Icc' hsS.1.1 hc'
    ⟨hsS.2, by simp only [H.hΦ0]; exact h0.le⟩
  have huS : u ∈ S := ⟨⟨hu.1, hu.2.trans hsS.1.2⟩, by simp [hcu]⟩
  have hut : u = t' := le_antisymm hu.2 (hlb u huS)
  rw [← hut]; exact hcu.ge

/-! ## The node's context, with the pre-landing premise -/

section NodeB

variable (G : SearchGraph (Var n)) (fR : Fin n → Term (Var n)) (domL domR gL : Formula (Var n))
  (guard : ℕ → Formula (Var n)) (q : ℕ) (m : RMode (Var n)) (hm : G.modeAt q = some m)
  (hsys : m.sys = rightBlock fR (Term.const 1)) (hdomM : m.dom = domR)
  (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
  (hgL : gL.fv ⊆ range Lv) (hguardR : ∀ q', (guard q').fv ⊆ range Rv)
  (hgR : GuardsRight G) (hguards : ∀ e ∈ G.edgesFrom q, e.guard = guard e.tgt)
  (A : Formula (Var n)) (hAfv : A.fv ⊆ range Lv ∪ range Rv)
  (hAdom : ∀ y, Formula.sat A y → Formula.sat domL y ∧ Formula.sat domR y)
  (pre : Bool)
  (epsR : ℝ) (hε : 0 < epsR)
  (tr : Var n) (htrL : tr ∉ range Lv) (htrR : tr ∉ range Rv)
  (reg : Formula (Var n)) (hregR : reg.fv ⊆ range Rv)
  (hAreg : ∀ y, Formula.sat A y → Formula.sat reg y)
  (hex : ∀ x, Formula.sat (guard q) x → Formula.sat domR x → Formula.sat reg x →
    ∃ Φ, ODESol (rightBlock fR (Term.const 1)) domR x epsR Φ)
  (hcomp : ∀ x, Formula.sat (guard q) x → Formula.sat domR x → Formula.sat reg x → ∀ t Φ, t ≤ epsR →
    ODESol (rightBlock fR (Term.const 1)) domR x t Φ →
    ∃ e ∈ G.edgesFrom q, Formula.sat (guard e.tgt) (Φ t))
  -- the PRE-LANDING right-only flow certificate: the anchor is kept along a right-only run
  -- that stays in `Bf` before its last instant
  (Bf : State (Var n) → Prop)
  (hboxB : ∀ y ρ, (∀ i, y (Rv i) = ρ (Rv i)) → Formula.sat A y → (pre = true → Formula.sat gL y) →
    ∀ T Φ, ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ →
    (∀ t ∈ Ico (0 : ℝ) T, Bf (Φ t)) → Formula.sat A (mergeLR y y (Φ T)))
  (hpruneD : ∀ e ∈ G.edgesFrom q, e.pruned = true → ∀ σ ω, Formula.sat A σ →
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (Formula.and domL domR)) σ ω → ¬ Formula.sat e.guard ω)
  (R : Formula (Var n)) (hR : ∀ y, Formula.sat A y → (pre = true → Formula.sat gL y) →
    Formula.sat R y)

include hfR hdomL hdomR hgL hAdom hboxB hR in
/-- The merged run of a right-only run, to every time before which the run stayed in `Bf`:
the frozen-left program run there, with the anchor and the region. -/
theorem merged_runB {y ρ : State (Var n)} (hyρ : ∀ i, y (Rv i) = ρ (Rv i))
    (hA : Formula.sat A y) (hgLy : pre = true → Formula.sat gL y)
    {T : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ) :
    ∀ t ∈ Icc (0 : ℝ) T, (∀ s ∈ Ico (0 : ℝ) t, Bf (Φ s)) →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
        (Formula.and domL domR)) (mergeLR y y ρ) (mergeLR y y (Φ t)) ∧
      Formula.sat A (mergeLR y y (Φ t)) ∧ Formula.sat R (mergeLR y y (Φ t)) := by
  intro t ht hB
  have hrun := right_sol_merge_joint hfR hdomL hdomR (ODESol_restrict H ht.1 ht.2) y y
    (hAdom y hA).1
  have hAt := hboxB y ρ hyρ hA hgLy t Φ (ODESol_restrict H ht.1 ht.2) hB
  exact ⟨hrun, hAt, hR _ hAt (fun hp => (sat_merge_L hgL y y _).mpr (hgLy hp))⟩

include hfR hdomL hdomR hgL hAdom hboxB hR in
/-- **A crossed threshold is kept** along a run that stays in `Bf` before its end, when the
coordinate's field is nonnegative at or below it on the region. -/
theorem keep_preservedB (z : Fin n) (z₀ : ℝ)
    (hkeep : ∀ y, Formula.sat R y → y (Rv z) ≤ z₀ → 0 ≤ Term.eval (fR z) y)
    {y ρ : State (Var n)} (hyρ : ∀ i, y (Rv i) = ρ (Rv i))
    (hA : Formula.sat A y) (hgLy : pre = true → Formula.sat gL y)
    {T : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ)
    (hB : ∀ t ∈ Ico (0 : ℝ) T, Bf (Φ t))
    (h0 : z₀ ≤ ρ (Rv z)) : z₀ ≤ Φ T (Rv z) := by
  have hmr := merged_runB fR domL domR gL hfR hdomL hdomR hgL A hAdom pre Bf hboxB R hR hyρ
    hA hgLy H
  set D := Formula.and domL (Formula.and domR R) with hD
  obtain ⟨hr, h0', hder, hmask, -⟩ := right_sol_merge hfR hdomR H y y
  have HD : ODESol (rightBlock fR (Term.const 1)) D (mergeLR y y ρ) T
      (fun t => mergeLR y y (Φ t)) := by
    refine ⟨hr, h0', hder, hmask, fun t ht => ?_⟩
    obtain ⟨-, hAt, hRt⟩ := hmr t ht (fun s hs => hB s ⟨hs.1, hs.2.trans_le ht.2⟩)
    exact ⟨(hAdom _ hAt).1, (hAdom _ hAt).2, hRt⟩
  have hrunD : Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1)) D)
      (mergeLR y y ρ) (mergeLR y y (Φ T)) := by
    rw [hD]
    exact (sem_rightBlock_frozen_iff hfR (by simp [Term.fv])).mpr
      (DLCalTiming.sem_ode_restrict HD H.hr le_rfl)
  have hinit : Term.eval (thrGe (Rv z) z₀) (mergeLR y y ρ) ≤ 0 := by
    simp [thrGe, Term.eval, AOp.interp, mergeLR_R]; linarith
  have hb := boxle_thrGe_R z z₀ (fun _ => Term.const 0) fR 1 zero_le_one D D (fun x h => h)
    (fun w hw hle => hkeep w hw.2.2 hle) hinit _ hrunD
  simp [thrGe, Term.eval, AOp.interp, mergeLR_R] at hb
  linarith

include hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR hguards hAfv hAdom hε htrL htrR hregR hAreg hex
  hcomp hboxB hpruneD hR in
/-- **The cycles of one stage, pre-landing** (`phase` with `hboxB`). The landing coordinate `j`
and its threshold `θ` bound the region `Bf` from inside (`hBf`: below `θ` is in `Bf`); the
landing on the line is at the FIRST entry into `x ≥ θ`. The stage invariant `Kf` is kept along
runs that stay in `Bf`. -/
theorem phaseB (j : Fin n) (θ : ℝ) (hBf : ∀ x : State (Var n), x (Rv j) < θ → Bf x)
    (hline : ∀ y, Formula.sat R y → y (Rv j) = θ →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (hstart : ∀ y, Formula.sat R y → Formula.sat (guard q) y → θ ≤ y (Rv j) →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (z : Fin n) (z₀ rz : ℝ) (hrz : 0 < rz) (Kf : Formula (Var n)) (hKfv : Kf.fv ⊆ range Rv)
    (hKkeep : ∀ y ρ, (∀ i, y (Rv i) = ρ (Rv i)) → Formula.sat A y →
      (pre = true → Formula.sat gL y) → Formula.sat Kf y →
      ∀ T Φ, ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ →
        (∀ t ∈ Ico (0 : ℝ) T, Bf (Φ t)) → Formula.sat Kf (mergeLR y y (Φ T)))
    (hrate : ∀ y, Formula.sat R y → Formula.sat Kf y → y (Rv z) < z₀ → rz ≤ Term.eval (fR z) y)
    (hkeep : (∀ y, Formula.sat R y → y (Rv z) ≤ z₀ → 0 ≤ Term.eval (fR z) y) ∨ (z = j ∧ z₀ = θ)) :
    ∀ (N : ℕ) (y ρ : State (Var n)), (∀ i, y (Rv i) = ρ (Rv i)) →
      (pre = true → Formula.sat gL y) → CycleStart guard q A Kf y ρ ρ →
      z₀ - ρ (Rv z) ≤ N * (rz * epsR) →
      RRespPC G tr epsR q (fun q' μ => Landed G q A y ρ q' μ ∨
        (q' = q ∧ CycleStart guard q A Kf y ρ μ ∧ z₀ ≤ μ (Rv z))) ρ := by
  have htrode := tr_notMem_ode_node fR domR m hsys hdomM hfR hdomR tr htrR
  have htrdom : tr ∉ m.dom.fv := ((notMem_ode_fv_iff _ _ _).mp htrode).2.2
  intro N
  induction N with
  | zero =>
      intro y ρ _ _ hcs hN
      simp only [CharP.cast_eq_zero, zero_mul] at hN
      exact rrespPC_stop (Or.inr ⟨rfl, hcs, by linarith⟩)
  | succ N ih =>
      intro y ρ hyρ hgLy hcs hN
      obtain ⟨hg, hA, hK, hL⟩ := hcs
      have hAy : Formula.sat A y :=
        (sat_of_agree hAfv (x := mergeLR y y ρ) (y := y) (fun i => mergeLR_L y y ρ i)
          (fun i => by rw [mergeLR_R, hyρ i])).mp hA
      have hKρ : Formula.sat Kf ρ := (sat_merge_R hKfv y y ρ).mp hK
      have hKy : Formula.sat Kf y :=
        (Formula.coincidence Kf (fun v hv => by
          obtain ⟨i, rfl⟩ := hKfv hv; exact hyρ i)).mpr hKρ
      have hρdom : Formula.sat domR ρ := (sat_merge_R hdomR y y ρ).mp (hAdom _ hA).2
      -- the landing at the start, already crossed
      by_cases hx0 : θ ≤ ρ (Rv j)
      · have hRρ : Formula.sat R (mergeLR y y ρ) := hR _ hA (fun hp =>
          (sat_merge_L hgL y y ρ).mpr (hgLy hp))
        have hgρ : Formula.sat (guard q) (mergeLR y y ρ) :=
          (sat_merge_R (hguardR q) y y ρ).mpr hg
        obtain ⟨e, he, hneq, hnp, hge⟩ := hstart _ hRρ hgρ (by rw [mergeLR_R]; exact hx0)
        have hleg : SwitchLegal e ρ := by
          unfold SwitchLegal; rw [hguards e he]
          exact (sat_merge_R (hguardR e.tgt) y y ρ).mp hge
        have hdom : Formula.sat m.dom ρ := by rw [hdomM]; exact hρdom
        exact rrespPC_step hm he (sem_clockedSeg_zero m.sys m.dom tr epsR hε.le htrdom hdom)
          ((switchLegal_update hgR he htrR _ _).mpr hleg)
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR 0
            ⟨e, he, hneq, hnp, rfl, hleg, hA, hL⟩)))
      push Not at hx0
      -- one cycle
      obtain ⟨Φ, H⟩ := hex ρ hg hρdom ((sat_merge_R hregR y y ρ).mp (hAreg _ hA))
      have hmr := merged_runB fR domL domR gL hfR hdomL hdomR hgL A hAdom pre Bf hboxB R hR
        hyρ hAy hgLy H
      have hHm : ODESol m.sys m.dom ρ epsR Φ := by rw [hsys, hdomM]; exact H
      -- the landing on the line within the cycle, at the FIRST entry into `x ≥ θ`
      by_cases hcross : ∃ t ∈ Icc (0 : ℝ) epsR, θ ≤ Φ t (Rv j)
      · obtain ⟨t, ht, hθt⟩ := hcross
        obtain ⟨t', ht', hline', hbef⟩ := first_hit H j θ hx0 ht hθt
        obtain ⟨-, hAt, hRt⟩ := hmr t' ht' (fun s hs => hBf _ (hbef s hs))
        obtain ⟨e, he, hneq, hnp, hge⟩ := hline _ hRt (by rw [mergeLR_R]; exact hline')
        have hleg : SwitchLegal e (Φ t') := by
          unfold SwitchLegal; rw [hguards e he]
          exact (sat_merge_R (hguardR e.tgt) y y _).mp hge
        exact rrespPC_step hm he
          (sem_clockedSeg_of_odeSol_fv m.sys m.dom tr epsR hHm ht'.1 ht'.2 ht'.2 htrode)
          ((switchLegal_update hgR he htrR _ _).mpr hleg)
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR t'
            ⟨e, he, hneq, hnp, rfl, hleg, hAt,
              fun i => (right_sol_left (ODESol_restrict H ht'.1 ht'.2) i).trans (hL i)⟩)))
      push Not at hcross
      -- no crossing: the whole cycle is in `Bf`
      have hBall : ∀ t ∈ Icc (0 : ℝ) epsR, ∀ s ∈ Ico (0 : ℝ) t, Bf (Φ s) :=
        fun t ht s hs => hBf _ (hcross s ⟨hs.1, hs.2.le.trans ht.2⟩)
      -- the invariant along the cycle
      have hKt : ∀ t ∈ Icc (0 : ℝ) epsR, Formula.sat Kf (mergeLR y y (Φ t)) := fun t ht =>
        hKkeep y ρ hyρ hAy hgLy hKy t Φ (ODESol_restrict H ht.1 ht.2) (hBall t ht)
      -- the end of the cycle: a declared successor is enabled
      obtain ⟨-, hAe, hRe⟩ := hmr epsR ⟨hε.le, le_rfl⟩ (hBall epsR ⟨hε.le, le_rfl⟩)
      obtain ⟨e, he, hge⟩ := hcomp ρ hg hρdom ((sat_merge_R hregR y y ρ).mp (hAreg _ hA)) epsR Φ le_rfl H
      have hleg : SwitchLegal e (Φ epsR) := by unfold SwitchLegal; rwa [hguards e he]
      have hflow := sem_clockedSeg_of_odeSol_fv m.sys m.dom tr epsR hHm H.hr le_rfl le_rfl htrode
      have hlegκ : SwitchLegal e (Function.update (Φ epsR) tr epsR) :=
        (switchLegal_update hgR he htrR _ _).mpr hleg
      have hLe : ∀ i, Φ epsR (Lv i) = ρ (Lv i) := fun i => (right_sol_left H i).trans (hL i)
      have hLeκ : ∀ i, Function.update (Φ epsR) tr epsR (Lv i) = ρ (Lv i) :=
        fun i => (update_Lv_of_notMem htrL _ _ i).trans (hLe i)
      by_cases hself : e.tgt = q
      · -- the self-loop: the next cycle start, with the measure decreased
        have hgnext : Formula.sat (guard q) (Φ epsR) := by rw [← hself]; exact hge
        have hKLR : Kf.fv ⊆ range Lv ∪ range Rv := fun v hv => Or.inr (hKfv hv)
        set y' := mergeLR y y (Φ epsR) with hy'
        have hgLy' : pre = true → Formula.sat gL y' := fun hp =>
          (sat_merge_L hgL y y _).mpr (hgLy hp)
        have hnext : CycleStart guard q A Kf y' (Φ epsR) (Φ epsR) :=
          ⟨hgnext, (sat_merge_merge hAfv y _ _).mpr hAe,
            (sat_merge_merge hKLR y _ _).mpr (hKt epsR ⟨hε.le, le_rfl⟩), fun _ => rfl⟩
        have hnextκ : CycleStart guard q A Kf y' (Function.update (Φ epsR) tr epsR)
            (Function.update (Φ epsR) tr epsR) := by
          obtain ⟨h1, h2, h3, -⟩ := cycleStart_update_tr guard q hguardR A tr htrL htrR epsR hnext
          exact ⟨h1, h2, h3, fun _ => rfl⟩
        have hgrow : z₀ - Φ epsR (Rv z) ≤ N * (rz * epsR) := by
          have hpos : (0 : ℝ) ≤ N * (rz * epsR) := by positivity
          by_cases hzend : z₀ ≤ Φ epsR (Rv z)
          · linarith
          push Not at hzend
          by_cases hz : ∃ t ∈ Icc (0 : ℝ) epsR, z₀ ≤ Φ t (Rv z)
          · -- crossed within the cycle: kept to its end (or it is the landing coordinate)
            exfalso
            obtain ⟨t, ht, hzt⟩ := hz
            rcases hkeep with hkeep | ⟨rfl, rfl⟩
            · have hsh := odeSol_shift H ht.1 ht.2 le_rfl
              have hmr' := hmr t ht (hBall t ht)
              have hAt' : Formula.sat A (mergeLR y y (Φ t)) := hmr'.2.1
              have hkept := keep_preservedB fR domL domR gL hfR hdomL hdomR hgL A hAdom pre Bf
                hboxB R hR z z₀ hkeep (y := mergeLR y y (Φ t)) (ρ := Φ t)
                (fun i => mergeLR_R y y _ i)
                ((sat_of_agree hAfv (y := mergeLR y y (Φ t)) (fun _ => rfl) (fun _ => rfl)).mp hAt')
                (fun hp => (sat_merge_L hgL y y _).mpr (hgLy hp)) hsh
                (fun s hs => hBf _ (hcross (t + s) ⟨by linarith [hs.1, ht.1],
                  by linarith [hs.2]⟩)) hzt
              simp only [add_sub_cancel] at hkept
              exact absurd hkept (not_le.mpr hzend)
            · exact absurd hzt (not_le.mpr (hcross t ht))
          · push Not at hz
            have hgr := cycle_growth H z rz (fun t ht => by
              obtain ⟨-, -, hRt⟩ := hmr t ht (hBall t ht)
              have := hrate _ hRt (hKt t ht) (by rw [mergeLR_R]; exact hz t ht)
              rwa [eval_fR_merge hfR] at this)
            have : (N.succ : ℝ) * (rz * epsR) = N * (rz * epsR) + rz * epsR := by
              push_cast; ring
            linarith
        have hgrowκ : z₀ - Function.update (Φ epsR) tr epsR (Rv z) ≤ N * (rz * epsR) := by
          rw [update_Rv_of_notMem htrR]; exact hgrow
        have hrest := ih y' (Function.update (Φ epsR) tr epsR)
          (fun i => by rw [hy', mergeLR_R, update_Rv_of_notMem htrR]) hgLy' hnextκ hgrowκ
        refine rrespPC_step hm he hflow hlegκ ?_
        rw [hself]
        refine rrespPC_mono ?_ hrest
        rintro q' μ (⟨e', he', hneq', hnp', rfl, hleg', hAμ, hμL⟩ | ⟨rfl, ⟨hg', hA', hK', hμL⟩, hz'⟩)
        · exact Or.inl ⟨e', he', hneq', hnp', rfl, hleg', (sat_merge_merge hAfv y _ _).mp hAμ,
            fun i => (hμL i).trans (hLeκ i)⟩
        · exact Or.inr ⟨rfl, ⟨hg', (sat_merge_merge hAfv y _ _).mp hA',
            (sat_merge_merge hKLR y _ _).mp hK', fun i => (hμL i).trans (hLeκ i)⟩, hz'⟩
      · -- a non-self successor: an exit (not pruned, by the non-connection certificate)
        have hnp : e.pruned = false := by
          by_contra hc
          have hp : e.pruned = true := by simpa using hc
          exact hpruneD e he hp _ _ hA
            (hmr epsR ⟨hε.le, le_rfl⟩ (hBall epsR ⟨hε.le, le_rfl⟩)).1
            ((switchLegal_merge hgR he y y).mpr hleg)
        exact rrespPC_step hm he hflow hlegκ
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR epsR
            ⟨e, he, hself, hnp, rfl, hleg, hAe, hLe⟩)))

include hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR hguards hAfv hAdom hε htrL htrR hregR hAreg hex
  hcomp hboxB hpruneD hR in
/-- **The cycles of one downward stage, pre-landing** (`phase_down` with `hboxB`; above `θ` is
in `Bf`; the landing is at the first entry into `x ≤ θ`). -/
theorem phase_downB (j : Fin n) (θ : ℝ) (hBf : ∀ x : State (Var n), θ < x (Rv j) → Bf x)
    (hline : ∀ y, Formula.sat R y → y (Rv j) = θ →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (hstart : ∀ y, Formula.sat R y → Formula.sat (guard q) y → y (Rv j) ≤ θ →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (r : ℝ) (hr : 0 < r)
    (hrate : ∀ y, Formula.sat R y → θ < y (Rv j) → Term.eval (fR j) y ≤ -r) :
    ∀ (N : ℕ) (y ρ : State (Var n)), (∀ i, y (Rv i) = ρ (Rv i)) →
      (pre = true → Formula.sat gL y) → CycleStart guard q A Formula.tt y ρ ρ →
      ρ (Rv j) - θ ≤ N * (r * epsR) →
      RRespPC G tr epsR q (fun q' μ => Landed G q A y ρ q' μ ∨
        (q' = q ∧ CycleStart guard q A Formula.tt y ρ μ ∧ μ (Rv j) ≤ θ)) ρ := by
  have htrode := tr_notMem_ode_node fR domR m hsys hdomM hfR hdomR tr htrR
  have htrdom : tr ∉ m.dom.fv := ((notMem_ode_fv_iff _ _ _).mp htrode).2.2
  intro N
  induction N with
  | zero =>
      intro y ρ _ _ hcs hN
      simp only [CharP.cast_eq_zero, zero_mul] at hN
      exact rrespPC_stop (Or.inr ⟨rfl, hcs, by linarith⟩)
  | succ N ih =>
      intro y ρ hyρ hgLy hcs hN
      obtain ⟨hg, hA, -, hL⟩ := hcs
      have hAy : Formula.sat A y :=
        (sat_of_agree hAfv (x := mergeLR y y ρ) (y := y) (fun i => mergeLR_L y y ρ i)
          (fun i => by rw [mergeLR_R, hyρ i])).mp hA
      have hρdom : Formula.sat domR ρ := (sat_merge_R hdomR y y ρ).mp (hAdom _ hA).2
      -- the landing at the start, already crossed
      by_cases hx0 : ρ (Rv j) ≤ θ
      · have hRρ : Formula.sat R (mergeLR y y ρ) := hR _ hA (fun hp =>
          (sat_merge_L hgL y y ρ).mpr (hgLy hp))
        have hgρ : Formula.sat (guard q) (mergeLR y y ρ) :=
          (sat_merge_R (hguardR q) y y ρ).mpr hg
        obtain ⟨e, he, hneq, hnp, hge⟩ := hstart _ hRρ hgρ (by rw [mergeLR_R]; exact hx0)
        have hleg : SwitchLegal e ρ := by
          unfold SwitchLegal; rw [hguards e he]
          exact (sat_merge_R (hguardR e.tgt) y y ρ).mp hge
        have hdom : Formula.sat m.dom ρ := by rw [hdomM]; exact hρdom
        exact rrespPC_step hm he (sem_clockedSeg_zero m.sys m.dom tr epsR hε.le htrdom hdom)
          ((switchLegal_update hgR he htrR _ _).mpr hleg)
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR 0
            ⟨e, he, hneq, hnp, rfl, hleg, hA, hL⟩)))
      push Not at hx0
      -- one cycle
      obtain ⟨Φ, H⟩ := hex ρ hg hρdom ((sat_merge_R hregR y y ρ).mp (hAreg _ hA))
      have hmr := merged_runB fR domL domR gL hfR hdomL hdomR hgL A hAdom pre Bf hboxB R hR
        hyρ hAy hgLy H
      have hHm : ODESol m.sys m.dom ρ epsR Φ := by rw [hsys, hdomM]; exact H
      -- the landing on the line within the cycle, at the FIRST entry into `x ≤ θ`
      by_cases hcross : ∃ t ∈ Icc (0 : ℝ) epsR, Φ t (Rv j) ≤ θ
      · obtain ⟨t, ht, hθt⟩ := hcross
        obtain ⟨t', ht', hline', hbef⟩ := first_hit_down H j θ hx0 ht hθt
        obtain ⟨-, hAt, hRt⟩ := hmr t' ht' (fun s hs => hBf _ (hbef s hs))
        obtain ⟨e, he, hneq, hnp, hge⟩ := hline _ hRt (by rw [mergeLR_R]; exact hline')
        have hleg : SwitchLegal e (Φ t') := by
          unfold SwitchLegal; rw [hguards e he]
          exact (sat_merge_R (hguardR e.tgt) y y _).mp hge
        exact rrespPC_step hm he
          (sem_clockedSeg_of_odeSol_fv m.sys m.dom tr epsR hHm ht'.1 ht'.2 ht'.2 htrode)
          ((switchLegal_update hgR he htrR _ _).mpr hleg)
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR t'
            ⟨e, he, hneq, hnp, rfl, hleg, hAt,
              fun i => (right_sol_left (ODESol_restrict H ht'.1 ht'.2) i).trans (hL i)⟩)))
      push Not at hcross
      have hBall : ∀ t ∈ Icc (0 : ℝ) epsR, ∀ s ∈ Ico (0 : ℝ) t, Bf (Φ s) :=
        fun t ht s hs => hBf _ (hcross s ⟨hs.1, hs.2.le.trans ht.2⟩)
      -- the end of the cycle: a declared successor is enabled
      obtain ⟨-, hAe, -⟩ := hmr epsR ⟨hε.le, le_rfl⟩ (hBall epsR ⟨hε.le, le_rfl⟩)
      obtain ⟨e, he, hge⟩ := hcomp ρ hg hρdom ((sat_merge_R hregR y y ρ).mp (hAreg _ hA)) epsR Φ le_rfl H
      have hleg : SwitchLegal e (Φ epsR) := by unfold SwitchLegal; rwa [hguards e he]
      have hflow := sem_clockedSeg_of_odeSol_fv m.sys m.dom tr epsR hHm H.hr le_rfl le_rfl htrode
      have hlegκ : SwitchLegal e (Function.update (Φ epsR) tr epsR) :=
        (switchLegal_update hgR he htrR _ _).mpr hleg
      have hLe : ∀ i, Φ epsR (Lv i) = ρ (Lv i) := fun i => (right_sol_left H i).trans (hL i)
      have hLeκ : ∀ i, Function.update (Φ epsR) tr epsR (Lv i) = ρ (Lv i) :=
        fun i => (update_Lv_of_notMem htrL _ _ i).trans (hLe i)
      by_cases hself : e.tgt = q
      · -- the self-loop: the next cycle start, with the measure decreased
        have hgnext : Formula.sat (guard q) (Φ epsR) := by rw [← hself]; exact hge
        set y' := mergeLR y y (Φ epsR) with hy'
        have hgLy' : pre = true → Formula.sat gL y' := fun hp =>
          (sat_merge_L hgL y y _).mpr (hgLy hp)
        have hnext : CycleStart guard q A Formula.tt y' (Φ epsR) (Φ epsR) :=
          ⟨hgnext, (sat_merge_merge hAfv y _ _).mpr hAe, trivial, fun _ => rfl⟩
        have hnextκ : CycleStart guard q A Formula.tt y' (Function.update (Φ epsR) tr epsR)
            (Function.update (Φ epsR) tr epsR) := by
          obtain ⟨h1, h2, h3, -⟩ := cycleStart_update_tr guard q hguardR A tr htrL htrR epsR hnext
          exact ⟨h1, h2, h3, fun _ => rfl⟩
        have hdecay : Φ epsR (Rv j) - θ ≤ N * (r * epsR) := by
          have hgr := cycle_decay H j r (fun t ht => by
            obtain ⟨-, -, hRt⟩ := hmr t ht (hBall t ht)
            have := hrate _ hRt (by rw [mergeLR_R]; exact hcross t ht)
            rwa [eval_fR_merge hfR] at this)
          have : (N.succ : ℝ) * (r * epsR) = N * (r * epsR) + r * epsR := by
            push_cast; ring
          linarith
        have hdecayκ : Function.update (Φ epsR) tr epsR (Rv j) - θ ≤ N * (r * epsR) := by
          rw [update_Rv_of_notMem htrR]; exact hdecay
        have hrest := ih y' (Function.update (Φ epsR) tr epsR)
          (fun i => by rw [hy', mergeLR_R, update_Rv_of_notMem htrR]) hgLy' hnextκ hdecayκ
        refine rrespPC_step hm he hflow hlegκ ?_
        rw [hself]
        refine rrespPC_mono ?_ hrest
        rintro q' μ (⟨e', he', hneq', hnp', rfl, hleg', hAμ, hμL⟩ | ⟨rfl, ⟨hg', hA', -, hμL⟩, hz'⟩)
        · exact Or.inl ⟨e', he', hneq', hnp', rfl, hleg', (sat_merge_merge hAfv y _ _).mp hAμ,
            fun i => (hμL i).trans (hLeκ i)⟩
        · exact Or.inr ⟨rfl, ⟨hg', (sat_merge_merge hAfv y _ _).mp hA', trivial,
            fun i => (hμL i).trans (hLeκ i)⟩, hz'⟩
      · -- a non-self successor: an exit (not pruned, by the non-connection certificate)
        have hnp : e.pruned = false := by
          by_contra hc
          have hp : e.pruned = true := by simpa using hc
          exact hpruneD e he hp _ _ hA
            (hmr epsR ⟨hε.le, le_rfl⟩ (hBall epsR ⟨hε.le, le_rfl⟩)).1
            ((switchLegal_merge hgR he y y).mpr hleg)
        exact rrespPC_step hm he hflow hlegκ
          (rrespPC_stop (Or.inl (landed_update_tr G q hgR A tr htrL htrR epsR
            ⟨e, he, hself, hnp, rfl, hleg, hAe, hLe⟩)))

end NodeB

/-! ## The certificate with one or two stages gives `RepoProgress`, pre-landing -/

section CloseB

variable (G : SearchGraph (Var n)) (fR : Fin n → Term (Var n)) (domL domR gL : Formula (Var n))
  (guard : ℕ → Formula (Var n)) (q : ℕ) (m : RMode (Var n)) (hm : G.modeAt q = some m)
  (hsys : m.sys = rightBlock fR (Term.const 1)) (hdomM : m.dom = domR)
  (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
  (hgL : gL.fv ⊆ range Lv) (hguardR : ∀ q', (guard q').fv ⊆ range Rv)
  (hgR : GuardsRight G) (hguards : ∀ e ∈ G.edgesFrom q, e.guard = guard e.tgt)
  (A : ℕ → Formula (Var n)) (hAfv : (A q).fv ⊆ range Lv ∪ range Rv)
  (hAdom : ∀ y, Formula.sat (A q) y → Formula.sat domL y ∧ Formula.sat domR y)
  (pre : Bool) (epsR : ℝ) (hε : 0 < epsR)
  (tr : Var n) (htrL : tr ∉ range Lv) (htrR : tr ∉ range Rv)
  (reg : Formula (Var n)) (hregR : reg.fv ⊆ range Rv)
  (hAreg : ∀ y, Formula.sat (A q) y → Formula.sat reg y)
  (hex : ∀ x, Formula.sat (guard q) x → Formula.sat domR x → Formula.sat reg x →
    ∃ Φ, ODESol (rightBlock fR (Term.const 1)) domR x epsR Φ)
  (hcomp : ∀ x, Formula.sat (guard q) x → Formula.sat domR x → Formula.sat reg x → ∀ t Φ, t ≤ epsR →
    ODESol (rightBlock fR (Term.const 1)) domR x t Φ →
    ∃ e ∈ G.edgesFrom q, Formula.sat (guard e.tgt) (Φ t))
  (Bf : State (Var n) → Prop)
  (hboxB : ∀ y ρ, (∀ i, y (Rv i) = ρ (Rv i)) → Formula.sat (A q) y →
    (pre = true → Formula.sat gL y) →
    ∀ T Φ, ODESol (rightBlock fR (Term.const 1)) domR ρ T Φ →
    (∀ t ∈ Ico (0 : ℝ) T, Bf (Φ t)) → Formula.sat (A q) (mergeLR y y (Φ T)))
  (hpruneD : ∀ e ∈ G.edgesFrom q, e.pruned = true → ∀ σ ω, Formula.sat (A q) σ →
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (Formula.and domL domR)) σ ω → ¬ Formula.sat e.guard ω)
  (R : Formula (Var n)) (hR : ∀ y, Formula.sat (A q) y → (pre = true → Formula.sat gL y) →
    Formula.sat R y)
  (j : Fin n) (θ : ℝ)
  (hline : ∀ y, Formula.sat R y → y (Rv j) = θ →
    ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)

include hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR hguards hAfv hAdom hε htrL htrR hregR hAreg hex
  hcomp hboxB hpruneD hR hline in
/-- **One stage, pre-landing** (`repoProgress_one` with `hboxB`; below `θ` is in `Bf`). -/
theorem repoProgress_oneB (hBf : ∀ x : State (Var n), x (Rv j) < θ → Bf x)
    (hstart : ∀ y, Formula.sat R y → Formula.sat (guard q) y → θ ≤ y (Rv j) →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (r : ℝ) (hr : 0 < r)
    (hrate : ∀ y, Formula.sat R y → y (Rv j) < θ → r ≤ Term.eval (fR j) y) :
    RepoProgress G tr epsR A gL (guard q) q pre := by
  intro ρ y hyρ hA hg hgLy
  have hA' : Formula.sat (A q) (mergeLR y y ρ) :=
    (sat_of_agree hAfv (x := y) (y := mergeLR y y ρ) (fun i => (mergeLR_L y y ρ i).symm)
      (fun i => by rw [mergeLR_R, hyρ i])).mp hA
  set N : ℕ := ⌈(θ - ρ (Rv j)) / (r * epsR)⌉₊ with hN
  have hbound : θ - ρ (Rv j) ≤ N * (r * epsR) := by
    have hpos : 0 < r * epsR := mul_pos hr hε
    have := Nat.le_ceil ((θ - ρ (Rv j)) / (r * epsR))
    rw [div_le_iff₀ hpos] at this
    exact this
  have hph := phaseB G fR domL domR gL guard q m hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR
    hguards (A q) hAfv hAdom pre epsR hε tr htrL htrR reg hregR hAreg hex hcomp Bf hboxB hpruneD R
    hR j θ hBf hline hstart j θ r hr
    Formula.tt (by simp [Formula.fv]) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun y hR' _ hlt => hrate y hR' hlt) (Or.inr ⟨rfl, rfl⟩) N y ρ hyρ hgLy
    ⟨hg, hA', trivial, fun _ => rfl⟩ hbound
  refine rrespPC_bind' hph ?_
  rintro q' μ (hland | ⟨hq', hcs, hθ⟩)
  · exact rrespPC_stop hland
  · subst q'
    exact land_at_start (G := G) (domL := domL) (domR := domR) (gL := gL) (guard := guard) (q := q)
      (m := m) (hm := hm)
      (hdomM := hdomM) (hdomR := hdomR) (hgL := hgL) (hguardR := hguardR) (hguards := hguards)
      (A := A) (hAdom := hAdom) (pre := pre) (epsR := epsR) (hε := hε) (hgR := hgR) (tr := tr)
      (htrL := htrL) (htrR := htrR) (R := R) (hR := hR) (j := j) (θ := θ)
      (hstart := hstart) hgLy hcs hθ

include hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR hguards hAfv hAdom hε htrL htrR hregR hAreg hex
  hcomp hboxB hpruneD hR hline in
/-- **Two stages, pre-landing** (`repoProgress_two` with `hboxB`; below the landing threshold
is in `Bf`). The helper's crossed fact is kept along runs that stay in `Bf`. -/
theorem repoProgress_twoB (hBf : ∀ x : State (Var n), x (Rv j) < θ → Bf x)
    (hstart : ∀ y, Formula.sat R y → Formula.sat (guard q) y → θ ≤ y (Rv j) →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (r : ℝ) (hr : 0 < r) (jh : Fin n) (θh rh : ℝ) (hrh : 0 < rh)
    (hrate_h : ∀ y, Formula.sat R y → y (Rv jh) < θh → rh ≤ Term.eval (fR jh) y)
    (hkeep_h : ∀ y, Formula.sat R y → y (Rv jh) ≤ θh → 0 ≤ Term.eval (fR jh) y)
    (hrate : ∀ y, Formula.sat R y → θh ≤ y (Rv jh) → y (Rv j) < θ → r ≤ Term.eval (fR j) y) :
    RepoProgress G tr epsR A gL (guard q) q pre := by
  intro ρ y hyρ hA hg hgLy
  have hA' : Formula.sat (A q) (mergeLR y y ρ) :=
    (sat_of_agree hAfv (x := y) (y := mergeLR y y ρ) (fun i => (mergeLR_L y y ρ i).symm)
      (fun i => by rw [mergeLR_R, hyρ i])).mp hA
  -- stage 1: the helper crosses
  set N₁ : ℕ := ⌈(θh - ρ (Rv jh)) / (rh * epsR)⌉₊ with hN₁
  have hbound₁ : θh - ρ (Rv jh) ≤ N₁ * (rh * epsR) := by
    have hpos : 0 < rh * epsR := mul_pos hrh hε
    have := Nat.le_ceil ((θh - ρ (Rv jh)) / (rh * epsR))
    rw [div_le_iff₀ hpos] at this
    exact this
  have hph₁ := phaseB G fR domL domR gL guard q m hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR
    hguards (A q) hAfv hAdom pre epsR hε tr htrL htrR reg hregR hAreg hex hcomp Bf hboxB hpruneD R
    hR j θ hBf hline hstart jh θh rh hrh
    Formula.tt (by simp [Formula.fv]) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun y hR' _ hlt => hrate_h y hR' hlt) (Or.inl hkeep_h) N₁ y ρ hyρ hgLy
    ⟨hg, hA', trivial, fun _ => rfl⟩ hbound₁
  refine rrespPC_bind' hph₁ ?_
  rintro q' μ (hland | ⟨hq', ⟨hg₁, hA₁, -, hL₁⟩, hθh⟩)
  · exact rrespPC_stop hland
  subst q'
  -- stage 2: from the cycle start with the helper crossed
  set Kf : Formula (Var n) := Formula.cmp CompOp.le (Term.const θh) (Term.var (Rv jh)) with hKf
  have hKsat : ∀ w : State (Var n), Formula.sat Kf w ↔ θh ≤ w (Rv jh) := fun w => by
    simp [hKf, Formula.sat, CompOp.interp, Term.eval]
  have hKfv : Kf.fv ⊆ range Rv := by
    intro v hv
    simp only [hKf, Formula.fv, Term.fv, Set.empty_union, Set.mem_singleton_iff] at hv
    exact ⟨jh, hv.symm⟩
  set y' := mergeLR y y μ with hy'
  have hgLy' : pre = true → Formula.sat gL y' := fun hp => (sat_merge_L hgL y y μ).mpr (hgLy hp)
  have hKkeep : ∀ y₁ ρ₁, (∀ i, y₁ (Rv i) = ρ₁ (Rv i)) → Formula.sat (A q) y₁ →
      (pre = true → Formula.sat gL y₁) → Formula.sat Kf y₁ →
      ∀ T Φ, ODESol (rightBlock fR (Term.const 1)) domR ρ₁ T Φ →
        (∀ t ∈ Ico (0 : ℝ) T, Bf (Φ t)) → Formula.sat Kf (mergeLR y₁ y₁ (Φ T)) := by
    intro y₁ ρ₁ hyρ₁ hA₁' hgL₁ hK₁ T Φ H hB
    rw [hKsat, mergeLR_R]
    refine keep_preservedB fR domL domR gL hfR hdomL hdomR hgL (A q) hAdom pre Bf hboxB R hR jh
      θh hkeep_h hyρ₁ hA₁' hgL₁ H hB ?_
    rw [← hyρ₁ jh]
    exact (hKsat y₁).mp hK₁
  set N₂ : ℕ := ⌈(θ - μ (Rv j)) / (r * epsR)⌉₊ with hN₂
  have hbound₂ : θ - μ (Rv j) ≤ N₂ * (r * epsR) := by
    have hpos : 0 < r * epsR := mul_pos hr hε
    have := Nat.le_ceil ((θ - μ (Rv j)) / (r * epsR))
    rw [div_le_iff₀ hpos] at this
    exact this
  have hcs₂ : CycleStart guard q (A q) Kf y' μ μ :=
    ⟨hg₁, (sat_merge_merge hAfv y μ μ).mpr hA₁,
      by rw [hKsat, mergeLR_R]; exact hθh, fun _ => rfl⟩
  have hph₂ := phaseB G fR domL domR gL guard q m hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR
    hguards (A q) hAfv hAdom pre epsR hε tr htrL htrR reg hregR hAreg hex hcomp Bf hboxB hpruneD R
    hR j θ hBf hline hstart j θ r hr
    Kf hKfv hKkeep (fun y₂ hR' hK' hlt => hrate y₂ hR' ((hKsat y₂).mp hK') hlt)
    (Or.inr ⟨rfl, rfl⟩) N₂ y' μ (fun i => by rw [hy', mergeLR_R]) hgLy' hcs₂ hbound₂
  refine rrespPC_bind' hph₂ ?_
  rintro q'' μ' (⟨e, he, hneq, hnp, hq'', hleg, hAμ, hμL⟩ | ⟨hq'', ⟨hg₂, hA₂, -, hL₂⟩, hθ⟩)
  · subst q''
    exact rrespPC_stop ⟨e, he, hneq, hnp, rfl, hleg, (sat_merge_merge hAfv y μ μ').mp hAμ,
      fun i => (hμL i).trans (hL₁ i)⟩
  · subst q''
    have hcs' : CycleStart guard q (A q) Formula.tt y ρ μ' :=
      ⟨hg₂, (sat_merge_merge hAfv y μ μ').mp hA₂, trivial, fun i => (hL₂ i).trans (hL₁ i)⟩
    exact land_at_start (G := G) (domL := domL) (domR := domR) (gL := gL) (guard := guard) (q := q)
      (m := m) (hm := hm)
      (hdomM := hdomM) (hdomR := hdomR) (hgL := hgL) (hguardR := hguardR) (hguards := hguards)
      (A := A) (hAdom := hAdom) (pre := pre) (epsR := epsR) (hε := hε) (hgR := hgR) (tr := tr)
      (htrL := htrL) (htrR := htrR) (R := R) (hR := hR) (j := j) (θ := θ)
      (hstart := hstart) hgLy hcs' hθ

include hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR hguards hAfv hAdom hε htrL htrR hregR hAreg hex
  hcomp hboxB hpruneD hR hline in
/-- **One downward stage, pre-landing** (`repoProgress_one_down` with `hboxB`; above `θ` is in
`Bf`). -/
theorem repoProgress_one_downB (hBf : ∀ x : State (Var n), θ < x (Rv j) → Bf x)
    (r : ℝ) (hr : 0 < r)
    (hstart_down : ∀ y, Formula.sat R y → Formula.sat (guard q) y → y (Rv j) ≤ θ →
      ∃ e ∈ G.edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧ Formula.sat (guard e.tgt) y)
    (hrate : ∀ y, Formula.sat R y → θ < y (Rv j) → Term.eval (fR j) y ≤ -r) :
    RepoProgress G tr epsR A gL (guard q) q pre := by
  intro ρ y hyρ hA hg hgLy
  have hA' : Formula.sat (A q) (mergeLR y y ρ) :=
    (sat_of_agree hAfv (x := y) (y := mergeLR y y ρ) (fun i => (mergeLR_L y y ρ i).symm)
      (fun i => by rw [mergeLR_R, hyρ i])).mp hA
  set N : ℕ := ⌈(ρ (Rv j) - θ) / (r * epsR)⌉₊ with hN
  have hbound : ρ (Rv j) - θ ≤ N * (r * epsR) := by
    have hpos : 0 < r * epsR := mul_pos hr hε
    have := Nat.le_ceil ((ρ (Rv j) - θ) / (r * epsR))
    rw [div_le_iff₀ hpos] at this
    exact this
  have hph := phase_downB G fR domL domR gL guard q m hm hsys hdomM hfR hdomL hdomR hgL hguardR hgR
    hguards (A q) hAfv hAdom pre epsR hε tr htrL htrR reg hregR hAreg hex hcomp Bf hboxB hpruneD R
    hR j θ hBf hline hstart_down r hr hrate N y ρ hyρ hgLy ⟨hg, hA', trivial, fun _ => rfl⟩ hbound
  refine rrespPC_bind' hph ?_
  rintro q' μ (hland | ⟨hq', hcs, hθ⟩)
  · exact rrespPC_stop hland
  · subst q'
    exact land_at_start_down (G := G) (domL := domL) (domR := domR) (gL := gL) (guard := guard)
      (q := q) (m := m) (hm := hm)
      (hdomM := hdomM) (hdomR := hdomR) (hgL := hgL) (hguardR := hguardR) (hguards := hguards)
      (A := A) (hAdom := hAdom) (pre := pre) (epsR := epsR) (hε := hε) (hgR := hgR) (tr := tr)
      (htrL := htrL) (htrR := htrR) (R := R) (hR := hR) (j := j) (θ := θ)
      hstart_down hgLy hcs hθ

end CloseB

end RelCertifier
