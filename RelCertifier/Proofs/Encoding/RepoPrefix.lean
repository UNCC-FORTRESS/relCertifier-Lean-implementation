/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S1 — the reposition prefix inside a window (multi-mode responses)

The paper's witness for a mismatched (window, right-start) pair opens with repositions:
the right hops (frozen-left dynamic flows) to a joint-certified mode, THEN tracks the
window's pieces. In the endpoint-based `faModalB` coupling this composes because of
three structural facts:

* the left run MASKS right coordinates — so the right's endpoint coordinates at the
  left's endpoint `ν` equal the anchor's, and the reposition run from the anchor
  REPLAYS verbatim from `ν` (rights identical; lefts constant under the 0-field);
* the replay's domain is the POST-J dyn domain (`evolveL ∧ evolveR`, no `guardL`) —
  correct, because the replay happens at the left's endpoint where the guard may have
  expired; `evolveL` holds there by the left run's own domain;
* left runs are right-frame-invariant (side-splits), so the anchor patches to the
  repositioned state `ρ₁` and the joint piece's cert-sourced coupling fires from `ρ₁`
  (where the invariant holds by the post-j dyn certificate).

`faModalB_repoPrefix` is the composition; iterating it gives multi-hop prefixes.
-/
import RelCertifier.Proofs.Encoding.RepositionDischarge
import RelCertifier.Proofs.Encoding.UniformFvDischarge
import RelCertifier.Proofs.Encoding.CoverMulti

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-- Right-coordinate patch: take rights from `ρ`, everything else from `x`. -/
def rpatch (x ρ : State (Var n)) : State (Var n) :=
  fun v => if v.1 = Side.R then ρ v else x v

@[simp] theorem rpatch_right (x ρ : State (Var n)) (i : Fin n) :
    rpatch x ρ (Rv i) = ρ (Rv i) := rfl

@[simp] theorem rpatch_left (x ρ : State (Var n)) (i : Fin n) :
    rpatch x ρ (Lv i) = x (Lv i) := rfl

@[simp] theorem rpatch_aux (x ρ : State (Var n)) (a : Fin n) :
    rpatch x ρ ((Side.Aux, a) : Var n) = x ((Side.Aux, a) : Var n) := rfl

theorem rpatch_of_ne_right (x ρ : State (Var n)) {v : Var n} (h : v.1 ≠ Side.R) :
    rpatch x ρ v = x v := by simp [rpatch, h]

/-- Coincidence: a formula whose variables split away from `Side.R` reads the same on a
right-patch. -/
theorem sat_rpatch_of_fv_not_right {φ : Formula (Var n)}
    (hfv : ∀ v ∈ φ.fv, v.1 ≠ Side.R) (x ρ : State (Var n)) :
    Formula.sat φ (rpatch x ρ) ↔ Formula.sat φ x :=
  Formula.coincidence φ (fun v hv => rpatch_of_ne_right x ρ (hfv v hv))

/-- Terms with only-right variables read only rights. -/
theorem eval_rpatch_of_fv_right {t : Term (Var n)}
    (hfv : ∀ v ∈ t.fv, v.1 = Side.R) (x ρ : State (Var n)) :
    Term.eval t (rpatch x ρ) = Term.eval t ρ :=
  Term.coincidence t (fun v hv => by simp [rpatch, hfv v hv])

/-- **Zero-field constancy.** Along a run of the frozen-left system, every left
coordinate is constant. -/
theorem frozen_left_constant {fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {dom : Formula (Var n)} {ν μ : State (Var n)}
    (h : Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam) dom) ν μ) :
    ∀ i : Fin n, μ (Lv i) = ν (Lv i) := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  intro i
  have hpair : (Lv i, Term.const 0) ∈ jointSys (fun _ => Term.const 0) fR lam := by
    rw [jointSys_split]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  have hd : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun u => Φ u (Lv i)) 0 (Set.Icc 0 r) t := by
    intro t ht
    have := hder t ht (Lv i, Term.const 0) hpair
    simpa [Term.eval] using this
  have hconst : ∀ t ∈ Set.Icc (0:ℝ) r, Φ t (Lv i) = Φ 0 (Lv i) := by
    intro t ht
    have hmono : ∀ s ∈ Set.Icc (0:ℝ) t, HasDerivWithinAt (fun u => Φ u (Lv i)) 0
        (Set.Icc 0 t) s := fun s hs =>
      (hd s ⟨hs.1, hs.2.trans ht.2⟩).mono (Set.Icc_subset_Icc_right ht.2)
    have h1 : AntitoneOn (fun u => Φ u (Lv i)) (Set.Icc 0 t) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
        (fun s hs => (hmono s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
      · rw [interior_Icc] at hs
        exact ((hmono s (Set.Ioo_subset_Icc_self hs)).hasDerivAt
          (Icc_mem_nhds hs.1 hs.2)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hs
        rw [((hmono s (Set.Ioo_subset_Icc_self hs)).hasDerivAt
          (Icc_mem_nhds hs.1 hs.2)).deriv]
    have h2 : MonotoneOn (fun u => Φ u (Lv i)) (Set.Icc 0 t) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
        (fun s hs => (hmono s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
      · rw [interior_Icc] at hs
        exact ((hmono s (Set.Ioo_subset_Icc_self hs)).hasDerivAt
          (Icc_mem_nhds hs.1 hs.2)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hs
        rw [((hmono s (Set.Ioo_subset_Icc_self hs)).hasDerivAt
          (Icc_mem_nhds hs.1 hs.2)).deriv]
    have ht0 : (0:ℝ) ∈ Set.Icc 0 t := Set.left_mem_Icc.mpr ht.1
    have htt : t ∈ Set.Icc (0:ℝ) t := Set.right_mem_Icc.mpr ht.1
    exact le_antisymm (h1 ht0 htt ht.1) (h2 ht0 htt ht.1)
  rw [← hΦr, hconst r (Set.right_mem_Icc.mpr hr), hΦ0]

/-- Non-bound coordinates are masked along any ode run (projection of `sem`'s (b)). -/
theorem sem_ode_mask {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {ν μ : State (Var n)} (h : Program.sem (Program.ode sys dom) ν μ)
    {x : Var n} (hx : x ∉ sys.bound) : μ x = ν x := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  rw [← hΦr, hmask r (Set.right_mem_Icc.mpr hr) x hx]

/-- Aux coordinates are not bound by any `jointSys`. -/
theorem aux_not_jointSys_bound (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (a : Fin n) : ((Side.Aux, a) : Var n) ∉ (jointSys fL fR lam).bound := by
  rw [jointSys_split]
  intro h
  simp only [ODESystem.bound, List.map_append, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := leftBlock_bound_sub fL _ h
    exact aux_ne_Lv a i hi
  · obtain ⟨i, hi⟩ := rightBlock_bound_sub fR lam _ h
    exact aux_ne_Rv a i hi

/-- **The reposition replay.** A frozen-left run from the anchor replays verbatim from
any state with the same right coordinates whose lefts satisfy `domL` — lefts constant
at the new state's values (0-field), rights identical, post-j domain valid. -/
theorem sem_frozen_replay {fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domL domR : Formula (Var n)} {ω₀ ρ₁ ν : State (Var n)}
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hlam : lam.fv ⊆ range Rv)
    (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
    (hrun : Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam)
      (Formula.and domL domR)) ω₀ ρ₁)
    (hrights : ∀ i : Fin n, ν (Rv i) = ω₀ (Rv i))
    (hνdomL : Formula.sat domL ν) :
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam)
      (Formula.and domL domR)) ν (rpatch ν ρ₁) := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hrun
  refine ⟨r, fun t => rpatch ν (Φ t), hr, ?_, ?_, ?_, ?_, ?_⟩
  · -- Φ' 0 = ν
    funext v
    show rpatch ν (Φ 0) v = ν v
    unfold rpatch
    split
    · next hv =>
        obtain ⟨s, i⟩ := v
        cases s with
        | R =>
            rw [hΦ0]
            exact (hrights i).symm
        | L => exact absurd hv (by simp)
        | Aux => exact absurd hv (by simp)
    · rfl
  · show rpatch ν (Φ r) = rpatch ν ρ₁
    rw [hΦr]
  · intro t ht p hp
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hpL | hpR
    · -- left pair (Lv i, 0): constant at ν
      have hex : ∃ i : Fin n, (Lv i, Term.const 0) = p := by
        simpa [leftBlock] using hpL
      obtain ⟨i, hip⟩ := hex
      cases hip
      have hfun : (fun u => rpatch ν (Φ u) (Lv i)) = fun _ => ν (Lv i) := by
        funext u; rfl
      show HasDerivWithinAt (fun u => rpatch ν (Φ u) (Lv i))
        (Term.eval (Term.const 0) (rpatch ν (Φ t))) (Set.Icc 0 r) t
      rw [hfun, show Term.eval (Term.const 0) (rpatch ν (Φ t)) = 0 from rfl]
      exact hasDerivWithinAt_const t (Set.Icc (0:ℝ) r) (ν (Lv i))
    · -- right pair: same trajectory, same derivative (rights-only reads)
      have hex : ∃ i : Fin n, (Rv i, Term.binop .mul lam (fR i)) = p := by
        simpa [rightBlock] using hpR
      obtain ⟨i, hip⟩ := hex
      cases hip
      have hfun : (fun u => rpatch ν (Φ u) (Rv i)) = fun u => Φ u (Rv i) := by
        funext u; rfl
      have hev : Term.eval (Term.binop .mul lam (fR i)) (rpatch ν (Φ t))
          = Term.eval (Term.binop .mul lam (fR i)) (Φ t) := by
        refine Term.coincidence _ ?_
        intro v hv
        have hvR : v.1 = Side.R := by
          simp only [Term.fv] at hv
          rcases hv with hv | hv
          · obtain ⟨j, rfl⟩ := hlam hv; rfl
          · obtain ⟨j, rfl⟩ := hfR i hv; rfl
        exact (by unfold rpatch; rw [if_pos hvR] : rpatch ν (Φ t) v = Φ t v)
      show HasDerivWithinAt (fun u => rpatch ν (Φ u) (Rv i))
        (Term.eval (Term.binop .mul lam (fR i)) (rpatch ν (Φ t))) (Set.Icc 0 r) t
      rw [hfun, hev]
      exact hder t ht (Rv i, Term.binop .mul lam (fR i)) (by
        rw [jointSys_split]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  · -- mask: non-bound coordinates held at ν
    intro t ht x hx
    show rpatch ν (Φ t) x = ν x
    have hxa : x.1 ≠ Side.R := by
      intro hR
      obtain ⟨s, i⟩ := x
      cases s with
      | R =>
          refine hx ?_
          rw [jointSys_split]
          simp only [ODESystem.bound, List.map_append, List.mem_append]
          right
          simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map,
            List.mem_finRange]
          exact ⟨i, trivial, rfl⟩
      | L => exact absurd hR (by simp)
      | Aux => exact absurd hR (by simp)
    exact rpatch_of_ne_right ν (Φ t) hxa
  · -- domain: domL at ν-lefts, domR along the original rights
    intro t ht
    refine ⟨?_, ?_⟩
    · exact (Formula.coincidence domL (fun v hv => by
        obtain ⟨i, rfl⟩ := hdomL hv
        rfl)).mpr hνdomL
    · exact (Formula.coincidence domR (fun v hv => by
        obtain ⟨i, rfl⟩ := hdomR hv
        exact (by unfold rpatch; rw [if_pos rfl] : rpatch ν (Φ t) (Rv i) = Φ t (Rv i)))).mpr
        ((hdom t ht).2)

/-- **Left runs are right-frame-invariant.** A clocked left run patches to any right
frame: same lefts/clock trajectory, rights held constant at the patch values. -/
theorem plantT_rpatch {fL : Fin n → Term (Var n)} {domL : Formula (Var n)}
    {a : Fin n} {dt : ℝ} {ω ν ρ : State (Var n)}
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (h : plantT (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
      ((Side.Aux, a) : Var n) dt ω ν) :
    plantT (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
      ((Side.Aux, a) : Var n) dt (rpatch ω ρ) (rpatch ν ρ) := by
  obtain ⟨⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩, hclk⟩ := h
  refine ⟨⟨r, fun t => rpatch (Φ t) ρ, hr,
    (by show rpatch (Φ 0) ρ = rpatch ω ρ; rw [hΦ0]),
    (by show rpatch (Φ r) ρ = rpatch ν ρ; rw [hΦr]), ?_, ?_, ?_⟩, ?_⟩
  · intro t ht p hp
    have hp1 : p.1.1 ≠ Side.R := by
      intro hR
      have hb : p.1 ∈ (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)).bound := by
        simp only [ODESystem.bound]
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
      rcases clk_boundSet_sub _ _ (by simpa [ODESystem.boundSet] using hb) with hx | hx
      · obtain ⟨i, hi⟩ := leftBlock_boundSet_sub fL hx
        rw [← hi] at hR
        exact absurd hR (by simp [Lv])
      · rw [Set.mem_singleton_iff] at hx
        rw [hx] at hR
        exact absurd hR (by simp)
    have hfun : (fun u => rpatch (Φ u) ρ p.1) = fun u => Φ u p.1 := by
      funext u
      exact rpatch_of_ne_right (Φ u) ρ hp1
    have hev : Term.eval p.2 (rpatch (Φ t) ρ) = Term.eval p.2 (Φ t) := by
      refine Term.coincidence _ ?_
      intro v hv
      -- reads of the clocked left block: Lv (fields) or none (clock's const 1)
      have hvL : v.1 ≠ Side.R := by
        have hrv : v ∈ (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)).readVars := by
          simp only [ODESystem.readVars, Set.mem_setOf_eq]
          exact ⟨p, hp, hv⟩
        have := clk_readVars_sub ((Side.Aux, a) : Var n) (leftBlock fL) hrv
        obtain ⟨i, hi⟩ := leftBlock_readVars_sub fL hfL this
        rw [← hi]
        simp [Lv]
      exact rpatch_of_ne_right (Φ t) ρ hvL
    show HasDerivWithinAt (fun u => rpatch (Φ u) ρ p.1)
      (Term.eval p.2 (rpatch (Φ t) ρ)) (Set.Icc 0 r) t
    rw [hfun, hev]
    exact hder t ht p hp
  · intro t ht x hx
    show rpatch (Φ t) ρ x = rpatch ω ρ x
    by_cases hxR : x.1 = Side.R
    · unfold rpatch
      rw [if_pos hxR, if_pos hxR]
    · rw [rpatch_of_ne_right _ _ hxR, rpatch_of_ne_right _ _ hxR]
      exact hmask t ht x hx
  · intro t ht
    exact (Formula.coincidence domL (fun v hv => by
      obtain ⟨i, rfl⟩ := hdomL hv
      rfl)).mpr (hdom t ht)
  · show rpatch ν ρ ((Side.Aux, a) : Var n) - rpatch ω ρ ((Side.Aux, a) : Var n) ≤ dt
    simpa using hclk

/-- **The reposition prefix (S1 core).** A window piece's coupling extends to a
reposition-prefixed response: the frozen-left hop runs at the anchor (invariant
preserved by the POST-J dynamic certificate), replays verbatim at the left's endpoint,
and the joint coupling fires from the repositioned anchor by right-frame-invariance. -/
theorem faModalB_repoPrefix {fL fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domL domR : Formula (Var n)} {φ : Formula (Var n)} {Q : Program (Var n)}
    {a : Fin n} {dt : ℝ} {ω₀ : State (Var n)}
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hlam : lam.fv ⊆ range Rv)
    (hdomR : domR.fv ⊆ range Rv)
    (hω₀tg : ω₀ ((Side.Aux, a) : Var n) = 0)
    -- the hop: a frozen-left run from the anchor, endpoint jointly invariant
    (hR : ∃ ρ₁, Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam)
        (Formula.and domL domR)) ω₀ ρ₁ ∧ Formula.sat φ ρ₁)
    -- the piece coupling, cert-sourced, anchored at any invariant state with clock 0
    (hQ : ∀ σ, Formula.sat φ σ → σ ((Side.Aux, a) : Var n) = 0 →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        Q φ ((Side.Aux, a) : Var n) dt σ) :
    faModalB (Equiv.refl (Var n))
      (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
      (Program.seq
        (Program.ode (jointSys (fun _ => Term.const 0) fR lam) (Formula.and domL domR))
        Q)
      φ ((Side.Aux, a) : Var n) dt ω₀ := by
  intro ν hplant
  obtain ⟨ρ₁, hhop, hρ₁sat⟩ := hR
  -- the left run masks rights: ν's rights are the anchor's
  have hrights : ∀ i : Fin n, ν (Rv i) = ω₀ (Rv i) := by
    intro i
    refine sem_ode_mask hplant.1 ?_
    intro hb
    rcases clk_boundSet_sub _ _ (by simpa [ODESystem.boundSet] using hb) with hx | hx
    · obtain ⟨j, hj⟩ := leftBlock_boundSet_sub fL hx
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
    · rw [Set.mem_singleton_iff] at hx
      exact absurd hx (by simp [Rv, Prod.ext_iff])
  -- the left run's endpoint satisfies domL
  have hνdomL : Formula.sat domL ν := by
    obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hplant.1
    rw [← hΦr]
    exact hdom r (Set.right_mem_Icc.mpr hr)
  -- the hop replays at ν
  have hreplay := sem_frozen_replay hfR hlam hdomL hdomR hhop hrights hνdomL
  -- the hop froze lefts and masked aux, so ρ₁ = rpatch ω₀ ρ₁
  have hρ₁eq : rpatch ω₀ ρ₁ = ρ₁ := by
    funext v
    obtain ⟨s, i⟩ := v
    cases s with
    | R => rfl
    | L =>
        show ω₀ (Lv i) = ρ₁ (Lv i)
        exact (frozen_left_constant hhop i).symm
    | Aux =>
        show ω₀ ((Side.Aux, i) : Var n) = ρ₁ ((Side.Aux, i) : Var n)
        exact (sem_ode_mask hhop (aux_not_jointSys_bound _ _ _ i)).symm
  -- the patched left run anchors the piece coupling at ρ₁
  have hplant' := plantT_rpatch hfL hdomL (ρ := ρ₁) hplant
  rw [hρ₁eq] at hplant'
  have hρ₁tg : ρ₁ ((Side.Aux, a) : Var n) = 0 := by
    rw [sem_ode_mask hhop (aux_not_jointSys_bound _ _ _ a)]
    exact hω₀tg
  obtain ⟨μ, hQμSem, hQμφ⟩ := hQ ρ₁ hρ₁sat hρ₁tg (rpatch ν ρ₁) hplant'
  refine ⟨μ, ?_, hQμφ⟩
  rw [Program.rename_refl] at hQμSem ⊢
  exact ⟨rpatch ν ρ₁, hreplay, hQμSem⟩

/-- Per-hop data: the frozen-left field and stretch of the mode being hopped through. -/
structure RepoHop (n : ℕ) where
  fR  : Fin n → Term (Var n)
  lam : Term (Var n)
  domR : Formula (Var n)

/-- The hop's frozen-left program (post-j domain). -/
def RepoHop.prog (h : RepoHop n) (domL : Formula (Var n)) : Program (Var n) :=
  Program.ode (jointSys (fun _ => Term.const 0) h.fR h.lam) (Formula.and domL h.domR)

/-- **Multi-hop reposition prefix.** Iterate `faModalB_repoPrefix` over a hop list:
each hop's existence-with-invariant is supplied as a family (anchored anywhere the
invariant holds with clock 0 — the previous hop's endpoint qualifies), and the final
continuation coupling fires at the last hop's endpoint. -/
theorem faModalB_repoPath {fL : Fin n → Term (Var n)} {domL : Formula (Var n)}
    {φ : Formula (Var n)} {Q : Program (Var n)} {a : Fin n} {dt : ℝ}
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (hops : List (RepoHop n))
    (hhops : ∀ h ∈ hops, (∀ i, (h.fR i).fv ⊆ range Rv) ∧ h.lam.fv ⊆ range Rv
      ∧ h.domR.fv ⊆ range Rv)
    (hR : ∀ h ∈ hops, ∀ σ, Formula.sat φ σ → σ ((Side.Aux, a) : Var n) = 0 →
      ∃ ρ, Program.sem (h.prog domL) σ ρ ∧ Formula.sat φ ρ)
    (hQ : ∀ σ, Formula.sat φ σ → σ ((Side.Aux, a) : Var n) = 0 →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        Q φ ((Side.Aux, a) : Var n) dt σ) :
    ∀ σ, Formula.sat φ σ → σ ((Side.Aux, a) : Var n) = 0 →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        (hops.foldr (fun h q => Program.seq (h.prog domL) q) Q)
        φ ((Side.Aux, a) : Var n) dt σ := by
  induction hops with
  | nil => exact hQ
  | cons h hs ih =>
      intro σ hσ hσtg
      obtain ⟨hhfR, hhlam, hhdomR⟩ := hhops h (List.mem_cons_self)
      have ihs := ih (fun h' hh' => hhops h' (List.mem_cons_of_mem _ hh'))
        (fun h' hh' => hR h' (List.mem_cons_of_mem _ hh'))
      exact faModalB_repoPrefix hfL hdomL hhfR hhlam hhdomR hσtg
        (hR h (List.mem_cons_self) σ hσ hσtg) ihs

/-! ## Automaton-shape bridges -/

/-- `foldr seq` and `bigSeq (· ++ [·])` have the same runs (associativity of `seq`). -/
theorem sem_foldr_seq_bigSeq (hops : List (Program (Var n))) (Q : Program (Var n)) :
    ∀ ν μ, Program.sem (hops.foldr (fun h q => Program.seq h q) Q) ν μ ↔
      Program.sem (bigSeq (hops ++ [Q])) ν μ := by
  induction hops with
  | nil =>
      intro ν μ
      constructor
      · intro h
        exact ⟨μ, h, rfl, by simpa [Formula.sat] using trivial⟩
      · rintro ⟨κ, hκ, rfl, -⟩
        exact hκ
  | cons h hs ih =>
      intro ν μ
      constructor
      · rintro ⟨κ, hκ, hrest⟩
        exact ⟨κ, hκ, (ih κ μ).mp hrest⟩
      · rintro ⟨κ, hκ, hrest⟩
        exact ⟨κ, hκ, (ih κ μ).mpr hrest⟩

/-- **Hop-shape bridge.** A run of the automaton's right-only mode ode (over the mode's
`domL ∧ domR` domain) is a run of the frozen-left joint ode and vice versa — lefts are
masked constants on one side, bound 0-field constants on the other. -/
theorem sem_rightBlock_frozen_iff {fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domL domR : Formula (Var n)} {ν μ : State (Var n)}
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hlam : lam.fv ⊆ range Rv) :
    Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam)
        (Formula.and domL domR)) ν μ ↔
      Program.sem (Program.ode (rightBlock fR lam) (Formula.and domL domR)) ν μ := by
  constructor
  · rintro ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩
    refine ⟨r, Φ, hr, hΦ0, hΦr, ?_, ?_, hdom⟩
    · intro t ht p hp
      refine hder t ht p ?_
      rw [jointSys_split]
      exact List.mem_append_right _ hp
    · intro t ht x hx
      by_cases hxL : ∃ i : Fin n, x = Lv i
      · obtain ⟨i, rfl⟩ := hxL
        -- left coordinate: 0-field-bound in the joint run, hence constant
        have hpair : (Lv i, Term.const 0) ∈ jointSys (fun _ => Term.const 0) fR lam := by
          rw [jointSys_split]
          exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
        have hd : ∀ s ∈ Set.Icc (0:ℝ) t, HasDerivWithinAt (fun u => Φ u (Lv i)) 0
            (Set.Icc 0 t) s := by
          intro s hs
          have := hder s ⟨hs.1, hs.2.trans ht.2⟩ (Lv i, Term.const 0) hpair
          simpa [Term.eval] using this.mono (Set.Icc_subset_Icc_right ht.2)
        -- constant on [0,t] (antitone + monotone at derivative 0)
        have h1 : AntitoneOn (fun u => Φ u (Lv i)) (Set.Icc 0 t) := by
          refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
            (fun s hs => (hd s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
          · rw [interior_Icc] at hs
            exact ((hd s (Set.Ioo_subset_Icc_self hs)).hasDerivAt
              (Icc_mem_nhds hs.1 hs.2)).differentiableAt.differentiableWithinAt
          · rw [interior_Icc] at hs
            rw [((hd s (Set.Ioo_subset_Icc_self hs)).hasDerivAt
              (Icc_mem_nhds hs.1 hs.2)).deriv]
        have h2 : MonotoneOn (fun u => Φ u (Lv i)) (Set.Icc 0 t) := by
          refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
            (fun s hs => (hd s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
          · rw [interior_Icc] at hs
            exact ((hd s (Set.Ioo_subset_Icc_self hs)).hasDerivAt
              (Icc_mem_nhds hs.1 hs.2)).differentiableAt.differentiableWithinAt
          · rw [interior_Icc] at hs
            rw [((hd s (Set.Ioo_subset_Icc_self hs)).hasDerivAt
              (Icc_mem_nhds hs.1 hs.2)).deriv]
        have ht0 : (0:ℝ) ∈ Set.Icc 0 t := Set.left_mem_Icc.mpr ht.1
        have htt : t ∈ Set.Icc (0:ℝ) t := Set.right_mem_Icc.mpr ht.1
        have hconst : Φ t (Lv i) = Φ 0 (Lv i) :=
          le_antisymm (h1 ht0 htt ht.1) (h2 ht0 htt ht.1)
        rw [hconst, hΦ0]
      · -- neither right-bound nor left: aux — masked in the joint run too
        refine hmask t ht x ?_
        rw [jointSys_split]
        intro hb
        simp only [ODESystem.bound, List.map_append, List.mem_append] at hb
        rcases hb with hb | hb
        · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fun _ => Term.const 0) _ hb
          exact hxL ⟨i, hi⟩
        · exact hx (by simpa [ODESystem.bound] using hb)
  · rintro ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩
    refine ⟨r, Φ, hr, hΦ0, hΦr, ?_, ?_, hdom⟩
    · intro t ht p hp
      rw [jointSys_split] at hp
      rcases List.mem_append.mp hp with hpL | hpR
      · -- left pair: the right-only run masks lefts (not bound), so constant, derivative 0
        have hex : ∃ i : Fin n, (Lv i, Term.const 0) = p := by
          simpa [leftBlock] using hpL
        obtain ⟨i, hip⟩ := hex
        cases hip
        have hLnb : Lv i ∉ (rightBlock fR lam).bound := by
          intro hb
          obtain ⟨j, hj⟩ := rightBlock_bound_sub fR lam _ hb
          exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
        show HasDerivWithinAt (fun u => Φ u (Lv i))
          (Term.eval (Term.const 0) (Φ t)) (Set.Icc 0 r) t
        rw [show Term.eval (Term.const 0) (Φ t) = 0 from rfl]
        refine (hasDerivWithinAt_const t (Set.Icc (0:ℝ) r) (ν (Lv i))).congr ?_ ?_
        · intro u hu
          exact hmask u hu (Lv i) hLnb
        · exact hmask t ht (Lv i) hLnb
      · exact hder t ht p hpR
    · intro t ht x hx
      refine hmask t ht x ?_
      intro hb
      refine hx ?_
      rw [jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr hb

/-- `bigSeq` with a folded head has the same runs as the flattened list. -/
theorem sem_bigSeq_fold_head (hops : List (Program (Var n))) (p : Program (Var n))
    (rest : List (Program (Var n))) :
    ∀ ν μ, Program.sem (bigSeq ((hops.foldr (fun h q => Program.seq h q) p) :: rest)) ν μ ↔
      Program.sem (bigSeq (hops ++ p :: rest)) ν μ := by
  induction hops with
  | nil => intro ν μ; exact Iff.rfl
  | cons h hs ih =>
      intro ν μ
      constructor
      · rintro ⟨κ, ⟨κ', hκ', hfold⟩, hrest⟩
        exact ⟨κ', hκ', (ih κ' μ).mp ⟨κ, hfold, hrest⟩⟩
      · rintro ⟨κ', hκ', htail⟩
        obtain ⟨κ, hfold, hrest⟩ := (ih κ' μ).mpr htail
        exact ⟨κ, ⟨κ', hκ', hfold⟩, hrest⟩

/-- `faModal` respects run-equivalent right programs (identity renaming). -/
theorem sat_faModal_congrR {P Q Q' : Program (Var n)} {φ : Formula (Var n)}
    {σ : State (Var n)}
    (h : ∀ ν μ, Program.sem Q ν μ ↔ Program.sem Q' ν μ)
    (hQ : Formula.sat (faModal (Equiv.refl (Var n)) P Q φ) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) P Q' φ) σ := by
  unfold faModal at hQ ⊢
  rw [sat_box] at hQ ⊢
  intro ν hν
  have hdia := hQ ν hν
  rw [sat_diamond] at hdia ⊢
  push_neg at hdia ⊢
  obtain ⟨μ, hsem, hφ⟩ := hdia
  rw [Program.rename_refl] at hsem ⊢
  exact ⟨μ, (h ν μ).mp hsem, hφ⟩

end RelCertifier
