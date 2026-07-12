/-
GAP 1 (A) — the static-reposition step-lemma.

A static-reposition mode carries `m.sys = []` (zero motion): its `modeStep` is
`test(mode=q); ode [] dom; test e.guard; assign mv := e.tgt` — a state-preserving discrete mode
switch along a DECLARED edge. It preserves `invLe g` by two banked/trivial facts: the empty ODE is
the identity on the continuous state, and the `mv`-assign is invisible to `invLe g` (`mv ∉ g.fv`).
No `RegionInvOn`, no analysis (see the C.2 resolution: `region` references the left guard, is not a
right-automaton transition, and drops out post-tightening). ∃-right jump-faithfulness is the same as
the flow case: the target is a declared `G`-edge (`e ∈ edgesFrom q`).
-/
import RelCertifier.JointBridge
import RelCertifier.Reify
import RelCertifier.PicardBridge
import RelCertifier.MultiSeg

namespace RelCertifier
open DL DLCalTiming Function Set

variable {n : ℕ}

/-- Forward direction: a `bigChoiceP` run is a run of one of its branches (the dispatch used to
case a `rightAutomatonBody` step onto its firing mode). -/
theorem bigChoiceP_sem_forward {ps : List (Program (Var n))} {ν μ : State (Var n)}
    (h : Program.sem (bigChoiceP ps) ν μ) : ∃ p ∈ ps, Program.sem p ν μ := by
  induction ps with
  | nil => exact absurd h (by simp [bigChoiceP, Program.sem, Formula.sat])
  | cons a as ih =>
      rcases h with h | h
      · exact ⟨a, List.mem_cons_self, h⟩
      · obtain ⟨p, hp, hsem⟩ := ih h; exact ⟨p, List.mem_cons_of_mem _ hp, hsem⟩

/-- The empty ODE system is the identity: every variable is unbound, so the mask freezes it. -/
theorem sem_ode_nil {dom : Formula (Var n)} {ν μ : State (Var n)}
    (h : Program.sem (Program.ode [] dom) ν μ) : μ = ν := by
  obtain ⟨r, Φ, hr, _, hΦr, _, hmask, _⟩ := h
  funext x
  rw [← hΦr, hmask r ⟨hr, le_refl r⟩ x (by simp [ODESystem.bound])]

/-- **(A) — static reposition preserves `invLe g`.** A `modeStep` at a zero-motion (`m.sys = []`)
mode is a state-preserving declared-edge mode switch; `invLe g` survives because the continuous
state is unchanged and the `mv`-assign is invisible to `g` (`mv ∉ g.fv`). -/
theorem reposition_step_pres (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (hg : mv ∉ g.fv) (hsys : m.sys = [])
    {ν μ : State (Var n)} (hsem : Program.sem (modeStep G mv q m) ν μ)
    (hinv : Formula.sat (invLe g) ν) : Formula.sat (invLe g) μ := by
  -- modeStep = test(mode=q) ; ode m.sys dom ; bigChoiceP (edges)
  obtain ⟨κ1, htest, κ2, hode, hjump⟩ := hsem
  -- test passes: κ1 = ν
  have e1 : κ1 = ν := htest.1.symm
  -- empty ODE is the identity: κ2 = ν
  rw [hsys, e1] at hode
  have e2 : κ2 = ν := sem_ode_nil hode
  rw [e2] at hjump
  -- the jump is a declared edge's `test e.guard ; assign mv := e.tgt`
  obtain ⟨p, hpmem, hpsem⟩ := bigChoiceP_sem_forward hjump
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpmem
  obtain ⟨κ3, hg3, hasgn⟩ := hpsem
  have e3 : κ3 = ν := hg3.1.symm
  rw [e3] at hasgn
  -- `assign` sem is pointwise: `hasgn.2 : ∀ y ≠ mv, μ y = ν y`; on `g.fv` (which excludes `mv`)
  -- `μ` agrees with `ν`, so `invLe g` transfers by coincidence.
  have heq : Set.EqOn ν μ (invLe g).fv := by
    intro x hx
    have hxne : x ≠ mv := by
      rintro rfl
      exact hg (by simpa only [invLe, Formula.fv, Term.fv, Set.union_empty] using hx)
    exact (hasgn.2 x hxne).symm
  exact (Formula.coincidence (invLe g) heq).mp hinv

/-- **(B) — dynamic reposition = flow machinery with `fL = 0`.** The dynamic reposition's right
segment evolves under the frozen-left field `m.dynSys = jointSys (0) fR lam` (`ṡ_L = 0`); its cert
`repoDynPresPre : SegPreservesOn g m.dynSys m.dynDomPre` is exactly the joint `BoxLe` that
`segment_faModal` consumes with `fL := 0`. So its modality image is the SAME `⟨ode rightBlock⟩`
diamond as the flow case — genuine reuse, NOT a new lemma. This wrapper makes the instantiation
explicit and confirms `fL = 0` presents no obstruction (the `hdisj`/footprint side-conditions hold:
`leftBlock 0` reads nothing, so it is disjoint from the right block). -/
theorem dynreposition_faModal (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (ν : State (Var n))
    (hdisj : Disjoint ((leftBlock (fun _ => Term.const 0)).boundSet ∪
                        (leftBlock (fun _ => Term.const 0)).readVars)
                      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock (fun _ => Term.const 0)).boundSet ∪
             (leftBlock (fun _ => Term.const 0)).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (hcert : BoxLe (Program.ode (jointSys (fun _ => Term.const 0) fR lam) (Formula.and domL domR))
        (fun ω => Term.eval g ω) ν)
    (hExist : ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ leftBlock (fun _ => Term.const 0),
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock (fun _ => Term.const 0)).bound → ΦL t x = ν x) →
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
        ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t))) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock (fun _ => Term.const 0)) domL)
      (Program.ode (rightBlock fR lam) domR) (invLe g)) ν :=
  segment_faModal g (fun _ => Term.const 0) fR lam domL domR ν hdisj hφL hφR hcert hExist

/-- **Piece 1 core — the ODE-semigroup split.** A single left flow splits at any interior time `t`
into two runs (`ν → Φt`, `Φt → μ`). Reverse of the banked `sem_ode_glue`; proven by restricting the
integral curve to `[0,t]` and shifting it to `[t,r]`. This is the general form; the zero-padding
`sem_ode_sub_piter` (one real factor) is its `t = 0` / `t = r` degenerate case. Flow segments split
off a `t > 0` piece; reposition segments are the `t = 0` (zero-duration) case. -/
theorem sem_ode_split {sys : ODESystem (Var n)} {dom : Formula (Var n)} (hwf : sys.WellFormed)
    {ν μ : State (Var n)} (h : Program.sem (Program.ode sys dom) ν μ) :
    ∀ {r : ℝ} {Φ : ℝ → State (Var n)}, 0 ≤ r → Φ 0 = ν → Φ r = μ →
      (∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt (fun s => Φ s) (odeField sys (Φ t)) (Icc 0 r) t) →
      (∀ t ∈ Icc (0:ℝ) r, Formula.sat dom (Φ t)) →
      ∀ t, t ∈ Icc (0:ℝ) r →
        Program.sem (Program.ode sys dom) ν (Φ t) ∧
        Program.sem (Program.ode sys dom) (Φ t) μ := by
  intro r Φ hr hΦ0 hΦr hcΦ hdΦ t ht
  constructor
  · -- first piece [0,t]: restrict Φ
    refine (sem_ode_iff_integralCurve hwf).mpr ⟨t, Φ, ht.1, hΦ0, rfl, ?_, ?_⟩
    · intro s hs
      exact (hcΦ s ⟨hs.1, hs.2.trans ht.2⟩).mono (Set.Icc_subset_Icc (le_refl 0) ht.2)
    · intro s hs; exact hdΦ s ⟨hs.1, hs.2.trans ht.2⟩
  · -- second piece [t,r]: shift Φ by t
    refine (sem_ode_iff_integralCurve hwf).mpr ⟨r - t, fun s => Φ (t + s), by linarith [ht.2],
      by simp, by simp [hΦr], ?_, ?_⟩
    · intro s hs
      have hts : t + s ∈ Icc (0:ℝ) r := ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩
      have hcomp : HasDerivWithinAt (fun u : ℝ => t + u) (1 : ℝ) (Icc 0 (r - t)) s :=
        (hasDerivWithinAt_id s (Icc 0 (r - t))).const_add t
      have hmaps : Set.MapsTo (fun u : ℝ => t + u) (Icc 0 (r - t)) (Icc 0 r) :=
        fun u hu => ⟨by linarith [ht.1, hu.1], by linarith [hu.2]⟩
      have := (hcΦ (t + s) hts).scomp s hcomp hmaps
      rwa [one_smul] at this
    · intro s hs; exact hdΦ (t + s) ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩

/-- Disjointness lifts over `bigSeq`: disjoint from every piece ⟹ disjoint from the sequence. -/
theorem disjoint_vars_bigSeq {A : Set (Var n)} :
    ∀ {L : List (Program (Var n))}, (∀ q ∈ L, Disjoint A (Program.vars q)) →
      Disjoint A (Program.vars (bigSeq L))
  | [], _ => by simp [bigSeq, Program.vars, Program.fv, Program.bv, Formula.fv]
  | q :: qs, h => by
      have htail := disjoint_vars_bigSeq (fun r hr => h r (List.mem_cons_of_mem q hr))
      have hsub : Program.vars (bigSeq (q :: qs)) ⊆
          Program.vars q ∪ Program.vars (bigSeq qs) := by
        intro x hx
        simp only [bigSeq, Program.vars, Program.fv, Program.bv, Set.mem_union, Set.mem_diff] at hx ⊢
        tauto
      exact (Set.disjoint_union_right.mpr ⟨h q (List.mem_cons_self ..), htail⟩).mono_right hsub

/-- **Piece 1 — the general MULTI composition.** A single left flow couples with a right segment
sequence `bigSeq (map snd pairs)`, where each segment couples with its OWN left factor `p.1`
(`p.1 = ode leftBlock` for a flow segment, `test ⊤` for a zero-time reposition). Composed
segment-by-segment via `faModal_seq` — the per-segment coupling, replacing `multiseg_het`'s
over-restrictive uniform hypothesis. Flow and reposition are the two `p.1` shapes; no class split. -/
theorem multiseg_gen (φinv : Formula (Var n)) :
    ∀ (pairs : List (Program (Var n) × Program (Var n))),
      (∀ p ∈ pairs, ∀ q ∈ pairs,
          Disjoint (Program.vars (p.2.rename (Equiv.refl (Var n)))) (Program.vars q.1)) →
      (∀ p ∈ pairs, ∀ σ, Formula.sat φinv σ →
          Formula.sat (faModal (Equiv.refl (Var n)) p.1 p.2 φinv) σ) →
      ∀ ω, Formula.sat φinv ω →
        Formula.sat (faModal (Equiv.refl (Var n)) (bigSeq (pairs.map Prod.fst))
          (bigSeq (pairs.map Prod.snd)) φinv) ω := by
  intro pairs
  induction pairs with
  | nil =>
      intro _ _ ω hω
      simp only [List.map_nil, bigSeq]
      rw [faModal_sat]
      intro ν hν
      rw [sem_test] at hν
      obtain ⟨rfl, _⟩ := hν
      exact ⟨ω, by rw [rename_test, sem_test]; exact ⟨rfl, trivial⟩, hω⟩
  | cons p rest ih =>
      intro hdis hcouple ω hω
      simp only [List.map_cons, bigSeq]
      refine faModal_seq (Equiv.refl (Var n)) p.1 (bigSeq (rest.map Prod.fst)) p.2
        (bigSeq (rest.map Prod.snd)) φinv ω ?_ ?_
      · -- Disjoint (vars (p.2.rename id)) (vars (bigSeq (rest.map fst)))
        refine disjoint_vars_bigSeq ?_
        intro r hr
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact hdis p (List.mem_cons_self ..) q (List.mem_cons_of_mem p hq)
      · refine faModal_MR (Equiv.refl (Var n)) p.1 p.2 φinv _ ω
          (hcouple p (List.mem_cons_self ..) ω hω) ?_
        intro μ hμ
        exact ih (fun a ha b hb => hdis a (List.mem_cons_of_mem p ha) b (List.mem_cons_of_mem p hb))
          (fun a ha => hcouple a (List.mem_cons_of_mem p ha)) μ hμ

/-- **The per-switch faithful lift** — the real content beyond the flat `reified_relational_multi`.
One right-mode flow at a **declared** mode `q`, followed by a **declared** ⊤-guarded edge `e`
(`e ∈ edgesFrom q`, `e.tgt < modes.length` — `EdgeTargetsValid`, the flat-`R*` guardrail), becomes
one `star (rightAutomatonBody G mv)` step, threading the mode variable `q → e.tgt`. This is the
∃-right faithfulness the emitted `rights` switch must respect: it maps to a real `G`-edge, not a
flat memoryless choice. Mirrors the witness lemma's `jump` case, per segment. -/
theorem single_seg_R_real (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (hfv : mv ∉ (Program.ode m.sys m.dom).fv)
    {e : REdge (Var n)} (hm : G.modeAt q = some m) (he : e ∈ G.edgesFrom q)
    (htt : e.guard = Formula.tt) (hlt : e.tgt < G.modes.length)
    {ν μ : State (Var n)} (hflow : Program.sem (Program.ode m.sys m.dom) ν μ) :
    Program.sem (Program.star (rightAutomatonBody G mv))
      (Function.update ν mv (q : ℝ)) (Function.update μ mv (e.tgt : ℝ)) := by
  have hg : Formula.sat e.guard (Function.update μ mv (q : ℝ)) := by rw [htt]; trivial
  have hstep := modeStep_sem G mv q m hfv he hflow hg
  have hbody : Program.sem (rightAutomatonBody G mv)
      (Function.update ν mv (q : ℝ)) (Function.update μ mv (e.tgt : ℝ)) := by
    refine bigChoiceP_sem_of_mem (List.mem_filterMap.mpr ⟨q, ?_, ?_⟩) hstep
    · exact List.mem_range.mpr (by
        have := hm; simp only [SearchGraph.modeAt] at this
        exact List.getElem?_eq_some_iff.mp this |>.1)
    · rw [hm]; rfl
  exact Relation.ReflTransGen.head hbody Relation.ReflTransGen.refl

end RelCertifier
