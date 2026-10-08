/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3_M1` — the DECLARED mode-dependent invariant, composed across left switches

`Rover3M1Modal.rover3_M1_modal` states Theorem 3 at the weakest declared row (`Stop`,
offset 2) for every left window, over `Var 2`. The mode-keyed statement needs a THIRD
auxiliary coordinate for the left mode variable `u_L` (`mv = (Aux, 0)` and the clock
`tg = (Aux, 1)` exhaust `Var 2`'s auxiliaries), so this leaf re-lowers the same benchmark
(the same `rover3_M1_IR` literal, the same `vsP = [px, vx]`) at the padded ambient
dimension `n = 3` — the padding device the development already uses for benchmarks whose
state-variable count is below the ambient `n` (`FaithfulBridgePad`, `arm_chain_rung1`).
The pad coordinate has field `0` on both sides and is unconstrained; every lemma below
is the `Var 2` instance's lemma at `Var 3`.

It then states what the file declares: one row per LEFT mode (`Drive` 0.5, `Drift` 1.0,
`Stop` 2.0), keyed by `u_L = (Aux, 2)`, as a ∀∃ invariant of the full left automaton over
the file's `next` lists, composed from the offset-independent catch-up step and the
in-kernel handoffs (nested constant offsets). Z3-free.
-/
import RelCertifier.Instances.Rover3M1Modal
import RelCertifier.Proofs.Encoding.ModeHandoff

namespace RelCertifier
namespace Rover3M1Handoff

open DL DLCalTiming DLRel Parse Set Rover3M1Modal

set_option maxHeartbeats 12800000

/-! ## The benchmark at the padded dimension `n = 3` -/

abbrev mvP3 : Var 3 := (Side.Aux, 0)
abbrev aP3 : Fin 3 := (1 : Fin 3)
abbrev tgP3 : Var 3 := (Side.Aux, aP3)
/-- The left mode variable — the third auxiliary. -/
abbrev ulP3 : Var 3 := (Side.Aux, 2)

noncomputable def fLP3 (l : ℕ) : Fin 3 → Term (Var 3) := hostDyn vsP 3 Side.L (mLP l)
noncomputable def fRP3 (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vsP 3 Side.R (mRP q)
noncomputable def domLP3 : Formula (Var 3) := hostEvolve vsP 3 Side.L (mLP 0)
noncomputable def domRP3 : Formula (Var 3) := hostEvolve vsP 3 Side.R (mRP 0)
noncomputable def envP3 : Formula (Var 3) := Formula.and domLP3 domRP3

/-! ## The declared rows -/

def invRowPF (r : ℕ) : Parse.PForm := (rover3_M1_IR.invariants.getD r ("", Parse.PForm.tt)).2

noncomputable def gRow (r : ℕ) : Term (Var 3) :=
  ((Run.invToG vsP 3 ((atomsOf (invRowPF r)).getD 0 .tt)).map ITerm.toHost).getD (Term.const 0)

noncomputable def FRow (r : ℕ) : Formula (Var 3) := FM (gRow r) []
noncomputable def ϕRow (r : ℕ) : RFormula (Var 3) := canonInvM (gRow r) []

theorem encode_ϕRow (r : ℕ) : encode (Equiv.refl (Var 3)) (ϕRow r) = FRow r :=
  encode_canonInvM (gRow r) []

noncomputable def cRow (r : ℕ) : ℝ := if r = 0 then 1/2 else if r = 1 then 1 else 2

theorem eval_gRow (r : ℕ) (hr : r < 3) (x : State (Var 3)) :
    Term.eval (gRow r) x = x (Lv 0) - (x (Rv 0) + cRow r) := by
  have hdL : ("L_px".drop 2).copy = "px" := by decide
  have hdR : ("R_px".drop 2).copy = "px" := by decide
  interval_cases r <;>
  · simp [gRow, atomsOf, invRowPF, rover3_M1_IR, Run.invToG, Run.lowerE, vsP,
      Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp05, hp10, hp20,
      ITerm.toHost, Term.eval, AOp.interp, Lv, Rv, cRow]

theorem hgRow (r : ℕ) : (gRow r).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem aux_notin_gRow (a : Fin 3) (r : ℕ) : ((Side.Aux, a) : Var 3) ∉ (gRow r).fv := by
  intro h
  rcases hgRow r h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem aux_notin_FRow (a : Fin 3) (r : ℕ) : ((Side.Aux, a) : Var 3) ∉ (FRow r).fv :=
  notMem_FM_fv (fun g' hg' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl; exact aux_notin_gRow a r)

theorem sat_FRow (r : ℕ) (hr : r < 3) (x : State (Var 3)) :
    Formula.sat (FRow r) x ↔ x (Lv 0) ≤ x (Rv 0) + cRow r := by
  unfold FRow
  rw [sat_FM_iff]
  constructor
  · intro h
    have := h (gRow r) List.mem_cons_self
    rw [eval_gRow r hr] at this; linarith
  · intro h g' hg'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    subst hg'; rw [eval_gRow r hr]; linarith

/-! ## Side-splits -/

theorem fLP3_pipe (l : ℕ) (i : Fin 3) : fLP3 l i =
    (((some (mLP l)).bind (Run.dynOf vsP 3 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRP3_pipe (q : ℕ) (i : Fin 3) : fRP3 q i =
    (((some (mRP q)).bind (Run.dynOf vsP 3 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLP3_pipe : domLP3 =
    (((some (mLP 0)).bind (fun m => Run.lowerF vsP 3 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRP3_pipe : domRP3 =
    (((some (mRP 0)).bind (fun m => Run.lowerF vsP 3 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLP3 (l : ℕ) (hl : l < 3) : ∀ i, (fLP3 l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsP) (some (mLP l))
    (by interval_cases l <;>
      simp [mLP, rover3_M1_IR, Parse.PExpr.namesFree]) i x
    (fLP3_pipe l i ▸ hx))

theorem hfRP3 (q : ℕ) (hq : q < 3) : ∀ i, (fRP3 q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsP) (some (mRP q))
    (by interval_cases q <;>
      simp [mRP, rover3_M1_IR, Parse.PExpr.namesFree]) i x
    (fRP3_pipe q i ▸ hx))

theorem hdomLP3 : domLP3.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsP) (some (mLP 0))
    (by simp [mLP, rover3_M1_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domLP3_pipe ▸ hx))

theorem hdomRP3 : domRP3.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsP) (some (mRP 0))
    (by simp [mRP, rover3_M1_IR, Parse.PForm.namesFree,
      Parse.PExpr.namesFree]) x (domRP3_pipe ▸ hx))

theorem hmvenvP3 : mvP3 ∉ envP3.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLP3 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRP3 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem hulenvP3 : ulP3 ∉ envP3.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLP3 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRP3 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The right graph (one-way chain) -/

noncomputable def modeP3 (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fRP3 q) (Term.const 1), dom := domRP3, weight := 1 }

def edgeP3 (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := Formula.tt, pruned := false }

noncomputable def GrP3 : SearchGraph (Var 3) :=
  { modes := [modeP3 0, modeP3 1, modeP3 2],
    edges := [edgeP3 0 1, edgeP3 0 0, edgeP3 1 2, edgeP3 1 1, edgeP3 2 2] }

theorem GrP3_modeAt (q : ℕ) (hq : q < 3) : GrP3.modeAt q = some (modeP3 q) := by
  interval_cases q <;> rfl

theorem httP3 : ∀ q, ∀ e ∈ GrP3.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrP3.edges := List.mem_of_mem_filter he
  simp only [GrP3, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltP3 : ∀ q, ∀ e ∈ GrP3.edgesFrom q, e.tgt < GrP3.modes.length := by
  intro q e he
  have hmem : e ∈ GrP3.edges := List.mem_of_mem_filter he
  simp only [GrP3, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num [GrP3, edgeP3]

theorem hRvP3 : ∀ q m, GrP3.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 3 ∧ m = modeP3 q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP3] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP3] using hm.symm⟩
    | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP3] using hm.symm⟩
    | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrP3])
  obtain ⟨hq3, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRP3 q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRP3 q) (Term.const 1) (hfRP3 q hq3)
      (by simp [Term.fv]) hy
  · exact hdomRP3 hy

theorem edgeP3_mem : ∀ st tgt, edgeP3 st tgt ∈ GrP3.edges →
    edgeP3 st tgt ∈ GrP3.edgesFrom st :=
  fun st tgt he => List.mem_filter.mpr ⟨he, by simp [edgeP3]⟩

theorem hfreshP3 : ∀ q m, GrP3.modeAt q = some m →
    mvP3 ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvP3 q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## Field and shape pins at `n = 3` (the pad row is the zero field) -/

noncomputable def cstP3 (q : ℕ) : ℝ := if q = 0 then 2/5 else if q = 1 then 1/5 else 0

theorem fRP30_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRP3 q 0) x = x (Rv 1) := by
  interval_cases q <;>
    · simp [fRP3, hostDyn, mRP, rover3_M1_IR, vsP, Run.dynOf,
      Run.lowerE, hp04, hp02, hp0, hp1, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]
      try ring

theorem fRP31_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRP3 q 1) x = cstP3 q := by
  interval_cases q <;>
    · simp [fRP3, hostDyn, mRP, rover3_M1_IR, vsP, Run.dynOf,
      Run.lowerE, hp04, hp02, hp0, hp1, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv, cstP3]
      try norm_num

theorem fRP32_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fRP3 q 2) x = 0 := by
  interval_cases q <;>
    · simp [fRP3, hostDyn, mRP, rover3_M1_IR, vsP, Run.dynOf,
      Run.lowerE, hp04, hp02, hp0, hp1, Run.resolveVar,
      List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Rv]

theorem sat_domRP3 (x : State (Var 3)) : Formula.sat domRP3 x ↔
    (-(1:ℝ)/20 ≤ x (Rv 0) ∧ (1:ℝ)/4 ≤ x (Rv 1) ∧ x (Rv 1) ≤ (11:ℝ)/10) := by
  simp only [domRP3, hostEvolve, mRP, rover3_M1_IR, vsP]
  simp [Run.lowerF, Run.lowerE, hpm005, hp025, hp11,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]
  tauto

theorem sat_domLP3 (x : State (Var 3)) : Formula.sat domLP3 x ↔
    (-(1:ℝ)/20 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 12 ∧ -(1:ℝ)/20 ≤ x (Lv 1) ∧ x (Lv 1) ≤ 1) := by
  simp only [domLP3, hostEvolve, mLP, rover3_M1_IR, vsP]
  simp [Run.lowerF, Run.lowerE, hpm005, hp120, hp10, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Lv]
  tauto

/-! ## Window facts specialized to the left position -/

theorem leftBlock_wf3 (fL : Fin 3 → Term (Var 3)) : (leftBlock fL).WellFormed := by
  have hLinj : Function.Injective (Lv (n := 3)) := by
    intro a b h; simpa [Lv, Prod.ext_iff] using h
  unfold ODESystem.WellFormed leftBlock
  simp only [List.map_map, Function.comp_def]
  exact (List.nodup_finRange 3).map hLinj

theorem htg_leftBlock3 (fL : Fin 3 → Term (Var 3)) : tgP3 ∉ (leftBlock fL).bound := by
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub fL _ h
  exact aux_ne_Lv 1 i hi

theorem fLP30_eval (l : ℕ) (hl : l < 3) (x : State (Var 3)) :
    Term.eval (fLP3 l 0) x = x (Lv 1) := by
  interval_cases l <;>
    · simp [fLP3, hostDyn, mLP, rover3_M1_IR, vsP, Run.dynOf,
        Run.lowerE, hp02, hp01, hpm05, hp0, hp1, Run.resolveVar,
        List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp, Lv]

theorem window_pxL_bound3 (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : 0 ≤ dt) (k : ℕ)
    {σ ν : State (Var 3)}
    (hsem : Program.sem (windowSeg (leftBlock (fLP3 l)) domLP3 tgP3 dt k) σ ν) :
    ν (Lv 0) ≤ σ (Lv 0) + (k : ℝ) * dt := by
  have hwfL := leftBlock_wf3 (fLP3 l)
  have htgb := htg_leftBlock3 (fLP3 l)
  have hbnd : ∀ x : State (Var 3), Formula.sat domLP3 x →
      Lie (DLCalTiming.clk tgP3 (leftBlock (fLP3 l)))
        (fun ω => Term.eval (Term.var (Lv 0)) ω) x ≤ 1 := by
    intro x hx
    have hfun : (fun ω : State (Var 3) => Term.eval (Term.var (Lv 0)) ω)
        = fun y => (1 : ℝ) * y (Lv 0) + 0 := by
      funext y; simp [Term.eval]
    rw [hfun, lie_affine_coord _ (clk_wellFormed tgP3 _ hwfL htgb) (Lv 0) 1 0 x]
    have hmem : ((Lv 0 : Var 3), fLP3 l 0) ∈ DLCalTiming.clk tgP3 (leftBlock (fLP3 l)) := by
      simp only [DLCalTiming.clk, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
    have hb : (Lv 0 : Var 3) ∈ (DLCalTiming.clk tgP3 (leftBlock (fLP3 l))).bound :=
      List.mem_map.mpr ⟨_, hmem, rfl⟩
    have hfield : odeField (DLCalTiming.clk tgP3 (leftBlock (fLP3 l))) x (Lv 0)
        = Term.eval (fLP3 l 0) x := by
      simp only [odeField, if_pos hb]
      rw [ODESystem.rhs_eq_of_mem (clk_wellFormed tgP3 _ hwfL htgb) hmem]
    rw [hfield, fLP30_eval l hl]
    have := (sat_domLP3 x).mp hx
    linarith [this.2.2.2]
  have hg := windowSeg_growth (leftBlock (fLP3 l)) domLP3 tgP3 dt k hwfL htgb
    (Term.var (Lv 0)) 1 (by norm_num)
    (by intro h; simp only [Term.fv, Set.mem_singleton_iff] at h;
        exact absurd h (by simp [tgP3, Lv, Prod.ext_iff])) hbnd hdt hsem
  simpa [Term.eval] using hg

theorem window_maskP3 (l : ℕ) (dt : ℝ) (k : ℕ)
    {σ ν : State (Var 3)}
    (hsem : Program.sem (windowSeg (leftBlock (fLP3 l)) domLP3 tgP3 dt k) σ ν) :
    ∀ j : Fin 3, ν (Rv j) = σ (Rv j) := by
  intro j
  refine windowSeg_mask (leftBlock (fLP3 l)) domLP3 tgP3 dt k (leftBlock_wf3 (fLP3 l))
    (htg_leftBlock3 (fLP3 l)) hsem (Rv j) ?_
  intro h
  simp only [DLCalTiming.clk, ODESystem.bound, List.map_append, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLP3 l) _ (by simpa [ODESystem.bound] using h)
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact absurd h (by simp [Rv, tgP3, Prod.ext_iff])

/-! ## The Safe hold run -/

theorem sem_safe_hold3 (τ : ℝ) (hτ : 0 ≤ τ) {μ : State (Var 3)}
    (hdom : Formula.sat domRP3 μ) :
    Program.sem (Program.ode (rightBlock (fRP3 2) (Term.const 1)) domRP3) μ
      (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 1) * τ else μ x) := by
  have hR : (-(1:ℝ)/20 ≤ μ (Rv 0) ∧ (1:ℝ)/4 ≤ μ (Rv 1) ∧ μ (Rv 1) ≤ (11:ℝ)/10) := by
    have := (sat_domRP3 μ).mp hdom
    exact ⟨this.1, this.2.1, this.2.2⟩
  have hne10 : (Rv 1 : Var 3) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  have hne20 : (Rv 2 : Var 3) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
  classical
  refine ⟨τ, fun t x => if x = Rv 0 then μ (Rv 0) + μ (Rv 1) * t else μ x,
    hτ, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; simp
    · simp [if_neg h0]
  · rfl
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    fin_cases i
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRP3 2 ⟨0, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 1) * t else μ x)
          = μ (Rv 1) := by
        simp [Term.eval, AOp.interp, show fRP3 2 ⟨0, by norm_num⟩ = fRP3 2 0 from rfl,
          fRP30_eval 2 (by norm_num), if_neg hne10]
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => μ (Rv 0) + μ (Rv 1) * u)
          (μ (Rv 1) * 1) (Set.Icc 0 τ) t :=
        ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)).const_mul (μ (Rv 1))).const_add (μ (Rv 0))
      have heq : μ (Rv 1) * 1 = μ (Rv 1) := by ring
      rw [heq] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp
      · simp
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRP3 2 ⟨1, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 1) * t else μ x)
          = 0 := by
        simp [Term.eval, AOp.interp, show fRP3 2 ⟨1, by norm_num⟩ = fRP3 2 1 from rfl,
          fRP31_eval 2 (by norm_num), cstP3]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv 1))) ?_ ?_
      · intro y _; simp [if_neg hne10]
      · simp [if_neg hne10]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRP3 2 ⟨2, by norm_num⟩))
          (fun x => if x = Rv 0 then μ (Rv 0) + μ (Rv 1) * t else μ x)
          = 0 := by
        simp [Term.eval, AOp.interp, show fRP3 2 ⟨2, by norm_num⟩ = fRP3 2 2 from rfl,
          fRP32_eval 2 (by norm_num)]
      simp only [heval]
      refine HasDerivWithinAt.congr
        (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (μ (Rv 2))) ?_ ?_
      · intro y _; simp [if_neg hne20]
      · simp [if_neg hne20]
  · intro t ht x hx
    have hx0 : x ≠ Rv 0 := by
      intro h; subst h
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp [if_neg hx0]
  · intro t ht
    rw [sat_domRP3]
    have ht0 : (0:ℝ) ≤ t := ht.1
    refine ⟨?_, ?_, ?_⟩
    · simp only [eq_self_iff_true, if_true, if_pos rfl]
      have : 0 ≤ μ (Rv 1) * t := mul_nonneg (by linarith [hR.2.1]) ht0
      linarith [hR.1]
    · simp only [if_neg hne10]
      exact hR.2.1
    · simp only [if_neg hne10]
      exact hR.2.2

/-! ## The per-left-mode step at the mode's own row -/

theorem HmultiRow (r : ℕ) (hr : r < 3) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ (q : ℕ), q < GrP3.modes.length → ∀ σ, σ mvP3 = (q : ℝ) →
      Formula.sat (Formula.and (FRow r) envP3) σ →
      ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
        (∀ s ∈ segs, GrP3.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrP3.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 3))
          (windowSeg (leftBlock (fLP3 r)) domLP3 tgP3 dt 2)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FRow r) envP3)) σ := by
  intro q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrP3] using hq
  have hφ : σ (Lv 0) ≤ σ (Rv 0) + cRow r := (sat_FRow r hr σ).mp hσ.1
  have hdomRσ : Formula.sat domRP3 σ := hσ.2.2
  have hRb := (sat_domRP3 σ).mp hdomRσ
  have hchain2 : ∀ (a b c : ℕ × RMode (Var 3) × REdge (Var 3)),
      a.2.2.tgt = b.1 → b.2.2.tgt = c.1 →
      List.IsChain (fun x y => x.2.2.tgt = y.1) [a, b, c] := by
    intro a b c hab hbc
    refine (List.isChain_cons.mpr ⟨?_, ?_⟩)
    · intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; exact hab
    · refine (List.isChain_cons.mpr ⟨?_, by simp⟩)
      intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; exact hbc
  have hbody : ∀ (pres : List (Program (Var 3))),
      (∀ Q ∈ pres, ∀ μ : State (Var 3), Formula.sat domRP3 μ →
        Program.sem Q μ μ) →
      Formula.sat (faModal (Equiv.refl (Var 3))
        (windowSeg (leftBlock (fLP3 r)) domLP3 tgP3 dt 2)
        (bigSeq (pres ++ [Program.ode (rightBlock (fRP3 2) (Term.const 1)) domRP3]))
        (Formula.and (FRow r) envP3)) σ := by
    intro pres hpres
    rw [faModal_sat]
    intro ν hleft
    have hpx := window_pxL_bound3 r hr dt hdt 2 hleft
    push_cast at hpx
    have hmaskν := window_maskP3 r dt 2 hleft
    have hdomLν := windowSeg_end_domL (leftBlock (fLP3 r)) domLP3 tgP3 dt 2
      (by norm_num) hleft
    have hdomRν : Formula.sat domRP3 ν := by
      rw [sat_domRP3]
      rw [hmaskν 0, hmaskν 1]
      exact (sat_domRP3 σ).mp hdomRσ
    set τ : ℝ := 8 * dt with hτdef
    have hτ : 0 ≤ τ := by positivity
    have hhold := sem_safe_hold3 τ hτ hdomRν
    set μfin : State (Var 3) :=
      (fun x => if x = Rv 0 then ν (Rv 0) + ν (Rv 1) * τ else ν x) with hμfin
    have hsemseq : Program.sem
        (bigSeq (pres ++ [Program.ode (rightBlock (fRP3 2) (Term.const 1)) domRP3]))
        ν μfin := by
      clear hpx
      induction pres with
      | nil =>
          simp only [List.nil_append, bigSeq]
          exact ⟨μfin, hhold, by rw [sem_test]; exact ⟨rfl, trivial⟩⟩
      | cons Q rest ih =>
          simp only [List.cons_append, bigSeq]
          refine ⟨ν, hpres Q List.mem_cons_self ν hdomRν, ?_⟩
          exact ih (fun Q' hQ' => hpres Q' (List.mem_cons_of_mem _ hQ'))
    refine ⟨μfin, by rw [Program.rename_refl]; exact hsemseq, ?_, ?_⟩
    · rw [sat_FRow r hr]
      have hν0 : μfin (Lv 0) = ν (Lv 0) := by
        simp [hμfin, if_neg (show (Lv 0 : Var 3) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff])]
      have hνR : μfin (Rv 0) = ν (Rv 0) + ν (Rv 1) * τ := by simp [hμfin]
      rw [hν0, hνR]
      have hvfloor : (1:ℝ)/4 ≤ ν (Rv 1) := by
        rw [hmaskν 1]; exact hRb.2.1
      have hgain : 2 * dt ≤ ν (Rv 1) * τ := by
        rw [hτdef]
        nlinarith
      have hRν : ν (Rv 0) = σ (Rv 0) := hmaskν 0
      rw [hRν]
      linarith
    · constructor
      · have : Formula.sat domLP3 μfin := by
          rw [sat_domLP3]
          have h0 : μfin (Lv 0) = ν (Lv 0) := by
            simp [hμfin, if_neg (show (Lv 0 : Var 3) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff])]
          have h1 : μfin (Lv 1) = ν (Lv 1) := by
            simp [hμfin, if_neg (show (Lv 1 : Var 3) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff])]
          rw [h0, h1]
          exact (sat_domLP3 ν).mp hdomLν
        exact this
      · exact sem_ode_ends_in_domain hhold
  interval_cases q
  · refine ⟨[(0, modeP3 0, edgeP3 0 1), (1, modeP3 1, edgeP3 1 2), (2, modeP3 2, edgeP3 2 2)],
      ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact ⟨GrP3_modeAt 0 (by norm_num), edgeP3_mem 0 1 (by simp [GrP3])⟩
      · exact ⟨GrP3_modeAt 1 (by norm_num), edgeP3_mem 1 2 (by simp [GrP3])⟩
      · exact ⟨GrP3_modeAt 2 (by norm_num), edgeP3_mem 2 2 (by simp [GrP3])⟩
    · exact hchain2 _ _ _ rfl rfl
    · intro s hs
      simp only [List.head?_cons, Option.some_inj] at hs
      rw [← hs]
    · have := hbody [Program.ode (rightBlock (fRP3 0) (Term.const 1)) domRP3,
        Program.ode (rightBlock (fRP3 1) (Term.const 1)) domRP3]
        (by
          intro Q hQ μ hdom
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
          rcases hQ with rfl | rfl
          · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRP3 0)
              (lam := Term.const 1) (domR := domRP3) hdom
            rwa [hρ] at hsem
          · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRP3 1)
              (lam := Term.const 1) (domR := domRP3) hdom
            rwa [hρ] at hsem)
      simpa [modeP3] using this
  · refine ⟨[(1, modeP3 1, edgeP3 1 2), (2, modeP3 2, edgeP3 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact ⟨GrP3_modeAt 1 (by norm_num), edgeP3_mem 1 2 (by simp [GrP3])⟩
      · exact ⟨GrP3_modeAt 2 (by norm_num), edgeP3_mem 2 2 (by simp [GrP3])⟩
    · refine (List.isChain_cons.mpr ⟨?_, by simp⟩)
      intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; rfl
    · intro s hs
      simp only [List.head?_cons, Option.some_inj] at hs
      rw [← hs]
    · have := hbody [Program.ode (rightBlock (fRP3 1) (Term.const 1)) domRP3]
        (by
          intro Q hQ μ hdom
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
          subst hQ
          obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRP3 1)
            (lam := Term.const 1) (domR := domRP3) hdom
          rwa [hρ] at hsem)
      simpa [modeP3] using this
  · refine ⟨[(2, modeP3 2, edgeP3 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact ⟨GrP3_modeAt 2 (by norm_num), edgeP3_mem 2 2 (by simp [GrP3])⟩
    · simp
    · intro s hs
      simp only [List.head?_cons, Option.some_inj] at hs
      rw [← hs]
    · have := hbody [] (by intro Q hQ; exact absurd hQ (List.not_mem_nil))
      simpa [modeP3] using this

/-! ## The left automaton, from the file -/

def nextP3 : List (List ℕ) :=
  (List.range 3).map (fun l => (mLP l).next.filterMap (Handoff.leftModeIndex rover3_M1_IR))

/-- `Drive → [Drift, Drive]`, `Drift → [Stop, Drift]`, `Stop → [Stop]`. -/
theorem nextP3_eq : nextP3 = [[1, 0], [2, 1], [2]] := by decide

/-- The left graph's transitions are exactly the ones the handoff runner checks. -/
theorem nextP3_transitions :
    ((List.range 3).flatMap (fun m' => (nextP3.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions rover3_M1_IR := by decide

noncomputable def guardsP3 : List (Formula (Var 3)) :=
  (List.range 3).map (fun l => hostGuard vsP 3 Side.L (mLP l))

noncomputable def AP3 (dt : ℝ) : LeftAut 3 :=
  { windows := (List.range 3).map (fun l => windowSeg (leftBlock (fLP3 l)) domLP3 tgP3 dt 2),
    guards := guardsP3,
    next := nextP3 }

theorem AP3_numModes (dt : ℝ) : (AP3 dt).numModes = 3 := rfl

theorem AP3_window (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (AP3 dt).window t = windowSeg (leftBlock (fLP3 t)) domLP3 tgP3 dt 2 := by
  interval_cases t <;> rfl

theorem AP3_guard (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (AP3 dt).guard t = hostGuard vsP 3 Side.L (mLP t) := by
  interval_cases t <;> rfl

theorem AP3_succ (dt : ℝ) (m' : ℕ) : (AP3 dt).succ m' = nextP3.getD m' [] := rfl

theorem hnextP3 (dt : ℝ) : ∀ m' < (AP3 dt).numModes, ∀ t ∈ (AP3 dt).succ m', t < (AP3 dt).numModes := by
  intro m' hm' t ht
  rw [AP3_numModes] at hm' ⊢
  rw [AP3_succ, nextP3_eq] at ht
  interval_cases m' <;> simp at ht <;> omega

theorem hguardP3 (t : ℕ) (ht : t < 3) : (hostGuard vsP 3 Side.L (mLP t)).fv ⊆ range Lv := by
  refine hostGuard_fv_L vsP (mLP t) ?_
  interval_cases t <;> simp [mLP, rover3_M1_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]

theorem hgrdP3 (dt : ℝ) : ∀ t < (AP3 dt).numModes, ((AP3 dt).guard t).fv ⊆ range Lv := by
  intro t ht
  rw [AP3_numModes] at ht
  rw [AP3_guard dt t ht]
  exact hguardP3 t ht

theorem hwinP3 (dt : ℝ) : ∀ t < (AP3 dt).numModes,
    Program.vars ((AP3 dt).window t) ⊆ {((Side.Aux, 1) : Var 3)} ∪ range Lv := by
  intro t ht
  rw [AP3_numModes] at ht
  rw [AP3_window dt t ht]
  exact vars_windowSegL_sub (fLP3 t) domLP3 1 dt 2 (hfLP3 t ht) hdomLP3

/-! ## Freshness of `u_L` -/

theorem hulBkP3 : ulP3 ∉ (mvValid mvP3 GrP3.modes.length).fv := fun h => by
  have := mvValid_fv_sub mvP3 GrP3.modes.length h
  exact absurd (Set.mem_singleton_iff.mp this) (by decide)

theorem hulGP3 (dt : ℝ) : ∀ t, ulP3 ∉ ((AP3 dt).guard t).fv := by
  intro t h
  by_cases ht : t < 3
  · exact aux_notin_range_Lv 2 (hgrdP3 dt t ht h)
  · have : (AP3 dt).guard t = Formula.tt := by
      unfold LeftAut.guard AP3 guardsP3
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem hframesUlP3 (dt : ℝ) : ∀ t, FramesMv ((AP3 dt).window t) ulP3 := by
  intro t
  by_cases ht : t < 3
  · rw [AP3_window dt t ht]
    refine framesMv_window (leftBlock (fLP3 t)) domLP3 tgP3 dt 2 ulP3 (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLP3 t) _ h
    exact aux_ne_Lv 2 i hi
  · have : (AP3 dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window AP3
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulRP3 : ulP3 ∉ (rightAutomatonBody GrP3 mvP3).bv :=
  notMem_bv_rightAutomatonBody GrP3 mvP3 ulP3 (by decide) (aux_notin_range_Rv 2) httP3 hRvP3

/-! ## The handoff: nested constant offsets, in-kernel -/

theorem handoffP3 (dt : ℝ) : ∀ m' < (AP3 dt).numModes, ∀ t ∈ (AP3 dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat envP3 ω → Formula.sat ((AP3 dt).guard t) ω → Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _ _
  rw [AP3_numModes] at hm'
  rw [AP3_succ, nextP3_eq] at ht
  have hm3 : m' < 3 := hm'
  interval_cases m' <;> simp at ht <;> rcases ht with rfl | rfl <;>
    · rw [sat_FRow _ (by norm_num)] at hF ⊢
      simp only [cRow] at hF ⊢
      norm_num at hF ⊢
      linarith

/-! ## The per-mode steps -/

theorem hstepMP3 (dt : ℝ) (hdt : 0 ≤ dt) : ∀ t < (AP3 dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envP3) (mvValid mvP3 GrP3.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 3)) ((AP3 dt).window t)
      (Program.star (rightAutomatonBody GrP3 mvP3))
      (Formula.and (Formula.and (FRow t) envP3) (mvValid mvP3 GrP3.modes.length))) σ := by
  intro t ht
  rw [AP3_numModes] at ht
  rw [AP3_window dt t ht]
  exact hstepMode_multiF GrP3 mvP3 (FRow t) envP3 _ (aux_notin_FRow 0 t) hmvenvP3 hfreshP3
    httP3 hltP3
    (by
      refine framesMv_window (leftBlock (fLP3 t)) domLP3 tgP3 dt 2 mvP3 (by decide) ?_
      intro h
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLP3 t) _ h
      exact aux_ne_Lv 0 i hi)
    (HmultiRow t ht dt hdt)

/-! ## The composed theorem -/

/-- **`rover3_M1`, Theorem 3 at the DECLARED mode-dependent invariant** (padded to
`n = 3` for the left mode variable). The left program is the left automaton over the
file's `next` lists, the loop invariant `⋀_m (u_L = m → row_m)` with `row_Drive = px_L ≤
px_R + 0.5`, `row_Drift = … + 1.0`, `row_Stop = … + 2.0`, plus the chain's bookkeeping.
Composed from the per-mode catch-up steps and the in-kernel handoffs. Z3-free. -/
theorem rover3_M1_modeKeyed (dt : ℝ) (hdt : 0 ≤ dt) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AP3 dt) ulP3)
      (rightAutomatonBody GrP3 mvP3)
      (psiK ulP3 ϕRow (AP3 dt).numModes domLP3 domRP3
        (mvValidR mvP3 GrP3.modes.length))) := by
  refine theorem3_modeKeyed (AP3 dt) ulP3 GrP3 mvP3 FRow ϕRow domLP3 domRP3
    (mvValid mvP3 GrP3.modes.length) (mvValidR mvP3 GrP3.modes.length)
    encode_ϕRow (encode_mvValidR _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (AP3 dt) GrP3 0 1 2 (by decide) (by decide) (hwinP3 dt) (hgrdP3 dt)
      (hnextP3 dt) httP3 hRvP3
  · exact hstep_modeKeyed (AP3 dt) ulP3 (rightAutomatonBody GrP3 mvP3) FRow envP3
      (mvValid mvP3 GrP3.modes.length) (aux_notin_FRow 2) hulenvP3 hulBkP3 (hulGP3 dt)
      (hframesUlP3 dt) hulRP3 (hnextP3 dt) (hstepMP3 dt hdt) (handoffP3 dt)
  · exact hddF_modeKeyed (AP3 dt) GrP3 0 1 2 (by decide) (by decide) ϕRow domLP3 domRP3
      (mvValidR mvP3 GrP3.modes.length) (hwinP3 dt) (hgrdP3 dt) (hnextP3 dt) httP3 hRvP3
      (fun m _ => canonInvM_varsL (gRow m) [] (fun g' hg' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl; exact hgRow m))
      (fun m _ => canonInvM_varsR (gRow m) []) hdomLP3 hdomRP3 rfl
      (fun v hv => Or.inl (mvValid_fv_sub mvP3 GrP3.modes.length hv))

end Rover3M1Handoff
end RelCertifier
