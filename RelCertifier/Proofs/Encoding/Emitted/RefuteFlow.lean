/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Refutations, part 4: kind B (a component pushed out by the left flow), both forms

At the witness `σ` component `k` of the entered row is `≥ 0`, its left Lie derivative along the
entered mode's field is `> 0`, and the witness (after the switch and the clock reset) is in the
INTERIOR of the left evolve domain (every atom strict, `strictQ`). The left run is the switch
followed by a flow of some short positive duration `t ≤ dt` (`exit_run`, `Emitted/RefuteExit`):
the component is `> 0` at its end `ν`. The bi-state is `(σ, σ')`, `σ'` the right copy carrying
`ν`'s left values (the antecedent reads only right coordinates and the right mode variable there,
`namesOK` and `cutsOK` decided in the kernel), so the right run starts from the left values the
post-condition reads; right rigidity (`rigid_star`) keeps the component `> 0` along every right
run, and the post-condition fails.

The window form (`windowClaim`, one declared row) has no left mode variable: the left picks the
window `m` whose guard holds at `σ`; the same argument applies to the common row.
-/
import RelCertifier.Proofs.Encoding.Emitted.Refute
import RelCertifier.Proofs.Encoding.Emitted.RefuteExit
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.WindowGrowth

set_option autoImplicit false

namespace RelCertifier

open DL Set Filter Topology

variable {n : ℕ}

/-! ## Strict interior of a lowered formula at a rational state -/

/-- Every atom of the formula holds strictly at the rational state (an open condition). -/
def IForm.strictQ (s : Var n → ℚ) : IForm n → Bool
  | .tt => true
  | .cmp .lt a b | .cmp .le a b => decide (a.evalQ s < b.evalQ s)
  | .cmp .gt a b | .cmp .ge a b => decide (a.evalQ s > b.evalQ s)
  | .cmp .ne a b => decide (a.evalQ s ≠ b.evalQ s)
  | .cmp .eq _ _ => false
  | .and x y => x.strictQ s && y.strictQ s
  | .neg _ => false

theorem term_continuous (t : Term (Var n)) : Continuous (fun x : State (Var n) => Term.eval t x) :=
  (term_contDiff t).continuous

theorem IForm.strictQ_nhds (s : Var n → ℚ) (f : IForm n) (h : f.strictQ s = true) :
    {x | Formula.sat f.toHost x} ∈ 𝓝 (castQ s) := by
  induction f with
  | tt => simp [IForm.toHost, Formula.sat]
  | cmp op a b =>
      have ha := term_continuous a.toHost
      have hb := term_continuous b.toHost
      have hva := ITerm.evalQ_toHost s a
      have hvb := ITerm.evalQ_toHost s b
      cases op <;> simp only [IForm.strictQ, decide_eq_true_eq, Bool.false_eq_true] at h
      · -- ne
        refine Filter.mem_of_superset ((isOpen_ne_fun ha hb).mem_nhds ?_) (fun x hx => hx)
        simp only [mem_setOf_eq, hva, hvb]; exact_mod_cast h
      all_goals
        first
        | refine Filter.mem_of_superset ((isOpen_lt ha hb).mem_nhds ?_) (fun x hx => ?_)
          · simp only [mem_setOf_eq, hva, hvb]; exact_mod_cast h
          · simp only [mem_setOf_eq, IForm.toHost, Formula.sat, CompOp.interp] at hx ⊢
            first | exact hx | exact hx.le
        | refine Filter.mem_of_superset ((isOpen_lt hb ha).mem_nhds ?_) (fun x hx => ?_)
          · simp only [mem_setOf_eq, hva, hvb]; exact_mod_cast h
          · simp only [mem_setOf_eq, IForm.toHost, Formula.sat, CompOp.interp] at hx ⊢
            first | exact hx | exact hx.le
  | neg f _ => simp [IForm.strictQ] at h
  | and x y ihx ihy =>
      simp only [IForm.strictQ, Bool.and_eq_true] at h
      exact Filter.mem_of_superset (Filter.inter_mem (ihx h.1) (ihy h.2))
        (fun z hz => ⟨hz.1, hz.2⟩)

/-- An optional lowered formula is strictly satisfied (a failed lowering reads as `⊤`). -/
def strictOpt (s : Var n → ℚ) (o : Option (IForm n)) : Bool :=
  match o with
  | some f => f.strictQ s
  | none => true

theorem strictOpt_nhds (s : Var n → ℚ) (o : Option (IForm n)) (h : strictOpt s o = true) :
    {x | Formula.sat ((o.map IForm.toHost).getD Formula.tt) x} ∈ 𝓝 (castQ s) := by
  rcases o with _ | f
  · simp [Formula.sat]
  · simpa using IForm.strictQ_nhds s f h

/-! ## Lie derivatives along the clocked left block -/

theorem lie_clk (tg : Var n) (sys : ODESystem (Var n)) (h : State (Var n) → ℝ)
    (x : State (Var n)) :
    Lie (DLCalTiming.clk tg sys) h x = Lie sys h x + fderiv ℝ h x (Pi.single tg 1) * 1 := by
  simp [Lie, DLCalTiming.clk, List.map_append, List.sum_append, Term.eval]

theorem tderiv_eval_notMem (t : Term (Var n)) (v : Var n) (hv : v ∉ t.fv) (x : State (Var n)) :
    Term.eval (tderiv t v) x = 0 := by
  induction t with
  | var y =>
      have : y ≠ v := fun h => hv (by simp [Term.fv, h])
      simp [tderiv, this, Term.eval]
  | const c => simp [tderiv, Term.eval]
  | binop op a b iha ihb =>
      have ha : v ∉ a.fv := fun h => hv (by simp [Term.fv, h])
      have hb : v ∉ b.fv := fun h => hv (by simp [Term.fv, h])
      cases op <;> simp [tderiv, Term.eval, AOp.interp, iha ha, ihb hb]

theorem lie_leftBlock (fL : Fin n → Term (Var n)) (h : State (Var n) → ℝ) (x : State (Var n)) :
    Lie (leftBlock fL) h x = Lie (jointSys fL (fun _ => Term.const 0) (Term.const 1)) h x := by
  unfold Lie
  rw [jointSys_split, List.map_append, List.sum_append]
  have h0 : ((rightBlock (fun _ => Term.const (0:ℝ)) (Term.const 1) : ODESystem (Var n)).map
      (fun p => fderiv ℝ h x (Pi.single p.1 1) * Term.eval p.2 x)).sum = 0 := by
    unfold rightBlock
    rw [List.map_map]
    refine List.sum_eq_zero (fun a ha => ?_)
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    simp [Term.eval, AOp.interp]
  rw [h0, add_zero]

theorem leftBlock_wf (fL : Fin n → Term (Var n)) : (leftBlock fL).WellFormed := by
  have h := jointSys_wellFormed fL (fun _ => Term.const 0) (Term.const 1)
  unfold ODESystem.WellFormed at h ⊢
  rw [jointSys_split, List.map_append] at h
  exact (List.nodup_append.mp h).1

theorem aux_notMem_leftBlock (fL : Fin n → Term (Var n)) (i : Fin n) :
    ((Side.Aux, i) : Var n) ∉ (leftBlock fL).bound := by
  intro h
  obtain ⟨j, hj⟩ := leftBlock_bound_sub fL _ h
  simp [Lv] at hj

theorem R_notMem_leftBlock (fL : Fin n → Term (Var n)) (i : Fin n) :
    ((Side.R, i) : Var n) ∉ (leftBlock fL).bound := by
  intro h
  obtain ⟨j, hj⟩ := leftBlock_bound_sub fL _ h
  simp [Lv] at hj

/-- **The clocked left segment pushes a component out.** From `μ` (before the clock reset), when
the reset state is interior to the domain, the component `G` is `≥ 0` there and its left Lie
derivative is `> 0`, a run of `clockedSeg` of some positive duration `≤ dt` ends with `G > 0`,
every coordinate outside the left block and the clock unchanged. -/
theorem clocked_exit (fL : Fin n → Term (Var n)) (dom : Formula (Var n)) (b : Fin n) (dt : ℝ)
    (hdt : 0 < dt) (μ : State (Var n))
    (hdom : {x | Formula.sat dom x} ∈ 𝓝 (Function.update μ (Side.Aux, b) 0))
    (G : Term (Var n)) (hGtg : ((Side.Aux, b) : Var n) ∉ G.fv)
    (hG0 : 0 ≤ Term.eval G (Function.update μ (Side.Aux, b) 0))
    (hlie : 0 < Term.eval (lieDeriv G fL (fun _ => Term.const 0) (Term.const 1))
      (Function.update μ (Side.Aux, b) 0)) :
    ∃ ν, Program.sem (clockedSeg (leftBlock fL) dom ((Side.Aux, b) : Var n) dt) μ ν ∧
      0 < Term.eval G ν ∧
      ∀ x, x ∉ (leftBlock fL).bound → x ≠ ((Side.Aux, b) : Var n) → ν x = μ x := by
  set tg : Var n := (Side.Aux, b) with htg
  set μ0 := Function.update μ tg 0 with hμ0
  have hwf := clk_wellFormed tg (leftBlock fL) (leftBlock_wf fL) (aux_notMem_leftBlock fL b)
  have hLie : 0 < Lie (DLCalTiming.clk tg (leftBlock fL)) (fun x => Term.eval G x) μ0 := by
    rw [lie_clk, tderiv_fderiv, tderiv_eval_notMem G tg hGtg, lie_leftBlock, ← lieDeriv_correct]
    simpa using hlie
  obtain ⟨t, htpos, htdt, Φ, hΦ0, hcurve, hdomΦ, hGpos⟩ :=
    exit_run hwf hdom (term_differentiable G) hG0 hLie hdt
  -- the clock reads the elapsed time; every other unbound coordinate is frozen
  have hclk : ∀ y, odeField (DLCalTiming.clk tg (leftBlock fL)) y tg = 1 := by
    intro y
    have hmem : (tg, Term.const (1:ℝ)) ∈ DLCalTiming.clk tg (leftBlock fL) := by
      simp [DLCalTiming.clk]
    have hb : tg ∈ (DLCalTiming.clk tg (leftBlock fL)).bound := List.mem_map_of_mem hmem
    simp only [odeField, if_pos hb, ODESystem.rhs_eq_of_mem hwf hmem, Term.eval]
  have hfree : ∀ x, x ∉ (leftBlock fL).bound → x ≠ tg → ∀ y,
      odeField (DLCalTiming.clk tg (leftBlock fL)) y x = 0 := by
    intro x hx hxt y
    have hnb : x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound := by
      simp only [DLCalTiming.clk, ODESystem.bound, List.map_append, List.mem_append,
        List.map_cons, List.map_nil, List.mem_singleton, not_or]
      exact ⟨hx, hxt⟩
    simp only [odeField, if_neg hnb]
  have htI : t ∈ Icc (0:ℝ) t := ⟨htpos.le, le_rfl⟩
  refine ⟨Φ t, ⟨μ0, ?_, Φ t, ?_, rfl, ?_⟩, hGpos, fun x hx hxt => ?_⟩
  · rw [sem_assign]
    exact ⟨by simp [μ0, Term.eval], fun y hy => by simp [μ0, Function.update_of_ne hy]⟩
  · rw [← hΦ0]
    exact sem_of_integralCurveOn _ _ hwf htpos.le hcurve hdomΦ
  · rw [sat_clkGuard, curve_coord hcurve tg 1 hclk t htI, hΦ0]
    simpa [μ0] using htdt
  · rw [curve_coord hcurve x 0 (hfree x hx hxt) t htI, hΦ0]
    simp [μ0, Function.update_of_ne hxt]

namespace Emitted

open DLRel Parse Run Oracle Refute

theorem bigChoice_sem_mem {ps : List (Program (Var n))} {q : Program (Var n)} (hq : q ∈ ps)
    {σ ν : State (Var n)} (h : Program.sem q σ ν) : Program.sem (bigChoice ps) σ ν := by
  induction ps with
  | nil => exact absurd hq (by simp)
  | cons x xs ih =>
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl h
      · exact Or.inr (ih hq)

/-! ## The claim, used once at a general bi-state -/

theorem t3_elim' {L R : Program (Var n)} {ψ : RFormula (Var n)}
    (h : RFormula.rvalid (theorem3Form L R ψ)) (ωL ωR : State (Var n))
    (hpre : RFormula.sat ψ (ωL, ωR)) {νL : State (Var n)}
    (hL : Program.sem (Program.star L) ωL νL) :
    ∃ μR, Program.sem (Program.star R) ωR μR ∧ RFormula.sat ψ (νL, μR) := by
  have h1 := (RFormula_sat_imp _ _ _).mp (h (ωL, ωR)) hpre
  have h2 : RFormula.sat (RFormula.rdiamond
      (RProgram.biprog (Program.test Formula.tt) (Program.star R)) ψ) (νL, ωR) :=
    h1 (νL, ωR) ⟨hL, rfl, trivial⟩
  by_contra hno
  push_neg at hno
  apply h2
  rintro ⟨x, y⟩ ⟨⟨rfl, -⟩, hy⟩ hψ
  exact hno y hy hψ

/-! ## The witness facts of kind B -/

section Data

variable (p : PProblem) (n : ℕ)

/-- Component `k` of row `row` and the left field of mode `mL`: the component is `≥ 0` and its
left Lie derivative `> 0` at the rational state. -/
def exitQ (row : PForm) (mL : PMode) (k : ℕ) (s : Var n → ℚ) : Bool :=
  match ((Oracle.invComponents (vars p) n row).bind (·[k]?)), dynOf (vars p) n Side.L mL with
  | some g, some f => decide (0 ≤ g.evalQ s) && decide (0 < (Bridge.ownLie Side.L g f).evalQ s)
  | _, _ => false

/-- The kind-B facts of the mode-keyed form, at the reset state (after `c := m`, `b := 0`): the
left envelope strictly, the component's sign and its left Lie derivative's. -/
def bQ (a b c : Fin n) (w : RefWitE) : Bool :=
  let s' := witPost n b c w (witState n a c w)
  strictOpt s' (lowerF (vars p) n Side.L (mLof p 0).evolve) &&
  exitQ p n (rowOf p w.m) (mLof p w.m) w.k s'

/-- The antecedent facts of the window form (no left mode variable; `c := b`, the clock, whose
stored value the window resets): the window and right mode in range; at the witness the common
row, both envelopes, the right mode's guard and kept atoms, the window's guard. -/
def preOKW (cX : EvolStrengtheningX) (a b : Fin n) (w : RefWitE) : Bool :=
  let s := witState n a b w
  decide (w.m < nL p) && decide (w.q0 < nR p) &&
  compsQ p n (rowOf p 0) s &&
  optQ s (lowerF (vars p) n Side.L (mLof p 0).evolve) &&
  optQ s (lowerF (vars p) n Side.R (mRof p 0).evolve) &&
  optQ s (lowerF (vars p) n Side.R (mRof p w.q0).guard) &&
  (cutAtomsOfX cX.R (mRof p w.q0).name).all (fun x => optQ s (lowerF (vars p) n Side.R x.atom)) &&
  optQ s (lowerF (vars p) n Side.L (mLof p w.m).guard)

/-- The kind-B facts of the window form, at the reset state `b := 0`. -/
def bQW (a b : Fin n) (w : RefWitE) : Bool :=
  let s' := Function.update (witState n a b w) (Side.Aux, b) 0
  strictOpt s' (lowerF (vars p) n Side.L (mLof p 0).evolve) &&
  exitQ p n (rowOf p w.m) (mLof p w.m) w.k s'

end Data

/-! ## Shared lemmas -/

theorem exitQ_sound {p : PProblem} {row : PForm} {mL : PMode} {k : ℕ} {s : Var n → ℚ}
    (h : exitQ p n row mL k s = true) :
    ∃ cs gI, Oracle.invComponents (vars p) n row = some cs ∧ cs[k]? = some gI ∧
      0 ≤ Term.eval gI.toHost (castQ s) ∧
      0 < Term.eval (lieDeriv gI.toHost (hostDyn (vars p) n Side.L mL) (fun _ => Term.const 0)
        (Term.const 1)) (castQ s) := by
  unfold exitQ at h
  rcases hcs : Oracle.invComponents (vars p) n row with _ | cs
  · simp [hcs] at h
  rcases hg : cs[k]? with _ | gI
  · simp [hcs, hg] at h
  rcases hf : dynOf (vars p) n Side.L mL with _ | f
  · simp [hcs, hg, hf] at h
  simp only [hcs, hg, hf, Option.bind_some, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨cs, gI, rfl, hg, ?_, ?_⟩
  · rw [ITerm.evalQ_toHost]; exact_mod_cast h.1
  · have hfL : hostDyn (vars p) n Side.L mL = fun j => (f j).toHost := by
      funext j; simp [hostDyn, hf]
    have hT : (Bridge.ownLie Side.L gI f).toHost = lieDeriv gI.toHost (hostDyn (vars p) n Side.L mL)
        (fun _ => Term.const 0) (Term.const 1) := by
      rw [hfL]; simp [Bridge.ownLie, ilieDeriv_toHost, ITerm.toHost]
    rw [← hT, ITerm.evalQ_toHost]; exact_mod_cast h.2

theorem rigid_of_groups {p : PProblem} {cX : EvolStrengtheningX} {w : RefWitE}
    (hk : w.kind ≠ "C") (hv : RefVerdicts p n cX w) :
    ∃ cs gI, Oracle.invComponents (vars p) n (rowOf p w.m) = some cs ∧ cs[w.k]? = some gI ∧
      ∀ q < nR p, ∀ x, Formula.sat (domR p n) x →
        Term.eval (lieDeriv (Term.binop .sub (Term.const 0) gI.toHost) (fun _ => Term.const 0)
          (fR p n q) (Term.const 1)) x ≤ 0 := by
  obtain ⟨gs, hgs, hok⟩ := hv
  have hk' : (w.kind == "C") = false := by simpa using hk
  simp only [refGroups, hk', Bool.false_eq_true, if_false, rigidGroups, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at hgs
  obtain ⟨cs, hcs, gI, hgI, hgs⟩ := hgs
  refine ⟨cs, gI, hcs, hgI, fun q hq x hx => ?_⟩
  obtain ⟨y, hy, hyq⟩ := mapM_range hgs q hq
  obtain ⟨Q, hQ, rfl⟩ := Option.map_eq_some_iff.mp hyq
  obtain ⟨Q', hQ', hz⟩ := hok _ hy
  rw [List.mem_singleton] at hQ'
  subst hQ'
  exact rigid_sound hQ hz x hx

/-- The right copy carrying the left end state's left values. -/
noncomputable def withLeft (ν σ : State (Var n)) : State (Var n) :=
  fun v => if v.1 = Side.L then ν v else σ v

theorem mixS_withLeft (ν σ : State (Var n)) : mixS σ (withLeft ν σ) = σ := by
  funext v
  rcases v with ⟨s, i⟩
  cases s <;> simp [mixS, withLeft]

theorem cuts_fv_of {p : PProblem} {cX : EvolStrengtheningX} (hc : cutsOK p n cX = true) (q : ℕ) :
    (cuts p n cX q).fv ⊆ range Rv :=
  cutF_fv_sub (cutPairsX_fvF_R (atomsWF_R_any hc q))

/-! ## The unclocked window claim (the pre-W3 `windowClaim`), and its transfer -/

/-- The one-row claim over the UNCLOCKED guarded right automaton (`rightAutomatonBody`; mode
variable `(Aux, a)`, left clock `(Aux, b)`): the pre-W3 `windowClaim`. The clocked claim
implies it (`windowClaim_to_unclocked`). -/
def windowClaimU (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
    (reg : Formula (Var n)) (a b : Fin n) (dt : ℝ) : Prop :=
  RFormula.rvalid (theorem3Form
    (bigChoice (leftProgsOf b dt (domL p n) (nL p) (guardL p n) (fL p n)))
    (rightAutomatonBody (grOf p n (prunedOf cov)) ((Side.Aux, a) : Var n))
    (RFormula.and (RFormula.and (canonInvM (g p n 0) (gs p n 0)) (envLR (domL p n) (domR p n)))
      (mvRegionR ((Side.Aux, a) : Var n) (regionG (guardR p n) (cutsR p n cX reg))
        (grOf p n (prunedOf cov)).modes.length)))

/-- **The clocked claim implies the unclocked one** (window form); mirror of
`keyedClaim_to_unclocked`. Only `d ≠ a` is needed. -/
theorem windowClaim_to_unclocked {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE}
    (hnm : namesOK p = true) (hcu : cutsOK p n cX = true) {reg : Formula (Var n)}
    (hregR : reg.fv ⊆ range Rv) {a b d : Fin n} (hda : d ≠ a) {dt : ℝ}
    (h : windowClaim p n cX cov reg a b d dt) : windowClaimU p n cX cov reg a b dt := by
  unfold windowClaim at h
  unfold windowClaimU
  refine t3_right_mono h ?_
  intro ωL ν μ hμ hψ
  obtain ⟨μ', hμ', hR, hA⟩ := erase_right_clock hnm hda hμ
  refine ⟨μ', hμ', ?_⟩
  obtain ⟨⟨hrow, hdL, hdR⟩, hB⟩ := hψ
  have hdR' : Formula.sat (domR p n) μ := hdR
  refine ⟨⟨?_, hdL, (sat_R_congr (domR_fv hnm) hR).mpr hdR'⟩, ?_⟩
  · change RFormula.sat (canonInvM (g p n 0) (gs p n 0)) _ at hrow ⊢
    rw [sat_canonInvM_bi] at hrow ⊢
    change Formula.sat (FRow p n 0) _ at hrow ⊢
    exact (sat_mixS_congr FRow_fv hR).mpr hrow
  · change Formula.sat (mvRegion _ _ _) μ at hB
    show Formula.sat (mvRegion _ _ _) μ'
    rw [sat_mvRegion] at hB ⊢
    obtain ⟨q, hq, hmv, hreg⟩ := hB
    exact ⟨q, hq, by rw [hA]; exact hmv,
      (sat_R_congr (gregion_fv_of hnm hcu hregR q) hR).mpr hreg⟩

/-! ## Kind B, mode-keyed -/

section KeyedB

variable {p : PProblem} {cX : EvolStrengtheningX} {a b c : Fin n} {w : RefWitE}

/-- The left run of the mode-keyed form: the switch `u → m`, then any clocked segment of `m`. -/
theorem left_run_seg (hpf : PreFacts p cX a b c w) (hca : c ≠ a) (dt : ℝ) {ν : State (Var n)}
    (hseg : Program.sem (clockedSeg (leftBlock (fL p n w.m)) (domL p n) ((Side.Aux, b) : Var n) dt)
      (σS a c w) ν) :
    Program.sem (Program.star (leftAutomatonBody (leftAutOf p n ((Side.Aux, b) : Var n) dt)
      ((Side.Aux, c) : Var n))) (σW a c w) ν := by
  have hmL : w.m < nL p := nextL_lt w.u hpf.hu w.m hpf.hm
  refine Relation.ReflTransGen.single ?_
  refine bigChoiceP_sem_of_mem (List.mem_map.mpr ⟨w.u, List.mem_range.mpr ?_, rfl⟩) ?_
  · rw [leftAutOf_numModes]; exact hpf.hu
  refine ⟨σW a c w, ⟨rfl, sat_modeIs.mpr (σW_aux_c hca)⟩, ?_⟩
  refine bigChoiceP_sem_of_mem (List.mem_map.mpr ⟨w.m, ?_, rfl⟩) ?_
  · rw [leftAutOf_succ]; exact hpf.hm
  refine ⟨σW a c w, ⟨rfl, ?_⟩, σS a c w, ?_, ?_⟩
  · have hg := leftAutOf_guard (p := p) (n := n) ((Side.Aux, b) : Var n) dt hmL
    rw [hg]; exact hpf.hguardL
  · rw [sem_assign, σS_eq]
    refine ⟨by simp [Term.eval], fun y hy => ?_⟩
    simp [Function.update_of_ne hy]
  · rw [LeftAut.window.eq_def]
    have hw : (leftAutOf p n ((Side.Aux, b) : Var n) dt).windows.getD w.m
        (Program.test (Formula.neg Formula.tt)) = windowOf p n ((Side.Aux, b) : Var n) dt w.m := by
      have := leftAutOf_window (p := p) (n := n) ((Side.Aux, b) : Var n) dt hmL
      simpa [LeftAut.window] using this
    rw [hw]
    unfold windowOf gwindowSeg windowSeg
    simp only [List.replicate_one, bigSeq]
    exact ⟨σS a c w, ⟨rfl, hpf.hguardL'⟩, ν, hseg, rfl, trivial⟩

/-- The antecedent at `(σ, σ')`, `σ'` agreeing with `σ` on the right coordinates and the right
mode variable. -/
theorem pre_sat_bi (hpf : PreFacts p cX a b c w) (hca : c ≠ a) (hnm : namesOK p = true)
    (hcu : cutsOK p n cX = true) (pr : String → String → Bool) (dt : ℝ) (σ' : State (Var n))
    (hR : ∀ i, σ' (Side.R, i) = σW a c w (Side.R, i))
    (ha : σ' (Side.Aux, a) = σW a c w (Side.Aux, a)) (hmix : mixS (σW a c w) σ' = σW a c w) :
    RFormula.sat (psiKOf p cX pr a b c dt) (σW a c w, σ') := by
  unfold psiKOf
  rw [sat_psiK_bi]
  refine ⟨?_, ⟨hpf.hdomL, (sat_R_congr (domR_fv hnm) hR).mpr hpf.hdomR⟩, ?_, ?_⟩
  · rw [sat_modeKeyedR_bi]
    intro m' _ hul
    rw [σW_aux_c hca] at hul
    have hm' : m' = w.u := by exact_mod_cast hul.symm
    subst hm'
    show RFormula.sat (canonInvM (g p n w.u) (gs p n w.u)) _
    rw [sat_canonInvM_bi, hmix]
    exact hpf.hrow
  · show Formula.sat (mvRegion _ _ _) σ'
    rw [sat_mvRegion]
    exact ⟨w.q0, by rw [grOf_len]; exact hpf.hq0, by rw [ha]; exact σW_aux_a,
      (sat_R_congr (guardR_fv hnm _) hR).mpr hpf.hguardR,
      (sat_R_congr (cuts_fv_of hcu _) hR).mpr hpf.hcuts, trivial⟩
  · show Formula.sat (mvValid _ _) (σW a c w)
    rw [sat_mvValid]
    exact ⟨w.u, by rw [leftAutOf_numModes]; exact hpf.hu, σW_aux_c hca⟩

/-- **Kind B, mode-keyed.** -/
theorem refute_keyed_B (hpre : preOK p n cX a b c w = true) (hb : bQ p n a b c w = true)
    (hk : w.kind ≠ "C") (hv : RefVerdicts p n cX w) (hnm : namesOK p = true)
    (hcu : cutsOK p n cX = true) (hca : c ≠ a) (hcb : c ≠ b) (dt : ℝ) (hdt : 0 < dt)
    (cov : CoverEmitE) : ¬ keyedClaimU p n cX cov Formula.tt a b c dt := by
  intro hclaim
  have hpf := preFacts_of hpre
  simp only [bQ, Bool.and_eq_true] at hb
  obtain ⟨hstrict, hexit⟩ := hb
  obtain ⟨cs, gI, hcs, hgI, hG0, hlie⟩ := exitQ_sound hexit
  obtain ⟨cs', gI', hcs', hgI', hrig⟩ := rigid_of_groups hk hv
  rw [hcs] at hcs'; cases hcs'; rw [hgI] at hgI'; cases hgI'
  set G := gI.toHost with hGdef
  have hmem : G ∈ comps p n w.m := by
    rw [comps_of_some hcs]; exact List.mem_map_of_mem (List.mem_of_getElem? hgI)
  have hGfv := comps_mem_fv hmem
  have hGtg : ((Side.Aux, b) : Var n) ∉ G.fv := fun h => by
    rcases hGfv h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> simp [Lv, Rv] at hi
  have hσP : Function.update (σS a c w) (Side.Aux, b) 0 = σP a b c w := σP_eq.symm
  obtain ⟨ν, hseg, hpos, hfr⟩ := clocked_exit (fL p n w.m) (domL p n) b dt hdt (σS a c w)
    (by rw [hσP]; exact strictOpt_nhds _ _ hstrict) G hGtg (by rw [hσP]; exact hG0)
    (by rw [hσP]; exact hlie)
  have hL := left_run_seg hpf hca dt hseg
  have hνR : ∀ i, ν (Side.R, i) = σW a c w (Side.R, i) := by
    intro i
    rw [hfr _ (R_notMem_leftBlock _ i) (by simp), σS_eq]
    simp [Function.update_apply]
  have hνc : ν (Side.Aux, c) = (w.m : ℝ) := by
    rw [hfr _ (aux_notMem_leftBlock _ c) (by simpa using hcb), σS_eq]
    simp
  set σ' := withLeft ν (σW a c w) with hσ'
  have hpre' := pre_sat_bi hpf hca hnm hcu (prunedOf cov) dt σ'
    (fun i => by simp [σ', withLeft]) (by simp [σ', withLeft]) (mixS_withLeft ν _)
  obtain ⟨μR, hR, hψ⟩ := t3_elim' hclaim (σW a c w) σ' hpre' hL
  -- the entered row at `μR`
  have hmL : w.m < nL p := nextL_lt w.u hpf.hu w.m hpf.hm
  rw [sat_psiK_bi] at hψ
  obtain ⟨hK, -, -, -⟩ := hψ
  rw [sat_modeKeyedR_bi] at hK
  have hrow := hK w.m (by rw [leftAutOf_numModes]; exact hmL) hνc
  change RFormula.sat (canonInvM (g p n w.m) (gs p n w.m)) _ at hrow
  rw [sat_canonInvM_bi] at hrow
  change Formula.sat (FRow p n w.m) _ at hrow
  have heq : EqOn (mixS ν μR) μR (FRow p n w.m).fv := by
    intro v hv
    rcases FRow_fv hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp only [mixS, Lv]
      rw [if_neg (by simp), rightStar_keepsL hR]
      simp [σ', withLeft]
    · simp [mixS, Rv]
  rw [Formula.coincidence _ heq, sat_FRow_iff] at hrow
  -- rigidity from `σ'`, where `G` reads `ν`'s value
  have hmono := rigid_star hGfv hrig hR
  have hσ'ν : Term.eval G σ' = Term.eval G ν := Term.coincidence G (fun v hv => by
    rcases hGfv hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp [σ', withLeft, Lv]
    · simp [σ', withLeft, Rv, hνR])
  linarith [hrow G hmem]

/-- **Kind B, mode-keyed, the clocked claim** (W4): `refute_keyed_B` by contraposition through
`keyedClaim_to_unclocked`; `(Aux, d)` is the right clock. -/
theorem refute_keyed_B_clocked (hpre : preOK p n cX a b c w = true) (hb : bQ p n a b c w = true)
    (hk : w.kind ≠ "C") (hv : RefVerdicts p n cX w) (hnm : namesOK p = true)
    (hcu : cutsOK p n cX = true) (hca : c ≠ a) (hcb : c ≠ b) (d : Fin n) (hda : d ≠ a) (dt : ℝ)
    (hdt : 0 < dt) (cov : CoverEmitE) : ¬ keyedClaim p n cX cov Formula.tt a b c d dt :=
  fun h => refute_keyed_B hpre hb hk hv hnm hcu hca hcb dt hdt cov
    (keyedClaim_to_unclocked hnm hcu (by simp [Formula.fv]) hda h)

end KeyedB

/-! ## Kind B, window form -/

section WindowB

variable {p : PProblem} {cX : EvolStrengtheningX} {a b : Fin n} {w : RefWitE}

/-- **Kind B, window form** (one declared row, `rowsSame`). -/
theorem refute_window_B (hpre : preOKW p n cX a b w = true) (hb : bQW p n a b w = true)
    (hk : w.kind ≠ "C") (hv : RefVerdicts p n cX w) (hsame : rowsSame p = true)
    (hnm : namesOK p = true) (hcu : cutsOK p n cX = true) (hab : a ≠ b) (dt : ℝ) (hdt : 0 < dt)
    (cov : CoverEmitE) : ¬ windowClaimU p n cX cov Formula.tt a b dt := by
  intro hclaim
  set s := witState n a b w with hs
  set σ := castQ s with hσ
  simp only [preOKW, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hpre
  obtain ⟨⟨⟨⟨⟨⟨⟨hm, hq0⟩, hrow0⟩, hdL⟩, hdR⟩, hgR⟩, hcut⟩, hgL⟩ := hpre
  have hrow0' : Formula.sat (FRow p n 0) σ := FRow_of_compsQ hrow0
  have hdL' : Formula.sat (domL p n) σ := (optQ_iff _ _).mpr hdL
  have hdR' : Formula.sat (domR p n) σ := (optQ_iff _ _).mpr hdR
  have hgR' : Formula.sat (guardR p n w.q0) σ := (optQ_iff _ _).mpr hgR
  have hgL' : Formula.sat (guardL p n w.m) σ := (optQ_iff _ _).mpr hgL
  have hcut' : Formula.sat (cuts p n cX w.q0) σ := by
    rw [cuts, sat_cutF]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (optQ_iff _ _).mpr (hcut y hy)
  simp only [bQW, Bool.and_eq_true] at hb
  obtain ⟨hstrict, hexit⟩ := hb
  obtain ⟨cs, gI, hcs, hgI, hG0, hlie⟩ := exitQ_sound hexit
  obtain ⟨cs', gI', hcs', hgI', hrig⟩ := rigid_of_groups hk hv
  rw [hcs] at hcs'; cases hcs'; rw [hgI] at hgI'; cases hgI'
  set G := gI.toHost with hGdef
  have hmem : G ∈ comps p n w.m := by
    rw [comps_of_some hcs]; exact List.mem_map_of_mem (List.mem_of_getElem? hgI)
  have hGfv := comps_mem_fv hmem
  have hGtg : ((Side.Aux, b) : Var n) ∉ G.fv := fun h => by
    rcases hGfv h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> simp [Lv, Rv] at hi
  have hσ0 : Function.update σ (Side.Aux, b) 0 = castQ (Function.update s (Side.Aux, b) 0) := by
    rw [castQ_update, Rat.cast_zero]
  obtain ⟨ν, hseg, hpos, hfr⟩ := clocked_exit (fL p n w.m) (domL p n) b dt hdt σ
    (by rw [hσ0]; exact strictOpt_nhds _ _ hstrict) G hGtg (by rw [hσ0]; exact hG0)
    (by rw [hσ0]; exact hlie)
  -- the left run: the window of `m`
  have hL : Program.sem (Program.star (bigChoice (leftProgsOf b dt (domL p n) (nL p) (guardL p n)
      (fL p n)))) σ ν := by
    refine Relation.ReflTransGen.single (bigChoice_sem_mem (q := gwindowSeg (guardL p n w.m)
      (leftBlock (fL p n w.m)) (domL p n) ((Side.Aux, b) : Var n) dt 1) ?_ ?_)
    · simp only [leftProgsOf, leftDataOf, List.map_map, List.mem_map, List.mem_range]
      exact ⟨w.m, hm, rfl⟩
    · unfold gwindowSeg windowSeg
      simp only [List.replicate_one, bigSeq]
      exact ⟨σ, ⟨rfl, hgL'⟩, ν, hseg, rfl, trivial⟩
  have hνR : ∀ i, ν (Side.R, i) = σ (Side.R, i) :=
    fun i => hfr _ (R_notMem_leftBlock _ i) (by simp)
  set σ' := withLeft ν σ with hσ'
  have hRσ' : ∀ i, σ' (Side.R, i) = σ (Side.R, i) := fun i => by simp [σ', withLeft]
  have hpre' : RFormula.sat (RFormula.and (RFormula.and (canonInvM (g p n 0) (gs p n 0))
      (envLR (domL p n) (domR p n)))
      (mvRegionR ((Side.Aux, a) : Var n) (regionG (guardR p n) (cutsR p n cX Formula.tt))
        (grOf p n (prunedOf cov)).modes.length)) (σ, σ') := by
    refine ⟨⟨?_, hdL', (sat_R_congr (domR_fv hnm) hRσ').mpr hdR'⟩, ?_⟩
    · show RFormula.sat (canonInvM (g p n 0) (gs p n 0)) (σ, σ')
      rw [sat_canonInvM_bi, mixS_withLeft]; exact hrow0'
    · show Formula.sat (mvRegion _ _ _) σ'
      rw [sat_mvRegion]
      refine ⟨w.q0, by rw [grOf_len]; exact hq0, ?_,
        (sat_R_congr (guardR_fv hnm _) hRσ').mpr hgR',
        (sat_R_congr (cuts_fv_of hcu _) hRσ').mpr hcut', trivial⟩
      simp [σ', withLeft, σ, castQ, s, witState]
  obtain ⟨μR, hR, hψ⟩ := t3_elim' hclaim σ σ' hpre' hL
  have hrow : Formula.sat (FRow p n 0) (mixS ν μR) := by
    have := hψ.1.1
    rw [sat_canonInvM_bi] at this
    exact this
  have heq : EqOn (mixS ν μR) μR (FRow p n 0).fv := by
    intro v hv
    rcases FRow_fv hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp only [mixS, Lv]
      rw [if_neg (by simp), rightStar_keepsL hR]
      simp [σ', withLeft]
    · simp [mixS, Rv]
  rw [Formula.coincidence _ heq, ← FRow_same hsame w.m, sat_FRow_iff] at hrow
  have hmono := rigid_star hGfv hrig hR
  have hσ'ν : Term.eval G σ' = Term.eval G ν := Term.coincidence G (fun v hv => by
    rcases hGfv hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp [σ', withLeft, Lv]
    · simp [σ', withLeft, Rv, hνR])
  linarith [hrow G hmem]

/-- **Kind B, window form, the clocked claim** (W4): `refute_window_B` by contraposition
through `windowClaim_to_unclocked`; `(Aux, d)` is the right clock. -/
theorem refute_window_B_clocked (hpre : preOKW p n cX a b w = true) (hb : bQW p n a b w = true)
    (hk : w.kind ≠ "C") (hv : RefVerdicts p n cX w) (hsame : rowsSame p = true)
    (hnm : namesOK p = true) (hcu : cutsOK p n cX = true) (hab : a ≠ b) (d : Fin n) (hda : d ≠ a)
    (dt : ℝ) (hdt : 0 < dt) (cov : CoverEmitE) : ¬ windowClaim p n cX cov Formula.tt a b d dt :=
  fun h => refute_window_B hpre hb hk hv hsame hnm hcu hab dt hdt cov
    (windowClaim_to_unclocked hnm hcu (by simp [Formula.fv]) hda h)

end WindowB

end Emitted
end RelCertifier
