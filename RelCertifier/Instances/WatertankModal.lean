/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S1 GATE — watertank, the multi-mode modal Theorem 3

`rvalid (theorem3Form …)` for a genuinely multi-mode benchmark: three left windows,
the three-mode right automaton with its REAL declared edges, and responses that OPEN
WITH REPOSITIONS where the start mode carries no joint certificate for the window —
the paper's witness, mechanized end to end.

Structure per (window ℓ, start q):
* `(ℓ, q)` joint-certified — response = the single self-edge piece (`k = 1`);
* otherwise — response = STATIC reposition hops along declared edges to a
  joint-certified mode, then the piece there. Static hops are zero-duration runs
  whose domain obligation is exactly the loop invariant's envelope conjunct
  (`static_hop_exists`) — certificate-free.

The loop invariant is the envelope-carrying `phiInvE` (invariant ∧ joint universal
domain ∧ mode-validity). Residuals: the six joint-piece verdicts (`hz3`) and the
envelope-conditioned per-piece existence (`hES`) — S3's target. Axioms: the standard
three + `z3_unsat_sound` where verdicts enter.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChain
import RelCertifier.Proofs.Encoding.CanonicalInv
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.ViabilityWiring
import RelCertifier.Instances.BenchIR

namespace RelCertifier
namespace WatertankModal

open DL DLCalTiming DLRel Parse Set

def vsM : List String := ["x"]
def dummyM : Parse.PMode := ⟨"", [], .tt, .tt, []⟩
def mLW (l : ℕ) : Parse.PMode := watertank_IR.L.modes.getD l dummyM
def mRW (q : ℕ) : Parse.PMode := watertank_IR.R.modes.getD q dummyM

abbrev mvM : Var 2 := (Side.Aux, 0)
abbrev aM : Fin 2 := (1 : Fin 2)
abbrev tgM : Var 2 := (Side.Aux, aM)

/-- Lowered fields and domains (n = 2 pad; coordinate 1 inert). -/
noncomputable def fLW (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsM 2 Side.L (mLW l)
noncomputable def fRW (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vsM 2 Side.R (mRW q)
noncomputable def domLW : Formula (Var 2) := hostEvolve vsM 2 Side.L (mLW 0)
noncomputable def domRW : Formula (Var 2) := hostEvolve vsM 2 Side.R (mRW 0)

/-- The joint universal envelope — the loop invariant's conditioning conjunct. -/
noncomputable def envW : Formula (Var 2) := Formula.and domLW domRW

/-- The invariant term (`L_x − (R_x + 3)`). -/
noncomputable def gW : Term (Var 2) :=
  ((Run.invToG vsM 2 ((watertank_IR.invariants.getD 0 ("", Parse.PForm.tt)).2)).map
    ITerm.toHost).getD (Term.const 0)

/-- Universal evolve: all six mode evolves lower identically (kernel facts). -/
theorem domLW_univ (l : ℕ) (hl : l < 3) : hostEvolve vsM 2 Side.L (mLW l) = domLW := by
  interval_cases l <;> rfl
theorem domRW_univ (q : ℕ) (hq : q < 3) : hostEvolve vsM 2 Side.R (mRW q) = domRW := by
  interval_cases q <;> rfl

/-- The right automaton graph: rightBlock modes over the RIGHT evolve domain (the
mode data must live on `Rv` for the `hd`/`hddF` side splits; the joint envelope is
carried by the loop invariant, not the mode domain), edges = the declared `next`
lists. -/
noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fRW q) (Term.const 1), dom := domRW, weight := 1 }

def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

noncomputable def GrW : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := [edgeW 0 1, edgeW 0 0, edgeW 1 2, edgeW 1 1, edgeW 2 1, edgeW 2 2] }

/-! ## Side-splits (kernel facts via the lowering pipelines) -/

theorem fLW_pipe (l : ℕ) (i : Fin 2) : fLW l i =
    (((some (mLW l)).bind (Run.dynOf vsM 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fRW_pipe (q : ℕ) (i : Fin 2) : fRW q i =
    (((some (mRW q)).bind (Run.dynOf vsM 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domLW_pipe : domLW =
    (((some (mLW 0)).bind (fun m => Run.lowerF vsM 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domRW_pipe : domRW =
    (((some (mRW 0)).bind (fun m => Run.lowerF vsM 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfLW (l : ℕ) (hl : l < 3) : ∀ i, ((fLW l) i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vsM) (some (mLW l))
    (by interval_cases l <;> simp [mLW, watertank_IR, Parse.PExpr.namesFree]) i x
    (fLW_pipe l i ▸ hx))

theorem hfRW (q : ℕ) (hq : q < 3) : ∀ i, ((fRW q) i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vsM) (some (mRW q))
    (by interval_cases q <;> simp [mRW, watertank_IR, Parse.PExpr.namesFree]) i x
    (fRW_pipe q i ▸ hx))

theorem hdomLW : domLW.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vsM) (some (mLW 0))
    (by simp [mLW, watertank_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domLW_pipe ▸ hx))

theorem hdomRW : domRW.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vsM) (some (mRW 0))
    (by simp [mRW, watertank_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domRW_pipe ▸ hx))

theorem hgW : gW.fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem hmvgW : mvM ∉ gW.fv := fun h => by
  rcases hgW h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem htggW : tgM ∉ gW.fv := fun h => by
  rcases hgW h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
theorem hmvenvW : mvM ∉ envW.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLW h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRW h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))
theorem htgenvW : tgM ∉ envW.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLW h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRW h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## Graph shape facts -/

theorem GrW_modeAt {q : ℕ} {m : RMode (Var 2)} (hm : GrW.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrW] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrW] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrW] using hm.symm⟩
  | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, GrW])

theorem httW : ∀ q, ∀ e ∈ GrW.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ GrW.edges := List.mem_of_mem_filter he
  simp only [GrW, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem hltW : ∀ q, ∀ e ∈ GrW.edgesFrom q, e.tgt < GrW.modes.length := by
  intro q e he
  have hmem : e ∈ GrW.edges := List.mem_of_mem_filter he
  simp only [GrW, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [GrW, edgeW]

theorem hRvW : ∀ q m, GrW.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  obtain ⟨hq, rfl⟩ := GrW_modeAt hm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRW q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRW q) (Term.const 1) (hfRW q hq) (by simp [Term.fv]) hy
  · exact hdomRW hy

theorem edgeW_from {s t : ℕ} (h : edgeW s t ∈ GrW.edges) : edgeW s t ∈ GrW.edgesFrom s :=
  List.mem_filter.mpr ⟨h, by simp [edgeW]⟩

/-! ## The left window family -/

noncomputable def leftDataW : List ((Fin 2 → Term (Var 2)) × Formula (Var 2) × ℕ) :=
  [(fLW 0, domLW, 1), (fLW 1, domLW, 1), (fLW 2, domLW, 1)]

noncomputable def leftProgsW (dt : ℝ) : List (Program (Var 2)) :=
  leftDataW.map (fun d => windowSeg (leftBlock d.1) d.2.1 tgM dt d.2.2)

theorem hLW : ∀ d ∈ leftDataW, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftDataW, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨hfLW 0 (by norm_num), hdomLW⟩
  · exact ⟨hfLW 1 (by norm_num), hdomLW⟩
  · exact ⟨hfLW 2 (by norm_num), hdomLW⟩

theorem hframesW (dt : ℝ) : ∀ P ∈ leftProgsW dt, FramesMv P mvM := by
  intro P hP
  simp only [leftProgsW, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_window (leftBlock d.1) d.2.1 tgM dt d.2.2 mvM (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.1 _ h
  exact aux_ne_Lv 0 i hi

theorem hfreshW : ∀ q m, GrW.modeAt q = some m →
    mvM ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvW q m hm (vars_ode_sub _ _ (Or.inl hmv)))

/-! ## The residuals: per-pair route verdicts and envelope-conditioned existence -/

/-- The per-pair joint verdict residual: the tool's stratified three-route query family
(`checkSeg`) at the joint pair (left window `l`, right mode `q`), λ = 1, over the joint
universal envelope. Watertank's invariant is single-component, so the tool's per-stratum
domain `strataDomHost D (take 0) = D` is the plain joint envelope and the component term
is `invToG`'s primary component `gW` — stated directly (the `hostComps = [gW]` kernel
identity is blocked by `String.startsWith` being kernel-irreducible; the alignment is
covered by the drift-checked emitted IR, same as the battery). Padded to `n = 2`. -/
def VerdW (l q : ℕ) : Prop :=
  z3solve (flowQuery ⟨gW, fLW l, fRW q, Term.const 1,
    Formula.and domLW domRW⟩) = Verdict.unsat
  ∨ z3solve (flowQueryStrict ⟨gW, fLW l, fRW q, Term.const 1,
    Formula.and domLW domRW⟩) = Verdict.unsat
  ∨ z3solve (flowQuerySuperlevel ⟨gW, fLW l, fRW q, Term.const 1,
    Formula.and domLW domRW⟩) = Verdict.unsat

/-- The per-pair duration-existence residual, ENVELOPE-CONDITIONED and CLOCK-CAPPED:
anchors are only the loop invariant's states, and responses are needed only for left
durations `≤ dt` (`HExistSegB`) — the honest form both ways (the unconditioned `∀ ν`
version is false in general; the `∀ s` version needlessly demands unbounded flows).
Dischargeable from bounded box viability (`HExistSegB_of_viability` + the anchor
conditioning verdicts) — the S3 emission wiring. -/
def ESW (l q : ℕ) (dt : ℝ) : Prop :=
  ∀ σ, Formula.sat (Formula.and (invLe gW) envW) σ →
    HExistSegB (fLW l) (fRW q) (Term.const 1) domLW domRW dt (Function.update σ tgM 0)

/-! ## The per-pair bounded coupling (cert-sourced, envelope-strengthened) -/

theorem coupleW {l q : ℕ} (hl : l < 3) (hq : q < 3) (dt : ℝ)
    (hv : VerdW l q) (hES : ESW l q dt) :
    ∀ σ', Formula.sat (Formula.and (invLe gW) envW) σ' → σ' tgM = 0 →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tgM (leftBlock (fLW l))) domLW)
        (Program.ode (rightBlock (fRW q) (Term.const 1)) domRW)
        (Formula.and (invLe gW) envW) tgM dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgM (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgM
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLW l) (fRW q) (Term.const 1)
    (Formula.and domLW domRW) [gW]
    (by
      intro i hi
      have hi1 : i < 1 := by simpa using hi
      interval_cases i
      simpa [strataDomHost, VerdW] using hv)
  have hbox : Formula.sat (Formula.box (Program.ode
      (leftBlock (fLW l) ++ rightBlock (fRW q) (Term.const 1))
      (Formula.and domLW domRW)) (invLe gW)) σ' := by
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) gW
      List.mem_cons_self
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact (sat_invLe gW σ').mp hσ'.1
  have hbase := segment_faModalB_from_certB gW (fLW l) (fRW q) (Term.const 1)
    domLW domRW tgM dt
    (LR_blocks_disjoint _ _ _ (hfLW l hl) (hfRW q hq) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLW hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRW hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLW l) _ h
      exact aux_ne_Lv aM i hi)
    (fun h => aux_notin_range_Lv aM (leftBlock_readVars_sub (fLW l) (hfLW l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRW q) (Term.const 1) _ h
      exact aux_ne_Rv aM i hi)
    (fun h => aux_notin_range_Rv aM (rightBlock_readVars_sub (fRW q) (Term.const 1)
      (hfRW q hq) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aM (rightBlock_boundSet_sub (fRW q) (Term.const 1) h))
    (fun h => aux_notin_range_Lv aM (hdomLW h))
    (fun h => aux_notin_range_Rv aM (hdomRW h))
    htggW hbox (hES σ' hσ')
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLW ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRW μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLW μ := by
    rwa [(Formula.coincidence domLW (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLW hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRW q) (Term.const 1) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLW μ ↔ Formula.sat domLW ν)]
  exact ⟨hdomLμ, hdomRμ⟩

/-! ## Per-(window, start) responses -/

/-- JointOK start: the single self-edge piece. -/
theorem seg_selfW (dt : ℝ) {l q : ℕ} (hl : l < 3) (hq : q < 3)
    (hv : VerdW l q) (hES : ESW l q dt)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (invLe gW) envW) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLW l)) domLW tgM dt 1)
      (bigSeq ([((q : ℕ), modeW q, edgeW q q)].map
        (fun s => Program.ode s.2.1.sys s.2.1.dom)))
      (Formula.and (invLe gW) envW)) σ := by
  have hfa := Hmulti_window1_prefixed (fLW l) domLW gW envW aM dt htggW htgenvW []
    (by simp) (by simp) (hfLW l hl) hdomLW
    (Program.ode (rightBlock (fRW q) (Term.const 1)) domRW)
    (coupleW hl hq dt hv hES) hσ
  simpa [modeW] using hfa

/-- Non-jointOK start `qh`: static hop `qh → 1` (Mid), then the piece at Mid. -/
theorem seg_hopW (dt : ℝ) {l qh : ℕ} (hl : l < 3) (hqh : qh < 3)
    (hv : VerdW l 1) (hES : ESW l 1 dt)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (invLe gW) envW) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLW l)) domLW tgM dt 1)
      (bigSeq ([((qh : ℕ), modeW qh, edgeW qh 1), ((1 : ℕ), modeW 1, edgeW 1 1)].map
        (fun s => Program.ode s.2.1.sys s.2.1.dom)))
      (Formula.and (invLe gW) envW)) σ := by
  have hfa := Hmulti_window1_prefixed (fLW l) domLW gW envW aM dt htggW htgenvW
    [⟨fRW qh, Term.const 1, domRW⟩]
    (by
      intro h hh
      rw [List.mem_singleton] at hh
      subst hh
      exact ⟨hfRW qh hqh, by simp [Term.fv], hdomRW⟩)
    (by
      intro h hh σ' hσ' htg'
      rw [List.mem_singleton] at hh
      subst hh
      exact static_hop_exists hσ')
    (hfLW l hl) hdomLW
    (Program.ode (rightBlock (fRW 1) (Term.const 1)) domRW)
    (coupleW hl (by norm_num) dt hv hES) hσ
  refine sat_faModal_monoR (fun ν μ hrun => sem_bigSeq_mono ?_ ν μ hrun) hfa
  refine List.Forall₂.cons ?_ (List.Forall₂.cons (fun ν μ h => h) List.Forall₂.nil)
  intro ν μ h
  exact sem_ode_dom_and_right
    ((sem_rightBlock_frozen_iff (hfRW qh hqh) (by simp [Term.fv])).mp h)

/-! ## The `Hmulti` provider -/

theorem HmultiW (dt : ℝ)
    (h00 : VerdW 0 0) (h01 : VerdW 0 1) (h11 : VerdW 1 1)
    (h20 : VerdW 2 0) (h21 : VerdW 2 1) (h22 : VerdW 2 2)
    (hES00 : ESW 0 0 dt) (hES01 : ESW 0 1 dt) (hES11 : ESW 1 1 dt)
    (hES20 : ESW 2 0 dt) (hES21 : ESW 2 1 dt) (hES22 : ESW 2 2 dt) :
    ∀ P ∈ leftProgsW dt, ∀ (q : ℕ), q < GrW.modes.length → ∀ σ, σ mvM = (q : ℝ) →
      Formula.sat (Formula.and (invLe gW) envW) σ →
      ∃ segs : List (ℕ × RMode (Var 2) × REdge (Var 2)),
        (∀ s ∈ segs, GrW.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrW.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 2)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (invLe gW) envW)) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrW] using hq
  simp only [leftProgsW, leftDataW, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  have hsingle : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2)),
      List.IsChain (fun a b => a.2.2.tgt = b.1) [a] := by
    intro a; simp
  have hpair : ∀ (qh : ℕ), List.IsChain (fun a b => a.2.2.tgt = b.1)
      [((qh : ℕ), modeW qh, edgeW qh 1), ((1 : ℕ), modeW 1, edgeW 1 1)] := by
    intro qh
    refine (hsingle _).cons ?_
    intro y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    rfl
  have hhead1 : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  interval_cases q
  · -- start Low (0)
    rcases hP with rfl | rfl | rfl
    · exact ⟨[(0, modeW 0, edgeW 0 0)],
        (by
          intro s hs
          rw [List.mem_singleton] at hs
          subst hs
          exact ⟨rfl, edgeW_from (by simp [GrW])⟩),
        hsingle _,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        seg_selfW dt (by norm_num) (by norm_num) h00 hES00 hσ⟩
    · exact ⟨[(0, modeW 0, edgeW 0 1), (1, modeW 1, edgeW 1 1)],
        (by
          intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact ⟨rfl, edgeW_from (by simp [GrW])⟩
          · exact ⟨rfl, edgeW_from (by simp [GrW])⟩),
        hpair 0,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        seg_hopW dt (by norm_num) (by norm_num) h11 hES11 hσ⟩
    · exact ⟨[(0, modeW 0, edgeW 0 0)],
        (by
          intro s hs
          rw [List.mem_singleton] at hs
          subst hs
          exact ⟨rfl, edgeW_from (by simp [GrW])⟩),
        hsingle _,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        seg_selfW dt (by norm_num) (by norm_num) h20 hES20 hσ⟩
  · -- start Mid (1)
    rcases hP with rfl | rfl | rfl
    · exact ⟨[(1, modeW 1, edgeW 1 1)],
        (by
          intro s hs
          rw [List.mem_singleton] at hs
          subst hs
          exact ⟨rfl, edgeW_from (by simp [GrW])⟩),
        hsingle _,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        seg_selfW dt (by norm_num) (by norm_num) h01 hES01 hσ⟩
    · exact ⟨[(1, modeW 1, edgeW 1 1)],
        (by
          intro s hs
          rw [List.mem_singleton] at hs
          subst hs
          exact ⟨rfl, edgeW_from (by simp [GrW])⟩),
        hsingle _,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        seg_selfW dt (by norm_num) (by norm_num) h11 hES11 hσ⟩
    · exact ⟨[(1, modeW 1, edgeW 1 1)],
        (by
          intro s hs
          rw [List.mem_singleton] at hs
          subst hs
          exact ⟨rfl, edgeW_from (by simp [GrW])⟩),
        hsingle _,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        seg_selfW dt (by norm_num) (by norm_num) h21 hES21 hσ⟩
  · -- start High (2)
    rcases hP with rfl | rfl | rfl
    · exact ⟨[(2, modeW 2, edgeW 2 1), (1, modeW 1, edgeW 1 1)],
        (by
          intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact ⟨rfl, edgeW_from (by simp [GrW])⟩
          · exact ⟨rfl, edgeW_from (by simp [GrW])⟩),
        hpair 2,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        seg_hopW dt (by norm_num) (by norm_num) h01 hES01 hσ⟩
    · exact ⟨[(2, modeW 2, edgeW 2 1), (1, modeW 1, edgeW 1 1)],
        (by
          intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact ⟨rfl, edgeW_from (by simp [GrW])⟩
          · exact ⟨rfl, edgeW_from (by simp [GrW])⟩),
        hpair 2,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        seg_hopW dt (by norm_num) (by norm_num) h11 hES11 hσ⟩
    · exact ⟨[(2, modeW 2, edgeW 2 2)],
        (by
          intro s hs
          rw [List.mem_singleton] at hs
          subst hs
          exact ⟨rfl, edgeW_from (by simp [GrW])⟩),
        hsingle _,
        (fun s hs => by rw [hhead1 _ _ _ hs]),
        seg_selfW dt (by norm_num) (by norm_num) h22 hES22 hσ⟩

/-! ## The S1 gate -/

/-- **`watertank`, reposition-window modal Theorem 3, end to end.** Three left windows
(one clock-capped piece each), the transition-faithful three-mode right automaton with
the declared edges, and per-(window, start) responses: joint-certified starts answer
with the self-edge piece; uncertified starts (`Low`-window/`High`-start,
`Mid`-window/`Low`- and `High`-start) answer with a STATIC reposition hop along a
declared edge to `Mid`, then the certified piece there. The loop invariant is the
envelope-carrying `phiInvE` via the LR-split relational form. Residuals: six per-pair
route verdicts (`VerdW`, the tool's stratified `checkSeg` family) and six
envelope-conditioned duration-existence facts (`ESW`, S3's target). -/
theorem watertank_modal (dt : ℝ)
    (h00 : VerdW 0 0) (h01 : VerdW 0 1) (h11 : VerdW 1 1)
    (h20 : VerdW 2 0) (h21 : VerdW 2 1) (h22 : VerdW 2 2)
    (hES00 : ESW 0 0 dt) (hES01 : ESW 0 1 dt) (hES11 : ESW 1 1 dt)
    (hES20 : ESW 2 0 dt) (hES21 : ESW 2 1 dt) (hES22 : ESW 2 2 dt) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsW dt))
      (rightAutomatonBody GrW mvM)
      (RFormula.and (RFormula.and (canonInv gW) (envLR domLW domRW))
        (mvValidR mvM GrW.modes.length))) := by
  refine theorem3_faithful_multiE_LR GrW mvM gW domLW domRW (leftProgsW dt)
    (canonInv gW) (encode_canonInv gW) ?_ ?_ ?_
  · exact hdis_multi GrW 0 1 dt leftDataW (by decide) httW hRvW hLW
  · exact hstep_assembled_multiE GrW mvM gW envW (leftProgsW dt) hmvgW hmvenvW
      hfreshW httW hltW (hframesW dt)
      (HmultiW dt h00 h01 h11 h20 h21 h22 hES00 hES01 hES11 hES20 hES21 hES22)
  · exact hddF_multiE GrW 0 1 dt leftDataW (canonInv gW) domLW domRW (by decide)
      httW hRvW hLW (canonInv_varsL gW hgW) (canonInv_varsR gW) hdomLW hdomRW

end WatertankModal
end RelCertifier
