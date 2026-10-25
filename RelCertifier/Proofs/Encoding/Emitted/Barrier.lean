/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge, part 3: pruned exits, admissibility, handoffs, read from Z3

* **Pruned exits (Definition 6).** The non-connection pair of a pruned edge `src → tgt`
  (`NonConn.queries`: the source check `guard ∧ evolve ∧ cut ∧ g > 0` and the barrier check
  `evolve ∧ cut ∧ g = 0 ∧ ġ_R ≥ 0`, `g` the tool's `guardTerm` of `tgt`'s guard) gives: on
  entering `src` the barrier term is `≤ 0` (`nonconn_entry`), it stays `≤ 0` along every flow
  of `src`'s field, joint or frozen, that keeps `src`'s kept atoms (`nonconn_keep`, strict DI
  on the narrowed domain lifted by the stays), and `tgt`'s guard forces it `> 0`
  (`guard_pos_of_barrier`). The anchor of the bridge carries the barrier terms of a mode's
  pruned exits, so a pruned exit is never enabled at the end of a segment.
* **Admissibility.** `unsat` of `guardL ∧ guardR ∧ ⋀ gᵢ ≤ 0` means no start of the pairing
  satisfies both guards and the row (`adm_sound`).
* **Handoffs.** `unsat` of the domain-conditioned handoff query means the source row, the
  envelope and the target guard imply the target row (`handoff_sound`).
* The row's components mention no auxiliary variable (`hostComps_fv`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Stay

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL Parse Run Set Oracle Bridge

variable {n : ℕ}

/-! ## Lowering facts -/

theorem lowerF_and {vars : List String} {s : Side} {x y : PForm} {f : IForm n}
    (h : lowerF vars n s (.and x y) = some f) :
    ∃ fx fy, lowerF vars n s x = some fx ∧ lowerF vars n s y = some fy ∧ f = IForm.and fx fy := by
  simp only [lowerF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨fx, hx, fy, hy, rfl⟩ := h
  exact ⟨fx, fy, hx, hy, rfl⟩

theorem hostGuard_of_lower {vars : List String} {s : Side} {m : PMode} {f : IForm n}
    (h : lowerF vars n s m.guard = some f) : hostGuard vars n s m = f.toHost := by
  simp [hostGuard, h]
theorem hostEvolve_of_lower {vars : List String} {s : Side} {m : PMode} {f : IForm n}
    (h : lowerF vars n s m.evolve = some f) : hostEvolve vars n s m = f.toHost := by
  simp [hostEvolve, h]
theorem hostDyn_of_lower {vars : List String} {s : Side} {m : PMode} {f : Fin n → ITerm n}
    (h : dynOf vars n s m = some f) : hostDyn vars n s m = fun j => (f j).toHost := by
  funext j; simp [hostDyn, h]

theorem mapM_option_forall {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') : ∀ x ∈ l, ∃ y ∈ l', f x = some y := by
  induction l generalizing l' with
  | nil => simp
  | cons a as ih =>
      rw [List.mapM_cons] at h
      simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨b, hb, bs, hbs, rfl⟩ := h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, List.mem_cons_self, hb⟩
      · obtain ⟨y, hy, hfy⟩ := ih hbs x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- The folded source cut denotes the kept atoms. -/
theorem sat_cutOfAtoms {vars : List String} {atoms : List CutAtomX} {c : IForm n}
    (h : NonConn.cutOfAtoms vars n (atoms.map (·.atom)) = some c) (ν : State (Var n)) :
    Formula.sat c.toHost ν ↔ CutSat (cutPairsX vars n Side.R atoms) ν := by
  unfold NonConn.cutOfAtoms at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at h
  obtain ⟨fs, hfs, rfl⟩ := h
  rw [sat_foldl_and]
  simp only [IForm.toHost, Formula.sat, true_and]
  constructor
  · intro hall a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨f, hf, hlow⟩ := mapM_option_forall hfs x.atom (List.mem_map.mpr ⟨x, hx, rfl⟩)
    simp only [hostAtomF, hlow, Option.map_some, Option.getD_some]
    exact hall f hf
  · intro hcut f hf
    obtain ⟨a, ha, hlow⟩ := mapM_option_mem hfs f hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    have := hcut _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa [hostAtomF, hlow] using this

/-! ## The barrier term of a guard -/

/-- The host barrier term of a mode's guard (`guardTerm`, `0` if it has none). -/
noncomputable def hostBarrier (vars : List String) (n : ℕ) (m : PMode) : Term (Var n) :=
  ((NonConn.guardTerm vars n m.guard).map ITerm.toHost).getD (Term.const 0)

theorem guardTerm_cmp_gt {vars : List String} {a b : PExpr} {t : ITerm n}
    (h : NonConn.guardTerm vars n (.cmp ">" a b) = some t) :
    ∃ ea eb, lowerE vars n Side.R a = some ea ∧ lowerE vars n Side.R b = some eb ∧
      t = ITerm.bin .sub ea eb := by
  simp only [NonConn.guardTerm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ea, hea, eb, heb, rfl⟩ := h
  exact ⟨ea, eb, hea, heb, rfl⟩

theorem guardTerm_cmp_lt {vars : List String} {a b : PExpr} {t : ITerm n}
    (h : NonConn.guardTerm vars n (.cmp "<" a b) = some t) :
    ∃ ea eb, lowerE vars n Side.R a = some ea ∧ lowerE vars n Side.R b = some eb ∧
      t = ITerm.bin .sub eb ea := by
  simp only [NonConn.guardTerm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ea, hea, eb, heb, rfl⟩ := h
  exact ⟨ea, eb, hea, heb, rfl⟩

theorem guardTerm_cmp_other {vars : List String} {op : String} {a b : PExpr}
    (h1 : op ≠ ">") (h2 : op ≠ "<") : NonConn.guardTerm vars n (.cmp op a b) = none := by
  unfold NonConn.guardTerm
  split
  all_goals first
    | rfl
    | (rename_i heq
       first
        | (injection heq with hop
           first | exact absurd hop h1 | exact absurd hop h2)
        | exact absurd heq (by simp))

/-- The guard forces its barrier term positive. -/
theorem guard_pos_of_term {vars : List String} :
    ∀ {guard : PForm} {t : ITerm n} {gf : IForm n}, NonConn.guardTerm vars n guard = some t →
      lowerF vars n Side.R guard = some gf → ∀ ω, Formula.sat gf.toHost ω →
      0 < Term.eval t.toHost ω := by
  intro guard
  induction guard with
  | cmp op a b =>
      intro t gf ht hgf ω hω
      by_cases h1 : op = ">"
      · subst h1
        obtain ⟨ea, eb, hea, heb, rfl⟩ := guardTerm_cmp_gt ht
        simp only [lowerF, hea, heb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
          at hgf
        subst hgf
        simpa [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp]
          using hω
      by_cases h2 : op = "<"
      · subst h2
        obtain ⟨ea, eb, hea, heb, rfl⟩ := guardTerm_cmp_lt ht
        simp only [lowerF, hea, heb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
          at hgf
        subst hgf
        simpa [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp]
          using hω
      rw [guardTerm_cmp_other h1 h2] at ht
      exact absurd ht (by simp)
  | and x y ihx _ =>
      intro t gf ht hgf ω hω
      obtain ⟨fx, fy, hx, -, rfl⟩ := lowerF_and hgf
      exact ihx (by simpa [NonConn.guardTerm] using ht) hx ω hω.1
  | tt => intro t gf ht; simp [NonConn.guardTerm] at ht
  | or x y _ _ => intro t gf ht; simp [NonConn.guardTerm] at ht
  | not x _ => intro t gf ht; simp [NonConn.guardTerm] at ht

/-- The barrier term of an `L_`-free guard is a right term. -/
theorem guardTerm_fv {vars : List String} :
    ∀ {guard : PForm} {t : ITerm n}, PForm.namesFree "L_" guard = true →
      NonConn.guardTerm vars n guard = some t → ∀ v ∈ t.toHost.fv, v.1 = Side.R := by
  intro guard
  induction guard with
  | cmp op a b =>
      intro t hfree ht v hv
      simp only [PForm.namesFree, Bool.and_eq_true] at hfree
      by_cases h1 : op = ">"
      · subst h1
        obtain ⟨ea, eb, hea, heb, rfl⟩ := guardTerm_cmp_gt ht
        simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv
        rcases hv with hv | hv
        · exact Run.lowerE_fv_side (resolvesTo_R vars) hfree.1 hea v hv
        · exact Run.lowerE_fv_side (resolvesTo_R vars) hfree.2 heb v hv
      by_cases h2 : op = "<"
      · subst h2
        obtain ⟨ea, eb, hea, heb, rfl⟩ := guardTerm_cmp_lt ht
        simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv
        rcases hv with hv | hv
        · exact Run.lowerE_fv_side (resolvesTo_R vars) hfree.2 heb v hv
        · exact Run.lowerE_fv_side (resolvesTo_R vars) hfree.1 hea v hv
      rw [guardTerm_cmp_other h1 h2] at ht
      exact absurd ht (by simp)
  | and x y ihx _ =>
      intro t hfree ht
      simp only [PForm.namesFree, Bool.and_eq_true] at hfree
      exact ihx hfree.1 (by simpa [NonConn.guardTerm] using ht)
  | tt => intro t _ ht; simp [NonConn.guardTerm] at ht
  | or x y _ _ => intro t _ ht; simp [NonConn.guardTerm] at ht
  | not x _ => intro t _ ht; simp [NonConn.guardTerm] at ht

/-! ## The non-connection verdict of a pruned edge -/

/-- The verdict: the source cut rebuilds from the kept atoms, the pair rebuilds, both
`unsat`. -/
def NonConnVerd (vars : List String) (n : ℕ) (atoms : List CutAtomX) (src tgt : PMode) : Prop :=
  ∃ cutR q1 q2, NonConn.cutOfAtoms vars n (atoms.map (·.atom)) = some cutR ∧
    NonConn.queries vars n cutR src tgt = some (q1, q2) ∧
    z3solve q1.toHost = Verdict.unsat ∧ z3solve q2.toHost = Verdict.unsat

theorem queries_parts {vars : List String} {cutR : IForm n} {src tgt : PMode} {q1 q2 : IForm n}
    (h : NonConn.queries vars n cutR src tgt = some (q1, q2)) :
    ∃ (g : ITerm n) (domR0 srcR0 : IForm n) (fR : Fin n → ITerm n),
      NonConn.guardTerm vars n tgt.guard = some g ∧
      lowerF vars n Side.R src.evolve = some domR0 ∧
      lowerF vars n Side.R (PForm.and src.guard src.evolve) = some srcR0 ∧
      dynOf vars n Side.R src = some fR ∧
      q1 = IForm.and (IForm.and srcR0 cutR) (IForm.cmp .gt g (ITerm.rat 0)) ∧
      q2 = IForm.and (IForm.and domR0 cutR) (IForm.and (IForm.cmp .eq g (ITerm.rat 0))
        (IForm.cmp .ge (ilieDeriv g (fun _ => ITerm.rat 0) fR (ITerm.rat 1)) (ITerm.rat 0))) := by
  unfold NonConn.queries at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨g, hg, domR0, hdom, srcR0, hsrc, fR, hfR, h1, h2⟩ := h
  exact ⟨g, domR0, srcR0, fR, hg, hdom, hsrc, hfR, h1.symm, h2.symm⟩

/-- **Entry**: in the source's guard, evolve domain and kept atoms, the barrier is `≤ 0`. -/
theorem nonconn_entry {vars : List String} {atoms : List CutAtomX} {src tgt : PMode}
    (hv : NonConnVerd vars n atoms src tgt) :
    ∀ y, Formula.sat (hostGuard vars n Side.R src) y → Formula.sat (hostEvolve vars n Side.R src) y →
      CutSat (cutPairsX vars n Side.R atoms) y → Term.eval (hostBarrier vars n tgt) y ≤ 0 := by
  obtain ⟨cutR, q1, q2, hcut, hq, hz1, -⟩ := hv
  obtain ⟨g, domR0, srcR0, fR, hg, hdom, hsrc, hfR, rfl, -⟩ := queries_parts hq
  intro y hgy hey hcy
  obtain ⟨fg, fe, hfg, hfe, rfl⟩ := lowerF_and hsrc
  rw [hostGuard_of_lower hfg] at hgy
  rw [hostEvolve_of_lower hfe] at hey
  have hB : hostBarrier vars n tgt = g.toHost := by simp [hostBarrier, hg]
  rw [hB]
  by_contra hpos
  rw [not_le] at hpos
  apply z3_unsat_sound hz1 y
  refine ⟨⟨⟨hgy, hey⟩, (sat_cutOfAtoms hcut y).mpr hcy⟩, ?_⟩
  simpa [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval] using hpos

/-- **Kept**: along any flow of the source's field (any left field, positive stretch) inside
its evolve domain that keeps its atoms, the barrier stays `≤ 0`. -/
theorem nonconn_keep {vars : List String} {atoms : List CutAtomX} {src tgt : PMode}
    (hv : NonConnVerd vars n atoms src tgt) (hwf : atomsWF vars n Side.R "L_" atoms = true)
    (hfree : PForm.namesFree "L_" tgt.guard = true)
    (fL : Fin n → Term (Var n)) (c : ℝ) (hc : 0 < c) (dom : Formula (Var n))
    (hdomEv : ∀ z, Formula.sat dom z → Formula.sat (hostEvolve vars n Side.R src) z)
    (hstay : AtomsStayC (cutPairsX vars n Side.R atoms)
      (jointSys fL (hostDyn vars n Side.R src) (Term.const c)) dom) :
    ∀ ν, CutSat (cutPairsX vars n Side.R atoms) ν → Term.eval (hostBarrier vars n tgt) ν ≤ 0 →
      BoxLe (Program.ode (jointSys fL (hostDyn vars n Side.R src) (Term.const c)) dom)
        (fun ω => Term.eval (hostBarrier vars n tgt) ω) ν := by
  obtain ⟨cutR, q1, q2, hcut, hq, -, hz2⟩ := hv
  obtain ⟨g, domR0, srcR0, fR, hg, hdom, hsrc, hfR, -, rfl⟩ := queries_parts hq
  intro ν hcν hinit
  have hB : hostBarrier vars n tgt = g.toHost := by simp [hostBarrier, hg]
  rw [hB] at hinit ⊢
  have hfv : ∀ j : Fin n, Lv j ∉ g.toHost.fv := by
    intro j hj
    have := guardTerm_fv hfree hg _ hj
    simp at this
  set D := (IForm.and domR0 cutR).toHost with hD
  have hnarrow : BoxLe (Program.ode (jointSys fL (hostDyn vars n Side.R src) (Term.const c))
      (Formula.and dom D)) (fun ω => Term.eval g.toHost ω) ν := by
    rw [hostDyn_of_lower hfR]
    refine atom_boxle_R_strict g.toHost fL (fun j => (fR j).toHost) c hc (Formula.and dom D) D
      hfv (fun z h => h.2) ?_ hinit
    intro σ hσ
    apply z3_unsat_sound hz2 σ
    simpa [flowQueryStrict, IForm.toHost, ITerm.toHost, ilieDeriv_toHost, hD] using hσ
  refine boxle_of_stays_in hnarrow ?_
  intro r Φ hr h0 hder hmask hdomΦ t ht
  rw [hD]
  refine ⟨?_, (sat_cutOfAtoms hcut _).mpr ?_⟩
  · have := hdomEv _ (hdomΦ t ht)
    rwa [hostEvolve_of_lower hdom] at this
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hok := (atomsWF_at hwf (List.getElem?_eq_getElem hi)).1
    have hB' := hstay _ ha ν hcν
    exact (atomOK_iff hok _).mpr (boxLe_trace hB' hr h0 hder hmask hdomΦ t ht)

/-- **The guard of the pruned target forces the barrier positive.** -/
theorem guard_pos_of_barrier {vars : List String} {atoms : List CutAtomX} {src tgt : PMode}
    (hv : NonConnVerd vars n atoms src tgt) {gf : IForm n}
    (hlow : lowerF vars n Side.R tgt.guard = some gf) :
    ∀ ω, Formula.sat (hostGuard vars n Side.R tgt) ω → 0 < Term.eval (hostBarrier vars n tgt) ω := by
  obtain ⟨cutR, q1, q2, -, hq, -, -⟩ := hv
  obtain ⟨g, -, -, -, hg, -, -, -, -, -⟩ := queries_parts hq
  intro ω hω
  rw [hostGuard_of_lower hlow] at hω
  have hB : hostBarrier vars n tgt = g.toHost := by simp [hostBarrier, hg]
  rw [hB]
  exact guard_pos_of_term hg hlow ω hω

/-! ## Admissibility -/

def AdmVerd (vars : List String) (n : ℕ) (row : PForm) (mL mR : PMode) : Prop :=
  ∃ q, admQueryOf vars n row mL mR = some q ∧ z3solve q.toHost = Verdict.unsat

theorem sat_foldl_le (cs : List (ITerm n)) (b : IForm n) (z : State (Var n)) :
    Formula.sat (cs.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) b).toHost z ↔
      Formula.sat b.toHost z ∧ ∀ c ∈ cs, Term.eval c.toHost z ≤ 0 := by
  induction cs generalizing b with
  | nil => simp
  | cons c cs ih =>
      rw [List.foldl_cons, ih]
      simp only [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rat.cast_zero,
        List.mem_cons, forall_eq_or_imp]
      tauto

theorem hostComps_of_lower {vars : List String} {f : PForm} {cs : List (ITerm n)}
    (h : invComponents vars n f = some cs) : hostComps vars n f = cs.map ITerm.toHost := by
  simp [hostComps, h]

/-- No state of the start satisfies both guards and the row. -/
theorem adm_sound {vars : List String} {row : PForm} {mL mR : PMode}
    (hv : AdmVerd vars n row mL mR) :
    ∀ σ, Formula.sat (hostGuard vars n Side.L mL) σ → Formula.sat (hostGuard vars n Side.R mR) σ →
      (∀ c ∈ hostComps vars n row, Term.eval c σ ≤ 0) → False := by
  obtain ⟨q, hq, hz⟩ := hv
  unfold admQueryOf at hq
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at hq
  obtain ⟨cs, hcs, gL, hgL, gR, hgR, rfl⟩ := hq
  intro σ hL hR hrow
  rw [hostGuard_of_lower hgL] at hL
  rw [hostGuard_of_lower hgR] at hR
  rw [hostComps_of_lower hcs] at hrow
  apply z3_unsat_sound hz σ
  rw [sat_foldl_le]
  refine ⟨⟨hL, hR⟩, fun c hc => hrow _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩

/-! ## Handoffs -/

def HandoffVerd (p : PProblem) (n : ℕ) (tr : ℕ × ℕ) : Prop :=
  ∃ q, Handoff.queryOf p n tr = some q ∧ z3solve q.toHost = Verdict.unsat

theorem sat_iinvConj (cs : List (ITerm n)) (b : IForm n) (z : State (Var n)) :
    Formula.sat (Handoff.iinvConj cs b).toHost z ↔
      Formula.sat b.toHost z ∧ ∀ c ∈ cs, Term.eval c.toHost z ≤ 0 :=
  sat_foldl_le cs b z

/-- The source row, the source's evolve domain, the target's guard and the right evolve
domain give the target row. -/
theorem handoff_sound {p : PProblem} {tr : ℕ × ℕ} (hv : HandoffVerd p n tr)
    {rowS rowT : PForm}
    (hS : Handoff.invRowOf p (p.L.modes.getD tr.1 dm) = some rowS)
    (hT : Handoff.invRowOf p (p.L.modes.getD tr.2 dm) = some rowT) :
    ∀ ω, (∀ c ∈ hostComps p.L.stateVars n rowS, Term.eval c ω ≤ 0) →
      Formula.sat (hostEvolve p.L.stateVars n Side.L (p.L.modes.getD tr.1 dm)) ω →
      Formula.sat (hostGuard p.L.stateVars n Side.L (p.L.modes.getD tr.2 dm)) ω →
      Formula.sat (((lowerF p.L.stateVars n Side.R (Handoff.evolveR p)).map IForm.toHost).getD
        Formula.tt) ω →
      ∀ c ∈ hostComps p.L.stateVars n rowT, Term.eval c ω ≤ 0 := by
  obtain ⟨q, hq, hz⟩ := hv
  unfold Handoff.queryOf at hq
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hq
  obtain ⟨rS, hrS, rT, hrT, hq⟩ := hq
  have hdm : (⟨"", [], .tt, .tt, []⟩ : PMode) = dm := rfl
  rw [hdm] at hrS hrT hq
  rw [hS] at hrS; obtain rfl := Option.some.inj hrS
  rw [hT] at hrT; obtain rfl := Option.some.inj hrT
  unfold Handoff.ihandoffQuery at hq
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at hq
  obtain ⟨cs, hcs, eL, heL, gT, hgT, eR, heR, ct, hct, rfl⟩ := hq
  intro ω hrow hev hg heR' c hc
  rw [hostComps_of_lower hcs] at hrow
  rw [hostComps_of_lower hct] at hc
  rw [hostEvolve_of_lower heL] at hev
  rw [hostGuard_of_lower hgT] at hg
  rw [heR] at heR'
  simp only [Option.map_some, Option.getD_some] at heR'
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  by_contra hpos
  rw [not_le] at hpos
  apply z3_unsat_sound hz ω
  refine ⟨(sat_iinvConj cs _ ω).mpr ⟨⟨⟨hev, hg⟩, heR'⟩,
    fun c hc => hrow _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩, ?_⟩
  simp only [IForm.toHost, Formula.sat]
  intro hall
  exact absurd ((sat_iinvConj ct IForm.tt ω).mp hall).2 (by
    intro h; exact absurd (h c' hc') (not_le.mpr hpos))

/-! ## The row's components mention no auxiliary variable -/

theorem invComponents_no_aux {vars : List String} :
    ∀ {f : PForm} {cs : List (ITerm n)}, invComponents vars n f = some cs →
      ∀ t ∈ cs, ∀ v ∈ t.toHost.fv, v.1 ≠ Side.Aux := by
  intro f
  induction f with
  | tt => intro cs h; simp [invComponents] at h; subst h; simp
  | cmp op a b =>
      intro cs h t ht v hv
      unfold invComponents at h
      split_ifs at h with h1 h2
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨ea, hea, eb, heb, rfl⟩ := h
        rw [List.mem_singleton] at ht; subst ht
        simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv
        rcases hv with hv | hv
        · exact Run.lowerE_no_aux (by decide) hea v hv
        · exact Run.lowerE_no_aux (by decide) heb v hv
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨ea, hea, eb, heb, rfl⟩ := h
        rw [List.mem_singleton] at ht; subst ht
        simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv
        rcases hv with hv | hv
        · exact Run.lowerE_no_aux (by decide) heb v hv
        · exact Run.lowerE_no_aux (by decide) hea v hv
      all_goals simp at h
  | and x y ihx ihy =>
      intro cs h t ht
      simp only [invComponents, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨lx, hlx, ly, hly, rfl⟩ := h
      rcases List.mem_append.mp ht with ht | ht
      · exact ihx hlx t ht
      · exact ihy hly t ht
  | or x y _ _ => intro cs h; simp [invComponents] at h
  | not x _ => intro cs h; simp [invComponents] at h

theorem hostComps_fv (vars : List String) (f : PForm) :
    ∀ c ∈ hostComps vars n f, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc v hv
  unfold hostComps at hc
  rcases h : invComponents vars n f with _ | cs
  · rw [h] at hc; simp at hc
  · rw [h] at hc
    simp only [Option.map_some, Option.getD_some, List.mem_map] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    exact notAux_mem_LR (invComponents_no_aux h t ht v hv)

end Emitted
end RelCertifier
