/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The checked-cut lift (phase 3): per-atom staying and the narrowed-query repair

The tool narrows its flow-query domains by checked cuts; the Z3 UNSAT it obtains is for
the NARROWED query. This file lifts that verdict back to the bare-evolution-domain
`BoxLe` the proof chain consumes, at bases where the cut atoms hold (guard bases, by O1):

* per-atom staying: each atom's O2 UNSAT (route A/B, one-sided, λ = 1) upgrades to
  flow-invariance of the atom along the λ-stretched JOINT system — `Lie` locality for
  one-sided atoms plus the λ-scaling `Lie_λ = λ·Lie_1` (sign-preserving for λ ≥ 0),
  then the same `DI_nonstrict_domain`/`DI_strict` the main certificates use;
* trace staying: endpoint `BoxLe` at every run prefix gives pointwise staying along the
  trace, so every bare-domain run IS a cut-domain run (`CutChannel.sem_ode_and_of_stays`);
* the lift: the narrowed certificate then applies to everything reachable
  (`CutChannel.boxLe_cut_lift`, finally consumed).

Scope note (load-bearing): O1 covers GUARD bases only, so narrowed verdicts lift into the
guard-threaded story (`hcert` at `Gd`-states). The flat CSF chain (`pair_faModal`,
quantified over ALL invariant states) must keep consuming un-narrowed queries.
-/
import RelCertifier.CutCertDefs
import RelCertifier.CutChannel
import RelCertifier.Oracle

namespace RelCertifier

open DL DLCalTiming DLRel Function Set RelCertifier.Oracle

variable {n : ℕ}

/-! ## `tderiv` vanishes on non-free variables -/

theorem tderiv_not_free {V : Type*} [DecidableEq V] {t : Term V} {x : V}
    (hx : x ∉ t.fv) (ν : DL.State V) : Term.eval (tderiv t x) ν = 0 := by
  induction t with
  | var y =>
      unfold tderiv
      rw [if_neg (by rintro rfl; exact hx (by simp [Term.fv]))]
      rfl
  | const c => rfl
  | binop op a b iha ihb =>
      have hxa : x ∉ a.fv := fun h => hx (by simp [Term.fv]; exact Or.inl h)
      have hxb : x ∉ b.fv := fun h => hx (by simp [Term.fv]; exact Or.inr h)
      cases op with
      | add =>
          show Term.eval (tderiv a x) ν + Term.eval (tderiv b x) ν = 0
          rw [iha hxa, ihb hxb]; ring
      | sub =>
          show Term.eval (tderiv a x) ν - Term.eval (tderiv b x) ν = 0
          rw [iha hxa, ihb hxb]; ring
      | mul =>
          show Term.eval (tderiv a x) ν * Term.eval b ν
              + Term.eval a ν * Term.eval (tderiv b x) ν = 0
          rw [iha hxa, ihb hxb]; ring

/-! ## `Lie` locality and λ-scaling for one-sided atoms -/

/-- Products distribute over list sums (local helper). -/
private theorem sum_map_mul {α : Type*} (l : List α) (f : α → ℝ) (r : ℝ) :
    (l.map fun x => r * f x).sum = r * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- A right-sided atom's Lie derivative along the λ-stretched joint field is `λ` times
its Lie along the one-sided (`fL = 0`, `λ = 1`) field the O2 query used. -/
theorem lieDeriv_one_sided_R (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (c : ℝ)
    (hfv : ∀ i : Fin n, Lv i ∉ g.fv) (x : DL.State (Var n)) :
    Term.eval (lieDeriv g fL fR (Term.const c)) x
      = c * Term.eval (lieDeriv g (fun _ => Term.const 0) fR (Term.const 1)) x := by
  unfold lieDeriv
  rw [eval_sumTerm, eval_sumTerm]
  simp only [List.map_map, Function.comp_def]
  rw [← sum_map_mul]
  congr 1
  refine List.map_congr_left ?_
  intro i _
  simp only [Term.eval, AOp.interp]
  rw [tderiv_not_free (hfv i)]
  ring

/-- A left-sided atom's Lie derivative along the joint field is independent of the right
field and the stretch. -/
theorem lieDeriv_one_sided_L (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (hfv : ∀ i : Fin n, Rv i ∉ g.fv) (x : DL.State (Var n)) :
    Term.eval (lieDeriv g fL fR lam) x
      = Term.eval (lieDeriv g fL (fun _ => Term.const 0) (Term.const 1)) x := by
  unfold lieDeriv
  rw [eval_sumTerm, eval_sumTerm]
  simp only [List.map_map, Function.comp_def]
  congr 1
  refine List.map_congr_left ?_
  intro i _
  simp only [Term.eval, AOp.interp]
  rw [tderiv_not_free (hfv i)]
  ring

/-! ## Per-atom staying from the O2 verdicts -/

/-- Right-sided atom, nonstrict route (A): the O2 UNSAT (`evolve ∧ ġ > 0`, one-sided,
λ = 1) gives flow-invariance of the atom along the λ-stretched joint system on any
domain inside the evolve region, for any λ ≥ 0. -/
theorem atom_boxle_R_nonstrict (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (c : ℝ) (hc : 0 ≤ c) (dom evR : Formula (Var n))
    (hfv : ∀ i : Fin n, Lv i ∉ g.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat evR x)
    (hunsat : ∀ σ, ¬ Formula.sat
      (flowQuery ⟨g, fun _ => Term.const 0, fR, Term.const 1, evR⟩) σ)
    {ν : DL.State (Var n)} (hinit : Term.eval g ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const c)) dom)
      (fun ω => Term.eval g ω) ν := by
  refine DI_nonstrict_domain (jointSys_wellFormed fL fR (Term.const c))
    (term_differentiable g) ?_ hinit
  intro x hx
  rw [← lieDeriv_correct, lieDeriv_one_sided_R g fL fR c hfv]
  have hle : Term.eval (lieDeriv g (fun _ => Term.const 0) fR (Term.const 1)) x ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    exact hunsat x ⟨hdomImp x hx,
      by simpa [flowQuery, Formula.sat, CompOp.interp, Term.eval] using hpos⟩
  exact mul_nonpos_of_nonneg_of_nonpos hc hle

/-- Right-sided atom, strict boundary route (B): needs a strictly positive stretch. -/
theorem atom_boxle_R_strict (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (c : ℝ) (hc : 0 < c) (dom evR : Formula (Var n))
    (hfv : ∀ i : Fin n, Lv i ∉ g.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat evR x)
    (hunsat : ∀ σ, ¬ Formula.sat
      (flowQueryStrict ⟨g, fun _ => Term.const 0, fR, Term.const 1, evR⟩) σ)
    {ν : DL.State (Var n)} (hinit : Term.eval g ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const c)) dom)
      (fun ω => Term.eval g ω) ν := by
  refine DI_strict (jointSys_wellFormed fL fR (Term.const c))
    (term_differentiable g) ?_ hinit
  intro x hx hg0
  rw [← lieDeriv_correct, lieDeriv_one_sided_R g fL fR c hfv]
  have hlt : Term.eval (lieDeriv g (fun _ => Term.const 0) fR (Term.const 1)) x < 0 := by
    by_contra hge
    rw [not_lt] at hge
    exact hunsat x ⟨hdomImp x hx,
      by simpa [Formula.sat, CompOp.interp, Term.eval] using hg0,
      by simpa [Formula.sat, CompOp.interp, Term.eval] using hge⟩
  exact mul_neg_of_pos_of_neg hc hlt

/-- Left-sided atom, nonstrict route (A) — the stretch is immaterial. -/
theorem atom_boxle_L_nonstrict (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (dom evL : Formula (Var n))
    (hfv : ∀ i : Fin n, Rv i ∉ g.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat evL x)
    (hunsat : ∀ σ, ¬ Formula.sat
      (flowQuery ⟨g, fL, fun _ => Term.const 0, Term.const 1, evL⟩) σ)
    {ν : DL.State (Var n)} (hinit : Term.eval g ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom) (fun ω => Term.eval g ω) ν := by
  refine DI_nonstrict_domain (jointSys_wellFormed fL fR lam)
    (term_differentiable g) ?_ hinit
  intro x hx
  rw [← lieDeriv_correct, lieDeriv_one_sided_L g fL fR lam hfv]
  by_contra hpos
  rw [not_le] at hpos
  exact hunsat x ⟨hdomImp x hx,
    by simpa [flowQuery, Formula.sat, CompOp.interp, Term.eval] using hpos⟩

/-- Left-sided atom, strict boundary route (B). -/
theorem atom_boxle_L_strict (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (dom evL : Formula (Var n))
    (hfv : ∀ i : Fin n, Rv i ∉ g.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat evL x)
    (hunsat : ∀ σ, ¬ Formula.sat
      (flowQueryStrict ⟨g, fL, fun _ => Term.const 0, Term.const 1, evL⟩) σ)
    {ν : DL.State (Var n)} (hinit : Term.eval g ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom) (fun ω => Term.eval g ω) ν := by
  refine DI_strict (jointSys_wellFormed fL fR lam) (term_differentiable g) ?_ hinit
  intro x hx hg0
  rw [← lieDeriv_correct, lieDeriv_one_sided_L g fL fR lam hfv]
  by_contra hge
  rw [not_lt] at hge
  exact hunsat x ⟨hdomImp x hx,
    by simpa [Formula.sat, CompOp.interp, Term.eval] using hg0,
    by simpa [Formula.sat, CompOp.interp, Term.eval] using hge⟩

/-! ## Trace staying from endpoint `BoxLe` -/

/-- Endpoint `BoxLe` at every prefix of a run gives pointwise staying along the trace. -/
theorem boxLe_trace {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {gv : DL.State (Var n) → ℝ} {ν : DL.State (Var n)}
    (hB : BoxLe (Program.ode sys dom) gv ν)
    {r : ℝ} {Φ : ℝ → DL.State (Var n)} (hr : 0 ≤ r) (hΦ0 : Φ 0 = ν)
    (hder : ∀ t ∈ Icc (0 : ℝ) r, ∀ p ∈ sys,
        HasDerivWithinAt (fun u => Φ u p.1) (Term.eval p.2 (Φ t)) (Icc 0 r) t)
    (hmask : ∀ t ∈ Icc (0 : ℝ) r, ∀ x, x ∉ sys.bound → Φ t x = ν x)
    (hdom : ∀ t ∈ Icc (0 : ℝ) r, Formula.sat dom (Φ t)) :
    ∀ t ∈ Icc (0 : ℝ) r, gv (Φ t) ≤ 0 := by
  intro t ht
  refine hB (Φ t) ⟨t, Φ, ht.1, hΦ0, rfl, ?_, ?_, ?_⟩
  · intro s hs p hp
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) r := Icc_subset_Icc_right ht.2
    exact (hder s (hsub hs) p hp).mono hsub
  · intro s hs x hx
    exact hmask s (Icc_subset_Icc_right ht.2 hs) x hx
  · intro s hs
    exact hdom s (Icc_subset_Icc_right ht.2 hs)

/-! ## Atom facts and the assembled lift -/

/-- One lifted cut atom: its lowered formula, its safe-side term, the ≤-normal-form
equivalence, and its staying fact along the target system. -/
structure AtomFact (n : ℕ) (sys : ODESystem (Var n)) (dom : Formula (Var n)) where
  form : Formula (Var n)
  gT : Term (Var n)
  hiff : ∀ ν, Formula.sat form ν ↔ Term.eval gT ν ≤ 0
  hstay : ∀ ν, Term.eval gT ν ≤ 0 →
    BoxLe (Program.ode sys dom) (fun ω => Term.eval gT ω) ν

/-- The conjoined cut formula, mirroring the tool's fold. -/
def hostCut {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    (afs : List (AtomFact n sys dom)) : Formula (Var n) :=
  afs.foldl (fun d af => Formula.and d af.form) Formula.tt

theorem sat_hostCut {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    (afs : List (AtomFact n sys dom)) (ν : DL.State (Var n)) :
    Formula.sat (hostCut afs) ν ↔ ∀ af ∈ afs, Formula.sat af.form ν := by
  suffices hgen : ∀ (acc : Formula (Var n)),
      Formula.sat (afs.foldl (fun d af => Formula.and d af.form) acc) ν
        ↔ (Formula.sat acc ν ∧ ∀ af ∈ afs, Formula.sat af.form ν) by
    unfold hostCut
    rw [hgen]
    simp [Formula.sat]
  induction afs with
  | nil => intro acc; simp
  | cons af afs ih =>
      intro acc
      simp only [List.foldl_cons, ih, Formula.sat]
      constructor
      · rintro ⟨⟨hacc, haf⟩, hrest⟩
        exact ⟨hacc, fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact haf
          · exact hrest x hx⟩
      · rintro ⟨hacc, hall⟩
        exact ⟨⟨hacc, hall af (List.mem_cons_self ..)⟩,
          fun x hx => hall x (List.mem_cons_of_mem _ hx)⟩

/-- Runs are insensitive to satisfaction-equivalent domain formulas. -/
theorem sem_ode_congr {sys : ODESystem (Var n)} {D D' : Formula (Var n)}
    (h : ∀ x, Formula.sat D x ↔ Formula.sat D' x) {ω ν : DL.State (Var n)}
    (hsem : Program.sem (Program.ode sys D) ω ν) :
    Program.sem (Program.ode sys D') ω ν := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hsem
  exact ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, fun t ht => (h (Φ t)).mp (hdom t ht)⟩

/-- **The assembled cut lift.** From the NARROWED certificate (`BoxLe` over
`(dom ∧ cutL) ∧ cutR` — what the tool's Z3 UNSAT establishes through
`flow_certified`) and the per-atom facts, the bare-domain `BoxLe` holds at every
base where the cut atoms hold (guard bases, by O1). -/
theorem cut_lift_boxle {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    (afsL afsR : List (AtomFact n sys dom)) (gv : DL.State (Var n) → ℝ)
    {ν : DL.State (Var n)}
    (hnarrow : BoxLe (Program.ode sys
      (Formula.and (Formula.and dom (hostCut afsL)) (hostCut afsR))) gv ν)
    (hbase : ∀ af ∈ afsL ++ afsR, Formula.sat af.form ν) :
    BoxLe (Program.ode sys dom) gv ν := by
  -- staying of the conjoined cut along every bare-domain trace
  have hstays : ∀ (r : ℝ) (Φ : ℝ → DL.State (Var n)), 0 ≤ r → Φ 0 = ν →
      (∀ t ∈ Icc (0 : ℝ) r, ∀ p ∈ sys,
          HasDerivWithinAt (fun u => Φ u p.1) (Term.eval p.2 (Φ t)) (Icc 0 r) t) →
      (∀ t ∈ Icc (0 : ℝ) r, ∀ x, x ∉ sys.bound → Φ t x = ν x) →
      (∀ t ∈ Icc (0 : ℝ) r, Formula.sat dom (Φ t)) →
      ∀ t ∈ Icc (0 : ℝ) r,
        Formula.sat (Formula.and (hostCut afsL) (hostCut afsR)) (Φ t) := by
    intro r Φ hr hΦ0 hder hmask hdom t ht
    have hone : ∀ af ∈ afsL ++ afsR, Formula.sat af.form (Φ t) := by
      intro af haf
      have hb := (af.hiff ν).mp (hbase af haf)
      have := boxLe_trace (af.hstay ν hb) hr hΦ0 hder hmask hdom t ht
      exact (af.hiff (Φ t)).mpr this
    refine ⟨(sat_hostCut afsL (Φ t)).mpr ?_, (sat_hostCut afsR (Φ t)).mpr ?_⟩
    · intro af haf; exact hone af (List.mem_append_left _ haf)
    · intro af haf; exact hone af (List.mem_append_right _ haf)
  -- every bare-domain run is a cut-domain run; the narrowed certificate applies
  intro ω hsem
  refine hnarrow ω (sem_ode_congr ?_ (sem_ode_and_of_stays sys dom
    (Formula.and (hostCut afsL) (hostCut afsR)) hsem
    (fun r Φ hr hΦ0 hΦr hder hmask hdom => hstays r Φ hr hΦ0 hder hmask hdom)))
  intro x
  constructor
  · rintro ⟨hd, hl, hrr⟩
    exact ⟨⟨hd, hl⟩, hrr⟩
  · rintro ⟨⟨hd, hl⟩, hrr⟩
    exact ⟨hd, hl, hrr⟩

/-! ## O1: cut atoms hold wherever the guard holds -/

/-- Every `cutAtoms` element is a nonstrict comparison. -/
theorem cutAtoms_nonstrict {f a : Parse.PForm} (ha : a ∈ cutAtoms f) :
    ∃ op x y, a = Parse.PForm.cmp op x y ∧ (op = "<=" ∨ op = ">=") := by
  induction f with
  | and p q ihp ihq =>
      unfold cutAtoms at ha
      rcases List.mem_append.mp ha with h | h
      · exact ihp h
      · exact ihq h
  | cmp op x y =>
      unfold cutAtoms at ha
      split at ha
      · rename_i hop
        rw [List.mem_singleton.mp ha]
        rcases Bool.or_eq_true .. |>.mp hop with h | h
        · exact ⟨op, x, y, rfl, Or.inl (by simpa using h)⟩
        · exact ⟨op, x, y, rfl, Or.inr (by simpa using h)⟩
      · exact absurd ha (by simp)
  | tt => exact absurd ha (by simp [cutAtoms])
  | or p q ihp ihq => exact absurd ha (by simp [cutAtoms])
  | not p ihp => exact absurd ha (by simp [cutAtoms])

/-- The lowering of a guard implies the lowering of each of its cut atoms. -/
theorem cutAtoms_sat {vars : List String} {side : Side} {f a : Parse.PForm}
    (ha : a ∈ cutAtoms f) : ∀ {fI aI : IForm n},
    Run.lowerF vars n side f = some fI → Run.lowerF vars n side a = some aI →
    ∀ ν, Formula.sat fI.toHost ν → Formula.sat aI.toHost ν := by
  induction f with
  | and p q ihp ihq =>
      intro fI aI hf haI ν hsat
      unfold Run.lowerF at hf
      rcases hp : Run.lowerF vars n side p with _ | pI <;> rw [hp] at hf
      · simp at hf
      rcases hq : Run.lowerF vars n side q with _ | qI <;> rw [hq] at hf
      · simp at hf
      injection hf with hf'
      subst hf'
      obtain ⟨hsp, hsq⟩ := hsat
      unfold cutAtoms at ha
      rcases List.mem_append.mp ha with h | h
      · exact ihp h hp haI ν hsp
      · exact ihq h hq haI ν hsq
  | cmp op x y =>
      intro fI aI hf haI ν hsat
      unfold cutAtoms at ha
      split at ha
      · rw [List.mem_singleton.mp ha] at haI
        rw [haI] at hf
        injection hf with hf'
        subst hf'
        exact hsat
      · exact absurd ha (by simp)
  | tt => intro fI aI hf haI ν hsat; exact absurd ha (by simp [cutAtoms])
  | or p q ihp ihq => intro fI aI hf haI ν hsat; exact absurd ha (by simp [cutAtoms])
  | not p ihp => intro fI aI hf haI ν hsat; exact absurd ha (by simp [cutAtoms])

/-- A nonstrict atom's lowering is satisfaction-equivalent to `g ≤ 0` for its
`cutAtomG` safe-side term. -/
theorem cutAtomG_sat {vars : List String} {side : Side} {op : String}
    {x y : Parse.PExpr} (hop : op = "<=" ∨ op = ">=") {aI : IForm n} {g : ITerm n}
    (haI : Run.lowerF vars n side (Parse.PForm.cmp op x y) = some aI)
    (hg : cutAtomG vars n side (Parse.PForm.cmp op x y) = some g)
    (ν : DL.State (Var n)) :
    Formula.sat aI.toHost ν ↔ Term.eval g.toHost ν ≤ 0 := by
  unfold Run.lowerF at haI
  rcases hex : Run.lowerE vars n side x with _ | ex <;> rw [hex] at haI
  · simp at haI
  rcases hey : Run.lowerE vars n side y with _ | ey <;> rw [hey] at haI
  · simp at haI
  rcases hop with rfl | rfl
  · simp only [cutAtomG, hex, hey, Option.bind_eq_bind, Option.bind] at hg
    simp only [reduceIte] at haI
    injection hg with hg'
    injection haI with haI'
    subst hg'
    subst haI'
    simp only [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
      AOp.interp]
    constructor
    · intro h; linarith
    · intro h; linarith
  · simp only [cutAtomG, hex, hey, Option.bind_eq_bind, Option.bind] at hg
    simp only [reduceIte] at haI
    injection hg with hg'
    injection haI with haI'
    subst hg'
    subst haI'
    simp only [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
      AOp.interp]
    constructor
    · intro h; linarith
    · intro h; linarith

/-! ## Phase 4: the strict-query IR mirror and the guard-base packaging -/

/-- IR mirror of the strict boundary query (the tool's route-B probe shape). -/
def iflowQueryStrict {n : ℕ} (g : ITerm n) (fL fR : Fin n → ITerm n) (lam : ITerm n)
    (domain : IForm n) : IForm n :=
  IForm.and domain (IForm.and (IForm.cmp .eq g (.rat 0))
    (IForm.cmp .ge (ilieDeriv g fL fR lam) (.rat 0)))

theorem iflowQueryStrict_toHost {n : ℕ} (g : ITerm n) (fL fR : Fin n → ITerm n)
    (lam : ITerm n) (domain : IForm n) :
    (iflowQueryStrict g fL fR lam domain).toHost
      = flowQueryStrict ⟨g.toHost, (fun i => (fL i).toHost), (fun i => (fR i).toHost),
          lam.toHost, domain.toHost⟩ := by
  simp [iflowQueryStrict, flowQueryStrict, IForm.toHost, ITerm.toHost, ilieDeriv_toHost]

/-! ### `AtomFact` constructors, one per route -/

/-- Right-sided nonstrict-route atom fact from its O2 Z3 verdict. -/
noncomputable def AtomFact.ofR_nonstrict (fL fR : Fin n → Term (Var n)) (c : ℝ)
    (hc : 0 ≤ c) (dom evR : Formula (Var n)) (form : Formula (Var n))
    (gT : Term (Var n))
    (hiff : ∀ ν, Formula.sat form ν ↔ Term.eval gT ν ≤ 0)
    (hfv : ∀ i : Fin n, Lv i ∉ gT.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat evR x)
    (hz3 : z3solve (flowQuery ⟨gT, fun _ => Term.const 0, fR, Term.const 1, evR⟩)
      = Verdict.unsat) :
    AtomFact n (jointSys fL fR (Term.const c)) dom :=
  { form := form, gT := gT, hiff := hiff,
    hstay := fun ν hinit =>
      atom_boxle_R_nonstrict gT fL fR c hc dom evR hfv hdomImp
        (z3_unsat_sound hz3) hinit }

/-- Right-sided strict-route atom fact from its O2 Z3 verdict (needs λ > 0). -/
noncomputable def AtomFact.ofR_strict (fL fR : Fin n → Term (Var n)) (c : ℝ)
    (hc : 0 < c) (dom evR : Formula (Var n)) (form : Formula (Var n))
    (gT : Term (Var n))
    (hiff : ∀ ν, Formula.sat form ν ↔ Term.eval gT ν ≤ 0)
    (hfv : ∀ i : Fin n, Lv i ∉ gT.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat evR x)
    (hz3 : z3solve (flowQueryStrict ⟨gT, fun _ => Term.const 0, fR, Term.const 1, evR⟩)
      = Verdict.unsat) :
    AtomFact n (jointSys fL fR (Term.const c)) dom :=
  { form := form, gT := gT, hiff := hiff,
    hstay := fun ν hinit =>
      atom_boxle_R_strict gT fL fR c hc dom evR hfv hdomImp
        (z3_unsat_sound hz3) hinit }

/-- Left-sided nonstrict-route atom fact from its O2 Z3 verdict. -/
noncomputable def AtomFact.ofL_nonstrict (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (dom evL : Formula (Var n)) (form : Formula (Var n))
    (gT : Term (Var n))
    (hiff : ∀ ν, Formula.sat form ν ↔ Term.eval gT ν ≤ 0)
    (hfv : ∀ i : Fin n, Rv i ∉ gT.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat evL x)
    (hz3 : z3solve (flowQuery ⟨gT, fL, fun _ => Term.const 0, Term.const 1, evL⟩)
      = Verdict.unsat) :
    AtomFact n (jointSys fL fR lam) dom :=
  { form := form, gT := gT, hiff := hiff,
    hstay := fun ν hinit =>
      atom_boxle_L_nonstrict gT fL fR lam dom evL hfv hdomImp
        (z3_unsat_sound hz3) hinit }

/-- Left-sided strict-route atom fact from its O2 Z3 verdict. -/
noncomputable def AtomFact.ofL_strict (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (dom evL : Formula (Var n)) (form : Formula (Var n))
    (gT : Term (Var n))
    (hiff : ∀ ν, Formula.sat form ν ↔ Term.eval gT ν ≤ 0)
    (hfv : ∀ i : Fin n, Rv i ∉ gT.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat evL x)
    (hz3 : z3solve (flowQueryStrict ⟨gT, fL, fun _ => Term.const 0, Term.const 1, evL⟩)
      = Verdict.unsat) :
    AtomFact n (jointSys fL fR lam) dom :=
  { form := form, gT := gT, hiff := hiff,
    hstay := fun ν hinit =>
      atom_boxle_L_strict gT fL fR lam dom evL hfv hdomImp
        (z3_unsat_sound hz3) hinit }

/-- Shape/frozen-route atom fact from a Lean-proved Lie bound (no Z3): the premise is
the `DI_nonstrict_superlevel` hypothesis, dischargeable per benchmark by `norm_num` on
the concrete lowered field (contract shapes: `ġ = k(c−x) ≤ 0` on `{g ≥ 0}`; frozen
atoms: `ġ = 0`). -/
noncomputable def AtomFact.ofLie (sys : ODESystem (Var n)) (dom : Formula (Var n))
    (form : Formula (Var n)) (gT : Term (Var n))
    (hwf : sys.WellFormed)
    (hiff : ∀ ν, Formula.sat form ν ↔ Term.eval gT ν ≤ 0)
    (hLie : ∀ x, Formula.sat dom x → 0 ≤ Term.eval gT x →
      Lie sys (fun ν => Term.eval gT ν) x ≤ 0) :
    AtomFact n sys dom :=
  { form := form, gT := gT, hiff := hiff,
    hstay := fun ν hinit =>
      DI_nonstrict_superlevel hwf (term_differentiable gT)
        (fun x hx hge => hLie x hx hge) hinit }

/-! ### The guard-base packaging -/

/-- **The cut-`hcert` packaging.** From the NARROWED main-query Z3 verdict (the exact
fold the tool sends: `(dom ∧ cutL) ∧ cutR`) and the per-atom facts, the bare-domain
`BoxLe` holds at every guard base — the shape the guard-threaded chain consumes. `hO1`
is the entry fact (each atom's formula holds wherever the guard's lowering holds),
dischargeable from `cutAtoms_sat` since every atom is a guard conjunct
(`cutCertWF`, kernel). -/
theorem cut_hcert {fL fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {dom guardH : Formula (Var n)} (gInv : Term (Var n))
    (afsL afsR : List (AtomFact n (jointSys fL fR lam) dom))
    (hO1 : ∀ af ∈ afsL ++ afsR, ∀ ν, Formula.sat guardH ν → Formula.sat af.form ν)
    (hz3 : z3solve (flowQuery ⟨gInv, fL, fR, lam,
      Formula.and (Formula.and dom (hostCut afsL)) (hostCut afsR)⟩) = Verdict.unsat) :
    ∀ ν, Formula.sat guardH ν → Term.eval gInv ν ≤ 0 →
      BoxLe (Program.ode (jointSys fL fR lam) dom) (fun ω => Term.eval gInv ω) ν := by
  intro ν hg hinit
  have hnarrow := flow_certified
    ⟨gInv, fL, fR, lam, Formula.and (Formula.and dom (hostCut afsL)) (hostCut afsR)⟩
    hz3 hinit
  exact cut_lift_boxle afsL afsR _ hnarrow (fun af haf => hO1 af haf ν hg)

end RelCertifier
