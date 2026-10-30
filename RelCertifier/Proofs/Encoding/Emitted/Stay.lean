/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge, part 2: the kept atoms stay, from the route verdicts

O2 of the extended cut certificate, read from Z3: each kept atom of a mode stays along every
flow of that mode's own field (any partner field, any nonnegative stretch; the strict route
needs a positive one) from any state where all of the mode's kept atoms hold. The route
query (`Bridge.stayQueryOf`) is over the mode's evolve domain narrowed by the atom's `given`
forms, which are earlier atoms of the same mode; their own stays (by induction on the index)
make every run from such a state stay in the narrowed domain, so the box fact under the
narrowed domain lifts to the flow's domain (`boxle_of_stays_in`). The three routes are the
DI lemmas of `CutLift`/`CutLiftX` (`atom_boxle_*_strict`, `atom_boxle_*_nonstrict`,
`boxle_*_of_super`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Data
import RelCertifier.Trusted.BridgeQueries

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL Parse Run Set Oracle Bridge

variable {n : ℕ}

/-! ## Lifting a box fact out of a narrowed domain -/

/-- A box fact under `dom ∧ D` is one under `dom` when every run in `dom` from `ν` stays in
`D`. -/
theorem boxle_of_stays_in {sys : ODESystem (Var n)} {dom D : Formula (Var n)}
    {gv : State (Var n) → ℝ} {ν : State (Var n)}
    (h : BoxLe (Program.ode sys (Formula.and dom D)) gv ν)
    (hstay : ∀ (r : ℝ) (Φ : ℝ → State (Var n)), 0 ≤ r → Φ 0 = ν →
      (∀ t ∈ Icc (0:ℝ) r, ∀ p ∈ sys,
        HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ t)) (Icc 0 r) t) →
      (∀ t ∈ Icc (0:ℝ) r, ∀ x, x ∉ sys.bound → Φ t x = ν x) →
      (∀ t ∈ Icc (0:ℝ) r, Formula.sat dom (Φ t)) → ∀ t ∈ Icc (0:ℝ) r, Formula.sat D (Φ t)) :
    BoxLe (Program.ode sys dom) gv ν := by
  intro ω hsem
  exact h ω (sem_ode_and_of_stays sys dom D hsem
    (fun r Φ hr h0 _ hder hmask hdom => hstay r Φ hr h0 hder hmask hdom))

/-- The host of a left-fold conjunction. -/
theorem sat_foldl_and (gs : List (IForm n)) (b : IForm n) (z : State (Var n)) :
    Formula.sat (gs.foldl IForm.and b).toHost z ↔
      Formula.sat b.toHost z ∧ ∀ f ∈ gs, Formula.sat f.toHost z := by
  induction gs generalizing b with
  | nil => simp
  | cons f fs ih =>
      rw [List.foldl_cons, ih]
      simp only [IForm.toHost, Formula.sat, List.mem_cons, forall_eq_or_imp]
      tauto

theorem mapM_option_mem {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') : ∀ y ∈ l', ∃ x ∈ l, f x = some y := by
  induction l generalizing l' with
  | nil => simp at h; subst h; simp
  | cons a as ih =>
      rw [List.mapM_cons] at h
      simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨b, hb, bs, hbs, rfl⟩ := h
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨a, List.mem_cons_self, hb⟩
      · obtain ⟨x, hx, hfx⟩ := ih hbs y hy
        exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-! ## Reading the atom checks -/

theorem atomsWF_at {vars : List String} {side : Side} {bad : String} {atoms : List CutAtomX}
    (h : atomsWF vars n side bad atoms = true)
    {i : ℕ} {x : CutAtomX} (hx : atoms[i]? = some x) :
    atomOK vars n side bad x = true ∧ ∀ f ∈ x.given, ∃ j < i, ∃ y, atoms[j]? = some y ∧ y.atom = f := by
  have hi : i < atoms.length := by
    by_contra hlt
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hx
    simp at hx
  simp only [atomsWF, List.all_eq_true, List.mem_range] at h
  have := h i hi
  rw [hx] at this
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at this
  refine ⟨this.1, fun f hf => ?_⟩
  obtain ⟨y, hy, hyf⟩ := this.2 f hf
  obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
  refine ⟨j, ?_, y, ?_, hyf⟩
  · have := hj; rw [List.length_take] at this; omega
  · rw [List.getElem_take] at hjy
    rw [← hjy]
    exact List.getElem?_eq_getElem _

theorem atomOK_shape {vars : List String} {side : Side} {bad : String} {x : CutAtomX}
    (h : atomOK vars n side bad x = true) :
    ∃ op a b, x.atom = PForm.cmp op a b ∧ (op = "<=" ∨ op = ">=") ∧
      PExpr.namesFree bad a = true ∧ PExpr.namesFree bad b = true := by
  unfold atomOK at h
  rcases hat : x.atom with _ | ⟨op, a, b⟩ | _ | _ | _ <;> rw [hat] at h
  · simp at h
  · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    exact ⟨op, a, b, rfl, h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩
  all_goals simp at h

theorem atomOK_lowers {vars : List String} {side : Side} {bad : String} {x : CutAtomX}
    (h : atomOK vars n side bad x = true) : (lowerF vars n side x.atom).isSome = true := by
  unfold atomOK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem atomOK_entry {vars : List String} {side : Side} {bad : String} {x : CutAtomX}
    (h : atomOK vars n side bad x = true) : x.entry ≠ CutEntry.z3 := by
  unfold atomOK at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2

/-- The atom's formula and term agree (`hiff`). -/
theorem atomOK_iff {vars : List String} {side : Side} {bad : String} {x : CutAtomX}
    (h : atomOK vars n side bad x = true) (ν : State (Var n)) :
    Formula.sat (hostAtomF vars n side x.atom) ν ↔ Term.eval (hostAtomG vars n side x.atom) ν ≤ 0 := by
  obtain ⟨op, a, b, hat, hop, -, -⟩ := atomOK_shape h
  rw [hat]
  exact hostAtom_iff hop ν

theorem atomsIff_of_WF {vars : List String} {side : Side} {bad : String} {atoms : List CutAtomX}
    (h : atomsWF vars n side bad atoms = true) : AtomsIff (cutPairsX vars n side atoms) := by
  intro a ha ν
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact atomOK_iff (atomsWF_at h (List.getElem?_eq_getElem hi)).1 ν

theorem atomG_fv_R {vars : List String} {x : CutAtomX} (h : atomOK vars n Side.R "L_" x = true) :
    ∀ j : Fin n, Lv j ∉ (hostAtomG vars n Side.R x.atom).fv := by
  obtain ⟨op, a, b, hat, hop, hfa, hfb⟩ := atomOK_shape h
  intro j hj
  rw [hat] at hj
  have := hostAtomG_fv_side (resolvesTo_R vars) hop hfa hfb _ hj
  simp at this

theorem atomG_fv_L {vars : List String} {x : CutAtomX} (h : atomOK vars n Side.L "R_" x = true) :
    ∀ j : Fin n, Rv j ∉ (hostAtomG vars n Side.L x.atom).fv := by
  obtain ⟨op, a, b, hat, hop, hfa, hfb⟩ := atomOK_shape h
  intro j hj
  rw [hat] at hj
  have := hostAtomG_fv_side (resolvesTo_L vars) hop hfa hfb _ hj
  simp at this

theorem cutPairsX_fv_R {vars : List String} {atoms : List CutAtomX}
    (h : atomsWF vars n Side.R "L_" atoms = true) : ∀ a ∈ cutPairsX vars n Side.R atoms, a.2.fv ⊆ range Rv := by
  intro a ha v hv
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨op, a', b', hat, hop, hfa, hfb⟩ :=
    atomOK_shape (atomsWF_at h (List.getElem?_eq_getElem hi)).1
  simp only at hv
  rw [hat] at hv
  exact side_eq_R_mem (hostAtomG_fv_side (resolvesTo_R vars) hop hfa hfb v hv)

theorem cutPairsX_fv_L {vars : List String} {atoms : List CutAtomX}
    (h : atomsWF vars n Side.L "R_" atoms = true) : ∀ a ∈ cutPairsX vars n Side.L atoms, a.2.fv ⊆ range Lv := by
  intro a ha v hv
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨op, a', b', hat, hop, hfa, hfb⟩ :=
    atomOK_shape (atomsWF_at h (List.getElem?_eq_getElem hi)).1
  simp only at hv
  rw [hat] at hv
  exact side_eq_L_mem (hostAtomG_fv_side (resolvesTo_L vars) hop hfa hfb v hv)

/-! ## One atom, from its route query -/

/-- The stay verdict of a mode's kept atoms on a side. -/
def StayVerd (vars : List String) (n : ℕ) (side : Side) (m : PMode) (atoms : List CutAtomX) :
    Prop :=
  ∀ i < atoms.length, ∃ q, stayQueryOf vars n side m atoms i = some q ∧
    z3solve q.toHost = Verdict.unsat

/-- The pieces of a built route query. -/
theorem stayQuery_dom {vars : List String} {side : Side} {m : PMode} {atoms : List CutAtomX}
    {i : ℕ} {x : CutAtomX} (hx : atoms[i]? = some x) {q : IForm n}
    (hq : stayQueryOf vars n side m atoms i = some q) :
    ∃ (f : Fin n → ITerm n) (g : ITerm n) (ev : IForm n) (givens : List (IForm n)),
      dynOf vars n side m = some f ∧ cutAtomG vars n side x.atom = some g ∧
      lowerF vars n side m.evolve = some ev ∧ x.given.mapM (lowerF vars n side) = some givens ∧
      q = routeQuery x.route (givens.foldl IForm.and ev) g (ownLie side g f) := by
  unfold stayQueryOf at hq
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at hq
  obtain ⟨x', hx', f, hf, g, hg, ev, hev, givens, hgv, hq⟩ := hq
  rw [hx] at hx'
  obtain rfl := Option.some.inj hx'
  exact ⟨f, g, ev, givens, hf, hg, hev, hgv, hq.symm⟩

section Atom

variable {vars : List String} {m : PMode} {atoms : List CutAtomX} {i : ℕ} {x : CutAtomX}

/-- A right atom stays along any joint flow of its mode's field from a state where it holds,
inside a domain within the mode's evolve domain, when every run in that domain keeps the
atom's given forms. -/
theorem stayR_of_query (hx : atoms[i]? = some x) (hok : atomOK vars n Side.R "L_" x = true)
    {q : IForm n} (hq : stayQueryOf vars n Side.R m atoms i = some q)
    (hz : z3solve q.toHost = Verdict.unsat)
    (fL : Fin n → Term (Var n)) (c : ℝ) (hc : 0 ≤ c) (dom : Formula (Var n))
    (hdomEv : ∀ z, Formula.sat dom z → Formula.sat (hostEvolve vars n Side.R m) z)
    {ν : State (Var n)} (hinit : Term.eval (hostAtomG vars n Side.R x.atom) ν ≤ 0)
    (hgiv : ∀ (r : ℝ) (Φ : ℝ → State (Var n)), 0 ≤ r → Φ 0 = ν →
      (∀ t ∈ Icc (0:ℝ) r, ∀ p ∈ jointSys fL (hostDyn vars n Side.R m) (Term.const c),
        HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ t)) (Icc 0 r) t) →
      (∀ t ∈ Icc (0:ℝ) r, ∀ v, v ∉ (jointSys fL (hostDyn vars n Side.R m) (Term.const c)).bound →
        Φ t v = ν v) →
      (∀ t ∈ Icc (0:ℝ) r, Formula.sat dom (Φ t)) →
      ∀ t ∈ Icc (0:ℝ) r, ∀ f ∈ x.given, Formula.sat (hostAtomF vars n Side.R f) (Φ t)) :
    BoxLe (Program.ode (jointSys fL (hostDyn vars n Side.R m) (Term.const c)) dom)
      (fun ω => Term.eval (hostAtomG vars n Side.R x.atom) ω) ν := by
  obtain ⟨f, g, ev, givens, hf, hg, hev, hgv, rfl⟩ := stayQuery_dom hx hq
  have hfR : hostDyn vars n Side.R m = fun j => (f j).toHost := by
    funext j; simp [hostDyn, hf]
  have hgH : hostAtomG vars n Side.R x.atom = g.toHost := by simp [hostAtomG, hg]
  have hevH : hostEvolve vars n Side.R m = ev.toHost := by simp [hostEvolve, hev]
  have hfv := atomG_fv_R (vars := vars) (n := n) hok
  rw [hgH] at hfv hinit ⊢
  set D := (givens.foldl IForm.and ev).toHost with hD
  have hnot := z3_unsat_sound hz
  -- the narrowed box fact, by the route
  have hnarrow : BoxLe (Program.ode (jointSys fL (hostDyn vars n Side.R m) (Term.const c))
      (Formula.and dom D)) (fun ω => Term.eval g.toHost ω) ν := by
    rw [hfR]
    rcases hroute : x.route with _ | _ | _ | _ | _ | _ | _
    all_goals simp only [hroute, routeQuery, ownLie] at hnot
    -- route B
    pick_goal 3
    · refine atom_boxle_R_strict0 g.toHost fL (fun j => (f j).toHost) c hc (Formula.and dom D) D
        hfv (fun z h => h.2) ?_ hinit
      intro σ hσ
      apply hnot σ
      simpa [flowQueryStrict, IForm.toHost, ITerm.toHost, ilieDeriv_toHost, hD] using hσ
    -- route A
    pick_goal 3
    · refine atom_boxle_R_nonstrict g.toHost fL (fun j => (f j).toHost) c hc (Formula.and dom D)
        D hfv (fun z h => h.2) ?_ hinit
      intro σ hσ
      apply hnot σ
      simpa [flowQuery, IForm.toHost, ITerm.toHost, ilieDeriv_toHost, hD] using hσ
    -- route C and the rational routes
    all_goals
      refine boxle_R_of_super g.toHost fL (fun j => (f j).toHost) c hc (Formula.and dom D) D
        hfv (fun z h => h.2) ?_ hinit
      intro z hz0 hge
      by_contra hlt
      rw [not_le] at hlt
      apply hnot z
      simp only [IForm.toHost, ITerm.toHost, ilieDeriv_toHost, Formula.sat, CompOp.interp,
        Term.eval, Rat.cast_zero, Rat.cast_one]
      refine ⟨by simpa [hD] using hz0, by simpa using hge, ?_⟩
      simpa [lie1R] using hlt
  refine boxle_of_stays_in hnarrow ?_
  intro r Φ hr h0 hder hmask hdom t ht
  rw [hD, sat_foldl_and]
  refine ⟨by rw [← hevH]; exact hdomEv _ (hdom t ht), ?_⟩
  intro gv hgvmem
  obtain ⟨fm, hfm, hlow⟩ := mapM_option_mem hgv gv hgvmem
  have := hgiv r Φ hr h0 hder hmask hdom t ht fm hfm
  simpa [hostAtomF, hlow] using this

/-- The left counterpart: any right field, any stretch. -/
theorem stayL_of_query (hx : atoms[i]? = some x) (hok : atomOK vars n Side.L "R_" x = true)
    {q : IForm n} (hq : stayQueryOf vars n Side.L m atoms i = some q)
    (hz : z3solve q.toHost = Verdict.unsat)
    (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (dom : Formula (Var n))
    (hdomEv : ∀ z, Formula.sat dom z → Formula.sat (hostEvolve vars n Side.L m) z)
    {ν : State (Var n)} (hinit : Term.eval (hostAtomG vars n Side.L x.atom) ν ≤ 0)
    (hgiv : ∀ (r : ℝ) (Φ : ℝ → State (Var n)), 0 ≤ r → Φ 0 = ν →
      (∀ t ∈ Icc (0:ℝ) r, ∀ p ∈ jointSys (hostDyn vars n Side.L m) fR lam,
        HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ t)) (Icc 0 r) t) →
      (∀ t ∈ Icc (0:ℝ) r, ∀ v, v ∉ (jointSys (hostDyn vars n Side.L m) fR lam).bound →
        Φ t v = ν v) →
      (∀ t ∈ Icc (0:ℝ) r, Formula.sat dom (Φ t)) →
      ∀ t ∈ Icc (0:ℝ) r, ∀ f ∈ x.given, Formula.sat (hostAtomF vars n Side.L f) (Φ t)) :
    BoxLe (Program.ode (jointSys (hostDyn vars n Side.L m) fR lam) dom)
      (fun ω => Term.eval (hostAtomG vars n Side.L x.atom) ω) ν := by
  obtain ⟨f, g, ev, givens, hf, hg, hev, hgv, rfl⟩ := stayQuery_dom hx hq
  have hfL : hostDyn vars n Side.L m = fun j => (f j).toHost := by
    funext j; simp [hostDyn, hf]
  have hgH : hostAtomG vars n Side.L x.atom = g.toHost := by simp [hostAtomG, hg]
  have hevH : hostEvolve vars n Side.L m = ev.toHost := by simp [hostEvolve, hev]
  have hfv := atomG_fv_L (vars := vars) (n := n) hok
  rw [hgH] at hfv hinit ⊢
  set D := (givens.foldl IForm.and ev).toHost with hD
  have hnot := z3_unsat_sound hz
  have hnarrow : BoxLe (Program.ode (jointSys (hostDyn vars n Side.L m) fR lam)
      (Formula.and dom D)) (fun ω => Term.eval g.toHost ω) ν := by
    rw [hfL]
    rcases hroute : x.route with _ | _ | _ | _ | _ | _ | _
    all_goals simp only [hroute, routeQuery, ownLie] at hnot
    pick_goal 3
    · refine atom_boxle_L_strict g.toHost (fun j => (f j).toHost) fR lam (Formula.and dom D) D
        hfv (fun z h => h.2) ?_ hinit
      intro σ hσ
      apply hnot σ
      simpa [flowQueryStrict, IForm.toHost, ITerm.toHost, ilieDeriv_toHost, hD] using hσ
    pick_goal 3
    · refine atom_boxle_L_nonstrict g.toHost (fun j => (f j).toHost) fR lam (Formula.and dom D) D
        hfv (fun z h => h.2) ?_ hinit
      intro σ hσ
      apply hnot σ
      simpa [flowQuery, IForm.toHost, ITerm.toHost, ilieDeriv_toHost, hD] using hσ
    all_goals
      refine boxle_L_of_super g.toHost (fun j => (f j).toHost) fR lam (Formula.and dom D) D
        hfv (fun z h => h.2) ?_ hinit
      intro z hz0 hge
      by_contra hlt
      rw [not_le] at hlt
      apply hnot z
      simp only [IForm.toHost, ITerm.toHost, ilieDeriv_toHost, Formula.sat, CompOp.interp,
        Term.eval, Rat.cast_zero, Rat.cast_one]
      refine ⟨by simpa [hD] using hz0, by simpa using hge, ?_⟩
      simpa [lie1L] using hlt
  refine boxle_of_stays_in hnarrow ?_
  intro r Φ hr h0 hder hmask hdom t ht
  rw [hD, sat_foldl_and]
  refine ⟨by rw [← hevH]; exact hdomEv _ (hdom t ht), ?_⟩
  intro gv hgvmem
  obtain ⟨fm, hfm, hlow⟩ := mapM_option_mem hgv gv hgvmem
  have := hgiv r Φ hr h0 hder hmask hdom t ht fm hfm
  simpa [hostAtomF, hlow] using this

end Atom

/-! ## A mode's atoms, by induction on the index -/

/-- The kept right atoms of `m` conditionally stay along any joint flow of `m`'s field inside
`m`'s evolve domain. -/
theorem atomsStayC_R (vars : List String) (m : PMode) (atoms : List CutAtomX)
    (hwf : atomsWF (vars) n Side.R "L_" atoms = true) (hv : StayVerd vars n Side.R m atoms)
    (fL : Fin n → Term (Var n)) (c : ℝ) (hc : 0 ≤ c) (dom : Formula (Var n))
    (hdomEv : ∀ z, Formula.sat dom z → Formula.sat (hostEvolve vars n Side.R m) z) :
    AtomsStayC (cutPairsX vars n Side.R atoms)
      (jointSys fL (hostDyn vars n Side.R m) (Term.const c)) dom := by
  -- the indexed statement
  have key : ∀ (i : ℕ) (x : CutAtomX), atoms[i]? = some x → ∀ ν, CutSat (cutPairsX vars n Side.R atoms) ν →
      BoxLe (Program.ode (jointSys fL (hostDyn vars n Side.R m) (Term.const c)) dom)
        (fun ω => Term.eval (hostAtomG vars n Side.R x.atom) ω) ν := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro x hx ν hν
      have hi : i < atoms.length := by
        by_contra hlt
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hx
        simp at hx
      obtain ⟨hok, hgiv⟩ := atomsWF_at hwf hx
      obtain ⟨q, hq, hz⟩ := hv i hi
      have hmem : (hostAtomF vars n Side.R x.atom, hostAtomG vars n Side.R x.atom) ∈
          cutPairsX vars n Side.R atoms :=
        List.mem_map.mpr ⟨x, List.mem_of_getElem? hx, rfl⟩
      have hinit : Term.eval (hostAtomG vars n Side.R x.atom) ν ≤ 0 :=
        (atomOK_iff hok ν).mp (hν _ hmem)
      refine stayR_of_query hx hok hq hz fL c hc dom hdomEv hinit ?_
      intro r Φ hr h0 hder hmask hdom t ht f hf
      obtain ⟨j, hj, y, hy, rfl⟩ := hgiv f hf
      have hokj := (atomsWF_at hwf hy).1
      have hB := ih j hj y hy ν hν
      exact (atomOK_iff hokj _).mpr (boxLe_trace hB hr h0 hder hmask hdom t ht)
  intro a ha ν hν
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact key i _ (List.getElem?_eq_getElem hi) ν hν

theorem atomsStayC_L (vars : List String) (m : PMode) (atoms : List CutAtomX)
    (hwf : atomsWF (vars) n Side.L "R_" atoms = true) (hv : StayVerd vars n Side.L m atoms)
    (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (dom : Formula (Var n))
    (hdomEv : ∀ z, Formula.sat dom z → Formula.sat (hostEvolve vars n Side.L m) z) :
    AtomsStayC (cutPairsX vars n Side.L atoms)
      (jointSys (hostDyn vars n Side.L m) fR lam) dom := by
  have key : ∀ (i : ℕ) (x : CutAtomX), atoms[i]? = some x → ∀ ν, CutSat (cutPairsX vars n Side.L atoms) ν →
      BoxLe (Program.ode (jointSys (hostDyn vars n Side.L m) fR lam) dom)
        (fun ω => Term.eval (hostAtomG vars n Side.L x.atom) ω) ν := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro x hx ν hν
      have hi : i < atoms.length := by
        by_contra hlt
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hx
        simp at hx
      obtain ⟨hok, hgiv⟩ := atomsWF_at hwf hx
      obtain ⟨q, hq, hz⟩ := hv i hi
      have hmem : (hostAtomF vars n Side.L x.atom, hostAtomG vars n Side.L x.atom) ∈
          cutPairsX vars n Side.L atoms :=
        List.mem_map.mpr ⟨x, List.mem_of_getElem? hx, rfl⟩
      have hinit : Term.eval (hostAtomG vars n Side.L x.atom) ν ≤ 0 :=
        (atomOK_iff hok ν).mp (hν _ hmem)
      refine stayL_of_query hx hok hq hz fR lam dom hdomEv hinit ?_
      intro r Φ hr h0 hder hmask hdom t ht f hf
      obtain ⟨j, hj, y, hy, rfl⟩ := hgiv f hf
      have hokj := (atomsWF_at hwf hy).1
      have hB := ih j hj y hy ν hν
      exact (atomOK_iff hokj _).mpr (boxLe_trace hB hr h0 hder hmask hdom t ht)
  intro a ha ν hν
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact key i _ (List.getElem?_eq_getElem hi) ν hν

end Emitted
end RelCertifier
