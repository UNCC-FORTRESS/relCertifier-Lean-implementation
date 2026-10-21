/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Refutations, part 2: Theorem 3's claim is false (kinds C and A, mode-keyed form)

Ground truth for "this invariant is correctly rejected": `¬ keyedClaim …`, for EVERY cover
record (so for every pruning of the right automaton: the arguments below never use the right
automaton's edges), at the model's cut certificate `cX`, at `reg = ⊤`, for every window length
`dt ≥ 0`.

W4: the refutation arguments are stated against the UNCLOCKED claim `keyedClaimU` (the pre-W3
`keyedClaim`, right program `rightAutomatonBody`). The clocked claim implies the unclocked one
(`keyedClaim_to_unclocked`: fewer right runs make the claim harder, the clock is erased by
`star_bodyC_to_body`), so each refutation transfers to `¬ keyedClaim … d dt` by contraposition
(`refute_keyed_C_clocked`, `refute_keyed_A_clocked`).

The left run is one step of the left automaton from a witness state `σ` (stored left mode `u`,
stored right mode `q0`): `?(u_L = u) ; ?guard_m ; u_L := m ; ?guard_m ; clock := 0 ; flow_m` for
`m ∈ next(u)`, the flow of duration zero (`sem_ode_zero`). At the bi-state `(σ, σ)` the claim's
antecedent holds (kernel-decided facts of the rational witness, `preOK`), so the claim gives a
right run from `σ` to some `μR` with the post-condition at `(νL, μR)`, `νL` the left end state.
The right run binds only right coordinates and the right mode variable, so `μR` keeps `σ`'s
left values, and the entered row `m` holds at `μR` itself.

* **Kind C (no partner):** a Z3 `unsat` per right mode `q` says no state with the witness's left
  values satisfies row `m`, the right evolve domain, `q`'s guard and `q`'s kept atoms; `μR` would.
* **Kind A (a component broken, right-rigid):** component `k` of row `m` is `> 0` at `σ`, and a
  Z3 `unsat` per right mode says the right field cannot decrease it inside the right evolve
  domain; along every right run (flows by `DI_nonstrict_domain`, jumps change no coordinate the
  component reads) it stays `> 0`, so row `m` fails at `μR`.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteData
import RelCertifier.Proofs.Encoding.LeftAutUniform
import RelCertifier.Proofs.Encoding.RightOnlyStay

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL DLRel DLCalTiming Parse Run Oracle Refute Set

variable {n : ℕ}

/-! ## Relational satisfaction at a bi-state, by pieces -/

/-- The joint state a side-split term reads at `(ωL, ωR)`: right coordinates from `ωR`, every
other coordinate from `ωL` (`rsplit`). -/
def mixS (ωL ωR : State (Var n)) : State (Var n) := fun v => if v.1 = Side.R then ωR v else ωL v

theorem mixS_self (σ : State (Var n)) : mixS σ σ = σ := by
  funext v; simp [mixS]

theorem rsplit_eval (t : Term (Var n)) (ωL ωR : State (Var n)) :
    RTerm.eval (rsplit t) (ωL, ωR) = Term.eval t (mixS ωL ωR) := by
  induction t with
  | var v =>
      rcases v with ⟨s, i⟩
      cases s <;> simp [rsplit, RTerm.eval, mixS, Term.eval]
  | const c => simp [rsplit, RTerm.eval, Term.eval]
  | binop op a b iha ihb => simp [rsplit, RTerm.eval, Term.eval, iha, ihb]

theorem sat_canonInvM_bi (g : Term (Var n)) (gs : List (Term (Var n))) (ωL ωR : State (Var n)) :
    RFormula.sat (canonInvM g gs) (ωL, ωR) ↔ Formula.sat (FM g gs) (mixS ωL ωR) := by
  induction gs with
  | nil =>
      simp [canonInvM, FM, canonInv, RFormula.sat, rsplit_eval, RTerm.eval, Term.eval,
        CompOp.interp]
  | cons g' rest ih =>
      show RFormula.sat (canonInv g') (ωL, ωR) ∧ RFormula.sat (canonInvM g rest) (ωL, ωR) ↔
        Formula.sat (invLe g') (mixS ωL ωR) ∧ Formula.sat (FM g rest) (mixS ωL ωR)
      rw [ih]
      simp [canonInv, RFormula.sat, rsplit_eval, RTerm.eval, Term.eval, CompOp.interp]

theorem sat_rbigAnd_bi {fs : List (RFormula (Var n))} {bs : BiState (Var n)} :
    RFormula.sat (rbigAnd fs) bs ↔ ∀ f ∈ fs, RFormula.sat f bs := by
  induction fs with
  | nil => simp [rbigAnd, RFormula.tt, RFormula.sat, Formula.sat]
  | cons f fs ih =>
      show RFormula.sat f bs ∧ RFormula.sat (rbigAnd fs) bs ↔ _
      rw [ih]; simp

theorem sat_modeKeyedR_bi {ul : Var n} {ϕ : ℕ → RFormula (Var n)} {nL : ℕ}
    {ωL ωR : State (Var n)} :
    RFormula.sat (modeKeyedR ul ϕ nL) (ωL, ωR) ↔
      ∀ m < nL, ωL ul = (m : ℝ) → RFormula.sat (ϕ m) (ωL, ωR) := by
  unfold modeKeyedR
  rw [sat_rbigAnd_bi]
  constructor
  · intro h m hm hul
    have := h _ (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩)
    rw [RFormula_sat_imp] at this
    exact this (by simpa [RFormula.sat, sat_modeIs] using hul)
  · intro h f hf
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hf
    rw [RFormula_sat_imp]
    intro hul
    exact h m (List.mem_range.mp hm) (by simpa [RFormula.sat, sat_modeIs] using hul)

theorem sat_psiK_bi {ul : Var n} {ϕ : ℕ → RFormula (Var n)} {nL : ℕ}
    {domL domR : Formula (Var n)} {BkR : RFormula (Var n)} {ωL ωR : State (Var n)} :
    RFormula.sat (psiK ul ϕ nL domL domR BkR) (ωL, ωR) ↔
      RFormula.sat (modeKeyedR ul ϕ nL) (ωL, ωR) ∧
        (Formula.sat domL ωL ∧ Formula.sat domR ωR) ∧ RFormula.sat BkR (ωL, ωR) ∧
        Formula.sat (mvValid ul nL) ωL := by
  simp only [psiK, envLR, ulValidL, RFormula.sat]
  tauto

/-! ## Eliminating the claim at a diagonal bi-state -/

/-- **The claim, used once.** At `(σ, σ)` with the antecedent, every left run from `σ` has a right
run from `σ` landing in the post-condition (left end state on the left). -/
theorem t3_elim {L R : Program (Var n)} {ψ : RFormula (Var n)}
    (h : RFormula.rvalid (theorem3Form L R ψ)) (σ : State (Var n))
    (hpre : RFormula.sat ψ (σ, σ)) {νL : State (Var n)}
    (hL : Program.sem (Program.star L) σ νL) :
    ∃ μR, Program.sem (Program.star R) σ μR ∧ RFormula.sat ψ (νL, μR) := by
  have h1 := (RFormula_sat_imp _ _ _).mp (h (σ, σ)) hpre
  have h2 : RFormula.sat (RFormula.rdiamond
      (RProgram.biprog (Program.test Formula.tt) (Program.star R)) ψ) (νL, σ) :=
    h1 (νL, σ) ⟨hL, rfl, trivial⟩
  by_contra hno
  push_neg at hno
  apply h2
  rintro ⟨x, y⟩ ⟨⟨rfl, -⟩, hy⟩ hψ
  exact hno y hy hψ

/-! ## The right automaton binds only right coordinates and its mode variable -/

theorem bv_bigChoiceP_sub {V : Type*} {ps : List (Program V)} {x : V}
    (h : x ∈ (bigChoiceP ps).bv) : ∃ q ∈ ps, x ∈ q.bv := by
  induction ps with
  | nil => simp [bigChoiceP, Program.bv] at h
  | cons a as ih =>
      rcases h with h | h
      · exact ⟨a, List.mem_cons_self, h⟩
      · obtain ⟨q, hq, hx⟩ := ih h; exact ⟨q, List.mem_cons_of_mem _ hq, hx⟩

theorem bv_rightAutomatonBody {G : SearchGraph (Var n)} {mv x : Var n}
    (hsys : ∀ q m, G.modeAt q = some m → m.sys.boundSet ⊆ range Rv)
    (h : x ∈ (rightAutomatonBody G mv).bv) : x = mv ∨ x ∈ range Rv := by
  obtain ⟨st, hst, hx⟩ := bv_bigChoiceP_sub h
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hst
  obtain ⟨q, -, m, hm, rfl⟩ := hst
  simp only [modeStep, Program.bv, Set.empty_union, Set.mem_union] at hx
  rcases hx with hx | hx
  · exact Or.inr (hsys q m hm hx)
  · obtain ⟨e, he, hxe⟩ := bv_bigChoiceP_sub hx
    obtain ⟨e', -, rfl⟩ := List.mem_map.mp he
    simp only [Program.bv, Set.empty_union, Set.mem_singleton_iff] at hxe
    exact Or.inl hxe

theorem grOf_sys_bound {p : PProblem} {pr : String → String → Bool} :
    ∀ q m, (grOf p n pr).modeAt q = some m → m.sys.boundSet ⊆ range Rv := by
  intro q m hm
  rw [grOf_sys hm]
  exact rightBlock_boundSet_sub _ _

/-- A right run of the file's automaton keeps every left coordinate. -/
theorem rightStar_keepsL {p : PProblem} {pr : String → String → Bool} {a : Fin n}
    {x y : State (Var n)}
    (h : Program.sem (Program.star (rightAutomatonBody (grOf p n pr) ((Side.Aux, a) : Var n))) x y)
    (i : Fin n) : y (Side.L, i) = x (Side.L, i) := by
  refine (Program.bound_effect _ h (Side.L, i) ?_).symm
  intro hb
  rcases bv_rightAutomatonBody grOf_sys_bound hb with h1 | ⟨j, hj⟩
  · simp at h1
  · simp [Rv] at hj

/-! ## Rows -/

theorem sat_FM_iff_mem (cs : List (Term (Var n))) (ν : State (Var n)) :
    Formula.sat (FM (cs.headD (Term.const 0)) cs.tail) ν ↔ ∀ c ∈ cs, Term.eval c ν ≤ 0 := by
  rw [sat_FM_iff]
  rcases cs with _ | ⟨c, cs⟩
  · simp [Term.eval]
  · rfl

theorem sat_FRow_iff {p : PProblem} {l : ℕ} {ν : State (Var n)} :
    Formula.sat (FRow p n l) ν ↔ ∀ c ∈ comps p n l, Term.eval c ν ≤ 0 :=
  sat_FM_iff_mem _ ν

theorem comps_mem_fv {p : PProblem} {l : ℕ} {G : Term (Var n)} (hG : G ∈ comps p n l) :
    G.fv ⊆ range Lv ∪ range Rv := by
  refine comps_fv_any (p := p) (n := n) l G ?_
  unfold g gs
  rcases hc : comps p n l with _ | ⟨c, cs⟩
  · rw [hc] at hG; simp at hG
  · rw [hc] at hG; simpa using hG

theorem FRow_fv {p : PProblem} {l : ℕ} : (FRow p n l).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  by_contra hc
  exact notMem_FM_fv (fun g' hg' hx => hc (comps_fv_any (p := p) (n := n) l g' hg' hx)) hv

theorem comps_of_some {p : PProblem} {l : ℕ} {cs : List (ITerm n)}
    (h : Oracle.invComponents (vars p) n (rowOf p l) = some cs) :
    comps p n l = cs.map ITerm.toHost := by
  simp [comps, hostComps, h]

theorem FRow_of_compsQ {p : PProblem} {l : ℕ} {s : Var n → ℚ}
    (h : compsQ p n (rowOf p l) s = true) : Formula.sat (FRow p n l) (castQ s) := by
  rw [sat_FRow_iff]
  intro c hc
  unfold compsQ at h
  rcases hcs : Oracle.invComponents (vars p) n (rowOf p l) with _ | cs
  · simp [comps, hostComps, hcs] at hc
  · rw [comps_of_some hcs] at hc
    rw [hcs] at h
    simp only [Option.map_some, Option.getD_some, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    rw [ITerm.evalQ_toHost]
    exact_mod_cast h c' hc'

/-! ## The witness state -/

theorem castQ_update (s : Var n → ℚ) (v : Var n) (r : ℚ) :
    castQ (Function.update s v r) = Function.update (castQ s) v (r : ℝ) := by
  funext x
  by_cases hx : x = v
  · subst hx; simp [castQ]
  · simp [castQ, Function.update_of_ne hx]

section Witness

variable (p : PProblem) (cX : EvolStrengtheningX) (a b c : Fin n) (w : RefWitE)

/-- The witness, the switched state, the left end state (real). -/
noncomputable def σW : State (Var n) := castQ (witState n a c w)
noncomputable def σS : State (Var n) := castQ (witSwitch n c w (witState n a c w))
noncomputable def σP : State (Var n) := castQ (witPost n b c w (witState n a c w))

variable {p cX a b c w}

theorem σW_L (i : Fin n) : σW a c w (Side.L, i) = ((w.wL.getD i.val 0 : ℚ) : ℝ) := rfl

theorem σW_aux_c (hca : c ≠ a) : σW a c w (Side.Aux, c) = (w.u : ℝ) := by
  simp [σW, castQ, witState, hca]

theorem σW_aux_a : σW a c w (Side.Aux, a) = (w.q0 : ℝ) := by
  simp [σW, castQ, witState]

theorem σS_eq : σS a c w = Function.update (σW a c w) (Side.Aux, c) (w.m : ℝ) := by
  simp [σS, σW, witSwitch, castQ_update]

theorem σP_eq : σP a b c w = Function.update (σS a c w) (Side.Aux, b) 0 := by
  simp [σP, σS, witPost, castQ_update]

theorem σP_L (i : Fin n) : σP a b c w (Side.L, i) = σW a c w (Side.L, i) := by
  rw [σP_eq, σS_eq]
  simp [Function.update_apply]

theorem σP_aux_c (hcb : c ≠ b) : σP a b c w (Side.Aux, c) = (w.m : ℝ) := by
  rw [σP_eq, σS_eq]
  simp [Function.update_apply, hcb]

/-- The antecedent facts, unpacked. -/
structure PreFacts (p : PProblem) (cX : EvolStrengtheningX) (a b c : Fin n) (w : RefWitE) : Prop where
  hu : w.u < nL p
  hm : w.m ∈ (nextL p).getD w.u []
  hq0 : w.q0 < nR p
  hrow : Formula.sat (FRow p n w.u) (σW a c w)
  hdomL : Formula.sat (domL p n) (σW a c w)
  hdomR : Formula.sat (domR p n) (σW a c w)
  hguardR : Formula.sat (guardR p n w.q0) (σW a c w)
  hcuts : Formula.sat (cuts p n cX w.q0) (σW a c w)
  hguardL : Formula.sat (guardL p n w.m) (σW a c w)
  hguardL' : Formula.sat (guardL p n w.m) (σS a c w)
  hdomL' : Formula.sat (domL p n) (σP a b c w)

theorem preFacts_of (h : preOK p n cX a b c w = true) : PreFacts p cX a b c w := by
  simp only [preOK, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, List.all_eq_true]
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu, hm⟩, hq0⟩, hrow⟩, hdL⟩, hdR⟩, hgR⟩, hcut⟩, hgL⟩, hgL'⟩, hdL'⟩ := h
  refine ⟨hu, hm, hq0, FRow_of_compsQ hrow, (optQ_iff _ _).mpr hdL, (optQ_iff _ _).mpr hdR,
    (optQ_iff _ _).mpr hgR, ?_, (optQ_iff _ _).mpr hgL, (optQ_iff _ _).mpr hgL',
    (optQ_iff _ _).mpr hdL'⟩
  rw [cuts, sat_cutF]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact (optQ_iff _ _).mpr (hcut y hy)

/-! ## The left run -/

theorem left_run (hpf : PreFacts p cX a b c w) (hca : c ≠ a) (hcb : c ≠ b) (dt : ℝ)
    (hdt : 0 ≤ dt) :
    Program.sem (Program.star (leftAutomatonBody (leftAutOf p n ((Side.Aux, b) : Var n) dt)
      ((Side.Aux, c) : Var n))) (σW a c w) (σP a b c w) := by
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
    refine ⟨σS a c w, ⟨rfl, hpf.hguardL'⟩, σP a b c w, ?_, rfl, trivial⟩
    refine ⟨σP a b c w, ?_, σP a b c w, sem_ode_zero _ _ hpf.hdomL', rfl, ?_⟩
    · rw [sem_assign, σP_eq]
      refine ⟨by simp [Term.eval], fun y hy => ?_⟩
      simp [Function.update_of_ne hy]
    · rw [sat_clkGuard, σP_eq]; simpa using hdt

/-! ## The claim's post-condition at the witness's runs -/

/-- The claim's loop invariant of the mode-keyed form at the cover's pruning `pr`. -/
noncomputable def psiKOf (p : PProblem) (cX : EvolStrengtheningX) (pr : String → String → Bool)
    (a b c : Fin n) (dt : ℝ) : RFormula (Var n) :=
  psiK ((Side.Aux, c) : Var n) (ϕRow p n) (leftAutOf p n ((Side.Aux, b) : Var n) dt).numModes
    (domL p n) (domR p n)
    (mvRegionR ((Side.Aux, a) : Var n) (gregion p n cX Formula.tt) (grOf p n pr).modes.length)

theorem pre_sat (hpf : PreFacts p cX a b c w) (hca : c ≠ a) (pr : String → String → Bool)
    (dt : ℝ) : RFormula.sat (psiKOf p cX pr a b c dt) (σW a c w, σW a c w) := by
  unfold psiKOf
  rw [sat_psiK_bi]
  refine ⟨?_, ⟨hpf.hdomL, hpf.hdomR⟩, ?_, ?_⟩
  · rw [sat_modeKeyedR_bi]
    intro m' _ hul
    rw [σW_aux_c hca] at hul
    have hm' : m' = w.u := by exact_mod_cast hul.symm
    subst hm'
    show RFormula.sat (canonInvM (g p n w.u) (gs p n w.u)) _
    rw [sat_canonInvM_bi, mixS_self]
    exact hpf.hrow
  · show Formula.sat (mvRegion _ _ _) (σW a c w)
    rw [sat_mvRegion]
    exact ⟨w.q0, by rw [grOf_len]; exact hpf.hq0, σW_aux_a, hpf.hguardR, hpf.hcuts, trivial⟩
  · show Formula.sat (mvValid _ _) (σW a c w)
    rw [sat_mvValid]
    exact ⟨w.u, by rw [leftAutOf_numModes]; exact hpf.hu, σW_aux_c hca⟩

/-- What the post-condition at `(νL, μR)` gives at `μR` itself: the entered row, the right
envelope, a right mode with its guard and kept atoms. -/
theorem post_facts (hpf : PreFacts p cX a b c w) (hcb : c ≠ b) {pr : String → String → Bool}
    {dt : ℝ} {μR : State (Var n)}
    (hR : Program.sem (Program.star (rightAutomatonBody (grOf p n pr) ((Side.Aux, a) : Var n)))
      (σW a c w) μR)
    (hψ : RFormula.sat (psiKOf p cX pr a b c dt) (σP a b c w, μR)) :
    Formula.sat (FRow p n w.m) μR ∧ Formula.sat (domR p n) μR ∧
      ∃ q < nR p, Formula.sat (guardR p n q) μR ∧ Formula.sat (cuts p n cX q) μR := by
  have hmL : w.m < nL p := nextL_lt w.u hpf.hu w.m hpf.hm
  unfold psiKOf at hψ
  rw [sat_psiK_bi] at hψ
  obtain ⟨hK, ⟨-, hdR⟩, hB, -⟩ := hψ
  rw [sat_modeKeyedR_bi] at hK
  have hrow := hK w.m (by rw [leftAutOf_numModes]; exact hmL) (σP_aux_c hcb)
  change RFormula.sat (canonInvM (g p n w.m) (gs p n w.m)) _ at hrow
  rw [sat_canonInvM_bi] at hrow
  change Formula.sat (FRow p n w.m) _ at hrow
  have heq : EqOn (mixS (σP a b c w) μR) μR (FRow p n w.m).fv := by
    intro v hv
    rcases FRow_fv hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp only [mixS, Lv]
      rw [if_neg (by simp), σP_L, rightStar_keepsL hR]
    · simp [mixS, Rv]
  rw [Formula.coincidence _ heq] at hrow
  change Formula.sat (mvRegion _ _ _) μR at hB
  rw [sat_mvRegion, grOf_len] at hB
  obtain ⟨q, hq, -, hg, hc, -⟩ := hB
  exact ⟨hrow, hdR, q, hq, hg, hc⟩

end Witness

/-! ## The query pins -/

theorem sat_fixLeft (wL : List ℚ) (x : State (Var n)) :
    Formula.sat (fixLeft n wL).toHost x ↔ ∀ i : Fin n, x (Side.L, i) = ((wL.getD i.val 0 : ℚ) : ℝ) := by
  unfold fixLeft
  rw [sat_foldl_and]
  simp [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval]

theorem noPartner_sound {p : PProblem} {cX : EvolStrengtheningX} {m q : ℕ} {wL : List ℚ}
    {Q : IForm n}
    (h : noPartnerQueryOf (vars p) n (rowOf p m) (mRof p 0) (mRof p q)
      (cutAtomsOfX cX.R (mRof p q).name) wL = some Q) {x : State (Var n)}
    (hL : ∀ i : Fin n, x (Side.L, i) = ((wL.getD i.val 0 : ℚ) : ℝ))
    (hrow : Formula.sat (FRow p n m) x) (hdR : Formula.sat (domR p n) x)
    (hg : Formula.sat (guardR p n q) x) (hc : Formula.sat (cuts p n cX q) x) :
    Formula.sat Q.toHost x := by
  unfold noPartnerQueryOf at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at h
  obtain ⟨cs, hcs, ev, hev, gR, hgR, cut, hcut, rfl⟩ := h
  simp only [IForm.toHost, Formula.sat]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · unfold compsConj
    rw [sat_foldl_le]
    refine ⟨(sat_fixLeft wL x).mpr hL, fun c hc => ?_⟩
    rw [sat_FRow_iff, comps_of_some hcs] at hrow
    exact hrow _ (List.mem_map_of_mem hc)
  · simpa [domR, hostEvolve, hev] using hdR
  · simpa [guardR, hostGuard, hgR] using hg
  · exact (sat_cutOfAtoms hcut x).mpr ((sat_cutF _ _).mp hc)

theorem lie_sub_const (c : ℝ) (G : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) :
    lieDeriv (Term.binop .sub (Term.const c) G) fL fR lam
      = lieDeriv (Term.binop .sub (Term.const 0) G) fL fR lam := rfl

/-- The rigidity query's `unsat`: the right field of mode `q` does not decrease `g` inside the
right evolve domain. -/
theorem rigid_sound {p : PProblem} {q : ℕ} {g : ITerm n} {Q : IForm n}
    (h : rigidQueryOf (vars p) n g (mRof p 0) (mRof p q) = some Q)
    (hz : z3solve Q.toHost = Verdict.unsat) (x : State (Var n))
    (hx : Formula.sat (domR p n) x) :
    Term.eval (lieDeriv (Term.binop .sub (Term.const 0) g.toHost) (fun _ => Term.const 0)
      (fR p n q) (Term.const 1)) x ≤ 0 := by
  unfold rigidQueryOf at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq]
    at h
  obtain ⟨f, hf, ev, hev, rfl⟩ := h
  have hfR : fR p n q = fun j => (f j).toHost := by
    funext j; simp [fR, hostDyn, hf]
  have hdom : domR p n = ev.toHost := by simp [domR, hostEvolve, hev]
  by_contra hgt
  rw [not_le] at hgt
  apply z3_unsat_sound hz x
  simp only [IForm.toHost, Formula.sat, CompOp.interp, Bridge.ownLie, ilieDeriv_toHost]
  refine ⟨hdom ▸ hx, ?_⟩
  rw [hfR] at hgt
  simpa [ITerm.toHost, Term.eval] using hgt

/-- **Right rigidity.** If no right mode's field decreases `G` inside the right evolve domain,
`G` never decreases along a run of the right automaton, whatever its pruning. -/
theorem rigid_star {p : PProblem} {pr : String → String → Bool} {a : Fin n} {G : Term (Var n)}
    (hGfv : G.fv ⊆ range Lv ∪ range Rv)
    (hlie : ∀ q < nR p, ∀ x, Formula.sat (domR p n) x →
      Term.eval (lieDeriv (Term.binop .sub (Term.const 0) G) (fun _ => Term.const 0) (fR p n q)
        (Term.const 1)) x ≤ 0)
    {x y : State (Var n)}
    (h : Program.sem (Program.star (rightAutomatonBody (grOf p n pr) ((Side.Aux, a) : Var n))) x y) :
    Term.eval G x ≤ Term.eval G y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
      refine ih.trans ?_
      obtain ⟨st, hst, hsem⟩ := bigChoiceP_sem_forward hstep
      simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hst
      obtain ⟨q, -, m, hm, rfl⟩ := hst
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm
      obtain ⟨x1, ⟨rfl, -⟩, x2, hode, hedge⟩ := hsem
      set c0 := Term.eval G _ with hc0
      have hbox := DI_nonstrict_domain (rightBlock_wellFormed (fR p n q) (Term.const 1))
        (term_differentiable (Term.binop .sub (Term.const c0) G)) (fun z hz => by
          rw [lie_rightBlock, ← lieDeriv_correct, lie_sub_const]
          exact hlie q hq z hz) (by simp [Term.eval, AOp.interp, hc0]) _ hode
      have hx2 : c0 ≤ Term.eval G x2 := by
        simpa [Term.eval, AOp.interp] using hbox
      refine hx2.trans (le_of_eq ?_)
      obtain ⟨e, he, hsem_e⟩ := bigChoiceP_sem_forward hedge
      obtain ⟨e', -, rfl⟩ := List.mem_map.mp he
      obtain ⟨x3, ⟨rfl, -⟩, -, hfr⟩ := hsem_e
      refine Term.coincidence G (fun v hv => (hfr v ?_).symm)
      rcases hGfv hv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp [Lv, Rv]

/-! ## The unclocked claim (the pre-W3 `keyedClaim`), the refutations' target -/

/-- The mode-keyed claim over the UNCLOCKED guarded right automaton (`rightAutomatonBody`; mode
variable `(Aux, a)`, left clock `(Aux, b)`, left mode variable `(Aux, c)`): the pre-W3
`keyedClaim`. The clocked claim implies it (`keyedClaim_to_unclocked`), so a refutation of this
claim refutes the clocked one by contraposition. -/
def keyedClaimU (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
    (reg : Formula (Var n)) (a b c : Fin n) (dt : ℝ) : Prop :=
  RFormula.rvalid (theorem3Form
    (leftAutomatonBody (leftAutOf p n ((Side.Aux, b) : Var n) dt) ((Side.Aux, c) : Var n))
    (rightAutomatonBody (grOf p n (prunedOf cov)) ((Side.Aux, a) : Var n))
    (psiK ((Side.Aux, c) : Var n) (ϕRow p n) (leftAutOf p n ((Side.Aux, b) : Var n) dt).numModes
      (domL p n) (domR p n)
      (mvRegionR ((Side.Aux, a) : Var n) (gregion p n cX reg) (grOf p n (prunedOf cov)).modes.length)))

/-! ## W4: the clocked claim implies the unclocked one -/

/-- Theorem 3's ∀∃ form is monotone in the right program up to a transport of the
post-condition: when every right run of `R'` landing in `ψ` yields a right run of `R` landing
in `ψ` (same left end state), the claim over `R'` gives the claim over `R`. -/
theorem t3_right_mono {L R R' : Program (Var n)} {ψ : RFormula (Var n)}
    (h : RFormula.rvalid (theorem3Form L R' ψ))
    (hR : ∀ {ωL ν μ : State (Var n)}, Program.sem (Program.star R') ν μ →
      RFormula.sat ψ (ωL, μ) →
      ∃ μ', Program.sem (Program.star R) ν μ' ∧ RFormula.sat ψ (ωL, μ')) :
    RFormula.rvalid (theorem3Form L R ψ) := by
  rintro ⟨ωL, ωR⟩
  have h1 := h (ωL, ωR)
  unfold theorem3Form at h1 ⊢
  rw [RFormula_sat_imp, rsat_faShape_iff] at h1 ⊢
  intro hpre a' ha'
  obtain ⟨μ, hμ, hψ⟩ := h1 hpre a' ha'
  exact hR hμ hψ

/-- A right-only formula reads the same at the right copy. -/
theorem sat_R_congr {f : Formula (Var n)} (hf : f.fv ⊆ range Rv) {x y : State (Var n)}
    (hR : ∀ i, y (Side.R, i) = x (Side.R, i)) : Formula.sat f y ↔ Formula.sat f x :=
  Formula.coincidence f (fun v hv => by obtain ⟨i, rfl⟩ := hf hv; exact hR i)

/-- A formula over `Lv ∪ Rv` reads the same at the mixes with two right states agreeing on
`Rv`. -/
theorem sat_mixS_congr {f : Formula (Var n)} (hf : f.fv ⊆ range Lv ∪ range Rv)
    {ωL μ μ' : State (Var n)} (hR : ∀ i, μ' (Side.R, i) = μ (Side.R, i)) :
    Formula.sat f (mixS ωL μ') ↔ Formula.sat f (mixS ωL μ) :=
  Formula.coincidence f (fun v hv => by
    rcases hf hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp [mixS, Lv]
    · simp [mixS, Rv, hR])

/-- `Keyed.grOf_Rv` from `namesOK` alone: every declared right mode's system and domain read
right coordinates only. -/
theorem grOf_Rv_of {p : PProblem} (hnm : namesOK p = true) {pr : String → String → Bool} :
    ∀ q m, (grOf p n pr).modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm y hy
  rw [grOf_sys hm, grOf_dom hm] at hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fR p n q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fR p n q) (Term.const 1) (fR_fv hnm q) (by simp [Term.fv]) hy
  · exact domR_fv hnm hy

/-- The right region reads right coordinates only (`namesOK`, `cutsOK`, `reg` over `Rv`). -/
theorem gregion_fv_of {p : PProblem} {cX : EvolStrengtheningX} (hnm : namesOK p = true)
    (hcu : cutsOK p n cX = true) {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv) (q : ℕ) :
    (gregion p n cX reg q).fv ⊆ range Rv :=
  regionG_fv_sub (guardR_fv hnm q) (fun v hv => by
    rcases hv with hv | hv
    · exact cutF_fv_sub (cutPairsX_fvF_R (atomsWF_R_any hcu q)) hv
    · exact hregR hv)

/-- **Erase the right clock** `(Aux, d)` from a run of the file's clocked right automaton: the
hygiene facts (`(Aux, d)` in no right system, domain or guard) come from `namesOK`. The erased
run agrees with the clocked one on `Rv` and on the right mode variable. -/
theorem erase_right_clock {p : PProblem} (hnm : namesOK p = true) {pr : String → String → Bool}
    {a d : Fin n} (hda : d ≠ a) {dt : ℝ} {ν μ : State (Var n)}
    (h : Program.sem (Program.star (rightAutomatonBodyC (grOf p n pr) ((Side.Aux, a) : Var n)
      ((Side.Aux, d) : Var n) dt)) ν μ) :
    ∃ μ', Program.sem (Program.star (rightAutomatonBody (grOf p n pr) ((Side.Aux, a) : Var n)))
        ν μ' ∧
      (∀ i, μ' (Side.R, i) = μ (Side.R, i)) ∧ μ' (Side.Aux, a) = μ (Side.Aux, a) := by
  obtain ⟨μ', hμ', hagree⟩ := star_bodyC_to_body (grOf p n pr) _ _ dt
    (by simp [Prod.ext_iff, hda.symm])
    (fun q m hm hx => aux_notin_range_Rv d (grOf_Rv_of hnm q m hm (vars_ode_sub _ _ (Or.inl hx))))
    (guardsFresh_of_right _ d (grOf_guardsRight hnm)) h
  exact ⟨μ', hμ', fun i => hagree _ (by simp), hagree _ (by simp [Prod.ext_iff, hda.symm])⟩

/-- **The clocked claim implies the unclocked one** (mode-keyed form). Fewer right runs make
the claim harder: a clocked right run is erased to an unclocked one (`erase_right_clock`), and
the post-condition reads the right state only on `Rv` and on the right mode variable
`(Aux, a)`, never on the clock `(Aux, d)`. Only `d ≠ a` is needed. -/
theorem keyedClaim_to_unclocked {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE}
    (hnm : namesOK p = true) (hcu : cutsOK p n cX = true) {reg : Formula (Var n)}
    (hregR : reg.fv ⊆ range Rv) {a b c d : Fin n} (hda : d ≠ a) {dt : ℝ}
    (h : keyedClaim p n cX cov reg a b c d dt) : keyedClaimU p n cX cov reg a b c dt := by
  unfold keyedClaim at h
  unfold keyedClaimU
  refine t3_right_mono h ?_
  intro ωL ν μ hμ hψ
  obtain ⟨μ', hμ', hR, hA⟩ := erase_right_clock hnm hda hμ
  refine ⟨μ', hμ', ?_⟩
  rw [sat_psiK_bi] at hψ ⊢
  obtain ⟨hK, ⟨hdL, hdR⟩, hB, hV⟩ := hψ
  refine ⟨?_, ⟨hdL, (sat_R_congr (domR_fv hnm) hR).mpr hdR⟩, ?_, hV⟩
  · rw [sat_modeKeyedR_bi] at hK ⊢
    intro m hm hul
    have hrow := hK m hm hul
    change RFormula.sat (canonInvM (g p n m) (gs p n m)) _ at hrow ⊢
    rw [sat_canonInvM_bi] at hrow ⊢
    change Formula.sat (FRow p n m) _ at hrow ⊢
    exact (sat_mixS_congr FRow_fv hR).mpr hrow
  · change Formula.sat (mvRegion _ _ _) μ at hB
    show Formula.sat (mvRegion _ _ _) μ'
    rw [sat_mvRegion] at hB ⊢
    obtain ⟨q, hq, hmv, hreg⟩ := hB
    exact ⟨q, hq, by rw [hA]; exact hmv,
      (sat_R_congr (gregion_fv_of hnm hcu hregR q) hR).mpr hreg⟩

/-! ## The refutations -/

section Refute

variable {p : PProblem} {cX : EvolStrengtheningX} {a b c : Fin n} {w : RefWitE}

/-- **Kind C, mode-keyed.** From the witness's kernel-decided facts and the no-partner `unsat`s,
the claim is false for every cover record (every pruning), every `dt ≥ 0`. -/
theorem refute_keyed_C (hpre : preOK p n cX a b c w = true) (hk : w.kind = "C")
    (hv : RefVerdicts p n cX w) (hca : c ≠ a) (hcb : c ≠ b) (dt : ℝ) (hdt : 0 ≤ dt)
    (cov : CoverEmitE) : ¬ keyedClaimU p n cX cov Formula.tt a b c dt := by
  intro hclaim
  have hpf := preFacts_of hpre
  obtain ⟨μR, hR, hψ⟩ := t3_elim hclaim (σW a c w) (pre_sat hpf hca (prunedOf cov) dt)
    (left_run hpf hca hcb dt hdt)
  obtain ⟨hrow, hdR, q, hq, hgq, hcq⟩ := post_facts hpf hcb hR hψ
  obtain ⟨gs, hgs, hok⟩ := hv
  simp only [refGroups, hk, beq_self_eq_true, if_true, noPartnerGroups] at hgs
  obtain ⟨y, hy, hyq⟩ := mapM_range hgs q hq
  obtain ⟨Q, hQ, rfl⟩ := Option.map_eq_some_iff.mp hyq
  obtain ⟨Q', hQ', hz⟩ := hok _ hy
  rw [List.mem_singleton] at hQ'
  subst hQ'
  refine z3_unsat_sound hz μR (noPartner_sound hQ (fun i => ?_) hrow hdR hgq hcq)
  rw [rightStar_keepsL hR, σW_L]

/-- **Kind A, mode-keyed.** Component `k` of the entered row is positive at the witness and no
right field decreases it inside the right evolve domain: the claim is false for every cover
record (every pruning), every `dt ≥ 0`. -/
theorem refute_keyed_A (hpre : preOK p n cX a b c w = true) (hk : w.kind ≠ "C")
    (hpos : compPosQ p n (rowOf p w.m) w.k (witState n a c w) = true)
    (hv : RefVerdicts p n cX w) (hca : c ≠ a) (hcb : c ≠ b) (dt : ℝ) (hdt : 0 ≤ dt)
    (cov : CoverEmitE) : ¬ keyedClaimU p n cX cov Formula.tt a b c dt := by
  intro hclaim
  have hpf := preFacts_of hpre
  obtain ⟨μR, hR, hψ⟩ := t3_elim hclaim (σW a c w) (pre_sat hpf hca (prunedOf cov) dt)
    (left_run hpf hca hcb dt hdt)
  obtain ⟨hrow, -, -⟩ := post_facts hpf hcb hR hψ
  obtain ⟨gs, hgs, hok⟩ := hv
  have hk' : (w.kind == "C") = false := by simpa using hk
  simp only [refGroups, hk', Bool.false_eq_true, if_false, rigidGroups, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at hgs
  obtain ⟨cs, hcs, gI, hgI, hgs⟩ := hgs
  have hmem : gI.toHost ∈ comps p n w.m := by
    rw [comps_of_some hcs]
    exact List.mem_map_of_mem (List.mem_of_getElem? hgI)
  have hposσ : 0 < Term.eval gI.toHost (σW a c w) := by
    unfold compPosQ at hpos
    rw [hcs] at hpos
    simp only [Option.bind_some, hgI, Option.map_some, Option.getD_some, decide_eq_true_eq]
      at hpos
    rw [σW, ITerm.evalQ_toHost]
    exact_mod_cast hpos
  have hmono := rigid_star (comps_mem_fv hmem) (fun q hq x hx => by
    obtain ⟨y, hy, hyq⟩ := mapM_range hgs q hq
    obtain ⟨Q, hQ, rfl⟩ := Option.map_eq_some_iff.mp hyq
    obtain ⟨Q', hQ', hz⟩ := hok _ hy
    rw [List.mem_singleton] at hQ'
    subst hQ'
    exact rigid_sound hQ hz x hx) hR
  rw [sat_FRow_iff] at hrow
  linarith [hrow _ hmem]

/-- **Kind C, mode-keyed, the clocked claim** (W4): `refute_keyed_C` by contraposition through
`keyedClaim_to_unclocked`; `(Aux, d)` is the right clock. -/
theorem refute_keyed_C_clocked (hpre : preOK p n cX a b c w = true) (hk : w.kind = "C")
    (hv : RefVerdicts p n cX w) (hnm : namesOK p = true) (hcu : cutsOK p n cX = true)
    (hca : c ≠ a) (hcb : c ≠ b) (d : Fin n) (hda : d ≠ a) (dt : ℝ) (hdt : 0 ≤ dt)
    (cov : CoverEmitE) : ¬ keyedClaim p n cX cov Formula.tt a b c d dt :=
  fun h => refute_keyed_C hpre hk hv hca hcb dt hdt cov
    (keyedClaim_to_unclocked hnm hcu (by simp [Formula.fv]) hda h)

/-- **Kind A, mode-keyed, the clocked claim** (W4): `refute_keyed_A` by contraposition through
`keyedClaim_to_unclocked`; `(Aux, d)` is the right clock. -/
theorem refute_keyed_A_clocked (hpre : preOK p n cX a b c w = true) (hk : w.kind ≠ "C")
    (hpos : compPosQ p n (rowOf p w.m) w.k (witState n a c w) = true)
    (hv : RefVerdicts p n cX w) (hnm : namesOK p = true) (hcu : cutsOK p n cX = true)
    (hca : c ≠ a) (hcb : c ≠ b) (d : Fin n) (hda : d ≠ a) (dt : ℝ) (hdt : 0 ≤ dt)
    (cov : CoverEmitE) : ¬ keyedClaim p n cX cov Formula.tt a b c d dt :=
  fun h => refute_keyed_A hpre hk hpos hv hca hcb dt hdt cov
    (keyedClaim_to_unclocked hnm hcu (by simp [Formula.fv]) hda h)

end Refute

end Emitted
end RelCertifier
