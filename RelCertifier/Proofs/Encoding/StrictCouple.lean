/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The cut-narrowed couplings at strict rows (extension `strict-atoms`)

Mirrors of the per-pairing anchor preservation for a row read through its strictness mask:

* `orderTag`: the strata-ordered flagged components (the cover's `order` over `tagS`), whose
  plain components are exactly the existing ordered components (`orderTag_map_snd`), so every
  query is the existing string;
* `VerdXCoreS`, `modalVerdXS`: the joint flow pack, a strict component's group being
  [route A, route B]; with an all-false mask it is `VerdXCore`/`modalVerdX`
  (`modalVerdXS_allFalse`);
* `couple_box_cutXS` (`SyncSwitch.couple_box_cutX`), `segPresAllS_dyn` and `couple_box_dynS`
  (`ReplayDyn`): the anchor `FMS g (gs ++ atomTerms) m` is a box invariant of the joint flow
  and of the frozen-left reposition flow. The reposition pack is UNCHANGED (route A for every
  component, which preserves `< 0`, `flow_cert_sound_lt`).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.SyncSwitch
import RelCertifier.Proofs.Encoding.ReplayDyn
import RelCertifier.Proofs.Encoding.StrictInv
import RelCertifier.Proofs.Soundness.StrictCover
import RelCertifier.Trusted.InvStrictFlags

namespace RelCertifier
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

variable {n : ℕ}

/-! ## The strata-ordered flagged components -/

theorem tagS_length (cs : List (Term (Var n))) (m : List Bool) : (tagS cs m).length = cs.length := by
  rw [← tagS_map_snd cs m, List.length_map, tagS_map_snd]

theorem tagS_getD_snd (cs : List (Term (Var n))) (m : List Bool) (i : ℕ) (d : Bool × Term (Var n)) :
    ((tagS cs m).getD i d).2 = cs.getD i d.2 := by
  induction cs generalizing m i with
  | nil => simp
  | cons c cs ih =>
      cases i with
      | zero => simp
      | succ i => simpa using ih m.tail i

/-- The flagged components of a row in the cover's strata order. -/
def orderTag (comps : List (Term (Var n))) (mask : List Bool) (order : List ℕ) :
    List (Bool × Term (Var n)) :=
  order.map (fun i => (tagS comps mask).getD i (false, Term.const 0))

theorem orderTag_map_snd (comps : List (Term (Var n))) (mask : List Bool) (order : List ℕ) :
    (orderTag comps mask order).map Prod.snd = order.map (fun i => comps.getD i (Term.const 0)) := by
  unfold orderTag
  rw [List.map_map]
  exact List.map_congr_left (fun i _ => tagS_getD_snd comps mask i _)

/-- With an all-false mask the ordered flagged list is the ordered list, all `false`. -/
theorem orderTag_allFalse (comps : List (Term (Var n))) {mask : List Bool}
    (h : ∀ b ∈ mask, b = false) (order : List ℕ) :
    orderTag comps mask order =
      (order.map (fun i => comps.getD i (Term.const 0))).map (fun g => (false, g)) := by
  unfold orderTag
  rw [tagS_allFalse comps h, List.map_map]
  refine List.map_congr_left (fun i _ => ?_)
  show (comps.map (fun c => (false, c))).getD i ((fun c => (false, c)) (Term.const 0)) = _
  rw [List.getD_map]
  rfl

/-- `mem_equiv_of_index_perm` for any element type. -/
theorem mem_equiv_of_index_perm' {α : Type*} (xs : List α) (d : α) (order : List Nat)
    (hperm : order.Perm (List.range xs.length)) :
    ∀ x, x ∈ order.map (fun j => xs.getD j d) ↔ x ∈ xs := by
  intro x
  have hmap : (order.map (fun j => xs.getD j d)).Perm
      ((List.range xs.length).map (fun j => xs.getD j d)) := hperm.map _
  rw [hmap.mem_iff]
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hj
    rw [List.getD_eq_getElem xs _ hj]
    exact List.getElem_mem hj
  · intro hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    refine List.mem_map.mpr ⟨j, List.mem_range.mpr hj, ?_⟩
    rw [List.getD_eq_getElem xs _ hj, hjx]

theorem mem_orderTag_iff (comps : List (Term (Var n))) (mask : List Bool) (order : List ℕ)
    (hperm : order.Perm (List.range comps.length)) (c : Bool × Term (Var n)) :
    c ∈ orderTag comps mask order ↔ c ∈ tagS comps mask := by
  unfold orderTag
  refine mem_equiv_of_index_perm' (tagS comps mask) _ order ?_ c
  rwa [tagS_length]

/-! ## The flagged joint pack -/

/-- The stratified flow pack of one pairing over flagged components: a strict component by
route A or B, the others by any of the three routes (the existing `VerdXCore` queries). -/
def VerdXCoreS (ts : List (Bool × Term (Var n))) (fL fR : Fin n → Term (Var n)) (lam : ℝ)
    (D : Formula (Var n)) : Prop :=
  StrataVerdS fL fR (Term.const lam) D ts

/-- **The suite_v2 modal verdict pack at a strict row** (`modalVerdX` with the row's mask). -/
noncomputable def modalVerdXS (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ)
    (order : List ℕ) (lam : ℝ) (l m : ℕ) : Prop :=
  let vars := p.L.stateVars
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mL := p.L.modes.getD l dm
  let mR := p.R.modes.getD m dm
  let row := (p.invariants.getD invRow ("", PForm.tt)).2
  let ts := orderTag (hostComps vars n row) ((invStrictFlags vars n row).getD []) order
  let base := Formula.and (hostEvolve vars n Side.L mL) (hostEvolve vars n Side.R mR)
  let cL := cutPairsX vars n Side.L (cutAtomsOfX cX.L mL.name)
  let cR := cutPairsX vars n Side.R (cutAtomsOfX cX.R mR.name)
  VerdXCoreS ts (hostDyn vars n Side.L mL) (hostDyn vars n Side.R mR) lam
    (domCutX base cL cR)

/-- **Collapse**: a row without strict atoms gives the existing pack. -/
theorem modalVerdXS_allFalse (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ)
    (order : List ℕ) (lam : ℝ) (l m : ℕ)
    (h : ∀ b ∈ (invStrictFlags p.L.stateVars n
      (p.invariants.getD invRow ("", PForm.tt)).2).getD [], b = false) :
    modalVerdXS p cX n invRow order lam l m ↔ modalVerdX p cX n invRow order lam l m := by
  unfold modalVerdXS modalVerdX VerdXCoreS VerdXCore
  simp only
  rw [orderTag_allFalse _ h, strataVerdS_allFalse]

/-! ## The joint coupling -/

theorem segPresAllS_congr {ts : List (Bool × Term (Var n))} {sys : ODESystem (Var n)}
    {D D' : Formula (Var n)} (hDD : ∀ x, Formula.sat D' x ↔ Formula.sat D x)
    (h : SegPreservesAllOnS ts sys D) : SegPreservesAllOnS ts sys D' := by
  intro ν hν ω hω
  exact h ν hν ω (sem_ode_congr (fun x => hDD x) hω)

/-- **`couple_box_cutX` at a strict row.** The anchor `FMS g (gs ++ atomTerms) m` (flagged row
components, closure atoms) is a box invariant of the joint flow, from the flagged pack. -/
theorem couple_box_cutXS (g : Term (Var n)) (gs : List (Term (Var n))) (m : List Bool)
    (ts : List (Bool × Term (Var n)))
    (cL cR : List (CutAtomP n)) (fL fR : Fin n → Term (Var n)) (lamv : ℝ)
    (domL domR : Formula (Var n)) (hm : m.length ≤ gs.length + 1)
    (hsub1 : ∀ c ∈ ts, c ∈ tagS (g :: gs) m) (hsub2 : ∀ c ∈ tagS (g :: gs) m, c ∈ ts)
    (hiffL : AtomsIff cL) (hiffR : AtomsIff cR)
    (hstayL : AtomsStayC cL (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
    (hstayR : AtomsStayC cR (jointSys fL fR (Term.const lamv)) (Formula.and domL domR))
    (hverd : VerdXCoreS ts fL fR lamv (domCutX (Formula.and domL domR) cL cR)) :
    ∀ σ ω, Formula.sat (FMS g (gs ++ atomTerms cL cR) m) σ →
      Program.sem (Program.ode (jointSys fL fR (Term.const lamv)) (Formula.and domL domR)) σ ω →
      Formula.sat (FMS g (gs ++ atomTerms cL cR) m) ω := by
  intro σ ω hσ hω
  have hnarrow : SegPreservesAllOnS ts (jointSys fL fR (Term.const lamv))
      (domCutX (Formula.and domL domR) cL cR) :=
    segPresAllS_from_strata_verdicts' fL fR (Term.const lamv) _ ts hverd
  have hnarrow' : SegPreservesAllOnS ts (jointSys fL fR (Term.const lamv))
      (Formula.and (Formula.and domL domR) (Formula.and (cutF cL) (cutF cR))) := by
    refine segPresAllS_congr (fun x => ?_) hnarrow
    rw [sat_domCutX]
    simp only [Formula.sat, sat_cutF]
  have hlift := segPresAllS_cut_liftX hiffL hiffR hstayL hstayR hnarrow'
  obtain ⟨hFσ, hatσ⟩ := (sat_FMS_append g gs _ m hm σ).mp hσ
  obtain ⟨hLσ, hRσ⟩ := (atomTerms_iff hiffL hiffR σ).mp hatσ
  have hcompsσ : ∀ c ∈ ts, HoldsAt c.1 c.2 σ :=
    fun c hc => (sat_FMS_iff g gs m σ).mp hFσ c (hsub1 c hc)
  obtain ⟨hcω, hLω, hRω⟩ := hlift σ hLσ hRσ hcompsσ ω hω
  refine (sat_FMS_append g gs _ m hm ω).mpr ⟨(sat_FMS_iff g gs m ω).mpr ?_,
    (atomTerms_iff hiffL hiffR ω).mpr ⟨hLω, hRω⟩⟩
  intro c hc
  exact hcω c (hsub2 c hc)

/-! ## The reposition coupling (the existing route-A pack) -/

/-- The reposition pack gives flagged preservation along the frozen-left right flow, on the
base domain narrowed by the region's half-open part: route A preserves `< 0` as well as `≤ 0`
(whole region: route A for every component; pre-landing region: a strict component's route A
holds over the closure, hence over the half-open part, `covers`). -/
theorem segPresAllS_dyn (pre : Bool) (ts : List (Bool × Term (Var n)))
    (fR : Fin n → Term (Var n)) (D gL : Formula (Var n)) {rg : DynRegion n}
    (hv : VerdDynCore pre (ts.map Prod.snd) fR D gL rg) (hrg : rg.covers (ts.map Prod.fst)) :
    SegPreservesAllOnS ts (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (dynBase pre (rg.dom D) gL) := by
  intro ν hinit
  refine stratified_barrier_endS _ (dynBase pre (rg.dom D) gL) ts ?_ hinit
  intro i hi ν' hν'
  have hcong : ∀ x, Formula.sat (Formula.and (dynBase pre (rg.dom D) gL)
      (bigLe ((ts.take i).map Prod.snd))) x ↔
      Formula.sat (dynDomHost pre (rg.dom D) gL ((ts.map Prod.snd).take i)) x := by
    intro x
    rw [sat_dynDomHost, ← List.map_take]
  refine holds_dom_congr hcong ?_
  have hi' : i < (ts.map Prod.snd).length := by simpa using hi
  have hget : (ts.map Prod.snd)[i] = ts[i].2 := by simp
  cases rg with
  | whole =>
      have hz := z3_unsat_sound (hv i hi')
      rw [hget] at hz
      rcases hb : ts[i].1 with _ | _
      · rw [hb] at hν'
        intro ω hω
        show Term.eval ts[i].2 ω ≤ 0
        exact flow_cert_sound ⟨ts[i].2, fun _ => Term.const 0, fR, Term.const 1,
          dynDomHost pre D gL ((ts.map Prod.snd).take i)⟩ hz hν' ω hω
      · rw [hb] at hν'
        intro ω hω
        show Term.eval ts[i].2 ω < 0
        exact flow_cert_sound_lt ⟨ts[i].2, fun _ => Term.const 0, fR, Term.const 1,
          dynDomHost pre D gL ((ts.map Prod.snd).take i)⟩ hz hν' ω hω
  | pre Bo Bc mask hmono _ =>
      have hwide : ∀ x, Formula.sat (dynDomHost pre (Formula.and D Bo) gL
          ((ts.map Prod.snd).take i)) x →
          Formula.sat (dynDomHost pre (Formula.and D Bc) gL ((ts.map Prod.snd).take i)) x :=
        dynDomHost_mono (D := Formula.and D Bo) (D' := Formula.and D Bc) pre _
          (fun x hx => ⟨hx.1, hmono x hx.2⟩)
      have h := hv i hi'
      rw [hget] at h
      rcases hb : ts[i].1 with _ | _
      · rw [hb] at hν'
        intro ω hω
        show Term.eval ts[i].2 ω ≤ 0
        split_ifs at h with hm
        · exact flow_cert_sound _ (z3_unsat_sound h) hν' ω (sem_ode_dom_mono hwide hω)
        · rcases h with h | h | h
          · exact flow_cert_sound _ (z3_unsat_sound h) hν' ω hω
          · exact flow_cert_sound_strict _ (z3_unsat_sound h) hν' ω hω
          · exact flow_cert_sound_superlevel _ (z3_unsat_sound h) hν' ω hω
      · rw [hb] at hν'
        intro ω hω
        show Term.eval ts[i].2 ω < 0
        have hm : mask.getD i false = true := hrg i (by
          rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp [hb])
        rw [if_pos hm] at h
        exact flow_cert_sound_lt _ (z3_unsat_sound h) hν' ω (sem_ode_dom_mono hwide hω)

/-- **`couple_box_dyn` at a strict row.** -/
theorem couple_box_dynS (pre : Bool) (g : Term (Var n)) (gs : List (Term (Var n)))
    (m : List Bool) (ts : List (Bool × Term (Var n)))
    (cL cR : List (CutAtomP n)) (fR : Fin n → Term (Var n)) (domL domR gL : Formula (Var n))
    {rg : DynRegion n} (hm : m.length ≤ gs.length + 1)
    (hsub1 : ∀ c ∈ ts, c ∈ tagS (g :: gs) m) (hsub2 : ∀ c ∈ tagS (g :: gs) m, c ∈ ts)
    (hiffL : AtomsIff cL) (hiffR : AtomsIff cR) (hLfv : ∀ a ∈ cL, a.2.fv ⊆ range Lv)
    (hgL : gL.fv ⊆ range Lv)
    (hstayR : AtomsStayC cR (jointSys (fun _ => Term.const 0) fR (Term.const 1))
      (dynBase pre (Formula.and domL (rg.dom domR)) gL))
    (hverd : VerdDynCore pre (ts.map Prod.snd) fR (domCutX (Formula.and domL domR) cL cR) gL rg)
    (hrg : rg.covers (ts.map Prod.fst)) :
    ∀ σ ω, Formula.sat (FMS g (gs ++ atomTerms cL cR) m) σ → (pre = true → Formula.sat gL σ) →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR (Term.const 1))
        (Formula.and domL (rg.dom domR))) σ ω →
      Formula.sat (FMS g (gs ++ atomTerms cL cR) m) ω := by
  intro σ ω hσ hgσ hω
  set sys := jointSys (fun _ => Term.const 0) fR (Term.const 1) with hsys
  have hrun : Program.sem (Program.ode sys
      (dynBase pre (Formula.and domL (rg.dom domR)) gL)) σ ω := by
    unfold dynBase
    cases pre with
    | false => simpa using hω
    | true => simpa using frozen_run_narrow hgL hω (hgσ rfl)
  have hnarrow : SegPreservesAllOnS ts sys
      (dynBase pre (rg.dom (domCutX (Formula.and domL domR) cL cR)) gL) :=
    segPresAllS_dyn pre ts fR _ gL hverd hrg
  have hnarrow' : SegPreservesAllOnS ts sys
      (Formula.and (dynBase pre (Formula.and domL (rg.dom domR)) gL)
        (Formula.and (cutF cL) (cutF cR))) := by
    refine segPresAllS_congr (fun x => ?_) hnarrow
    unfold dynBase
    cases rg <;> cases pre <;> simp only [DynRegion.dom, Bool.false_eq_true, if_false, if_true,
      Formula.sat, sat_domCutX, sat_cutF] <;> tauto
  have hlift := segPresAllS_cut_liftX hiffL hiffR
    (atomsStayC_frozenL hiffL hLfv fR (Term.const 1) _) hstayR hnarrow'
  obtain ⟨hFσ, hatσ⟩ := (sat_FMS_append g gs _ m hm σ).mp hσ
  obtain ⟨hLσ, hRσ⟩ := (atomTerms_iff hiffL hiffR σ).mp hatσ
  have hcompsσ : ∀ c ∈ ts, HoldsAt c.1 c.2 σ :=
    fun c hc => (sat_FMS_iff g gs m σ).mp hFσ c (hsub1 c hc)
  obtain ⟨hcω, hLω, hRω⟩ := hlift σ hLσ hRσ hcompsσ ω hrun
  refine (sat_FMS_append g gs _ m hm ω).mpr ⟨(sat_FMS_iff g gs m ω).mpr ?_,
    (atomTerms_iff hiffL hiffR ω).mpr ⟨hLω, hRω⟩⟩
  intro c hc
  exact hcω c (hsub2 c hc)

end RelCertifier
