/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S3 — the face/domain bridge and uniform Picard data

`HExistSegB_of_viability` consumes (i) `hdomsat : faces ≤ 0 → sat domR`, (ii) per-anchor
ball Lipschitz/bound data with ONE `K, L` for every box anchor. This file supplies both:

* `evolveFacesR_sound` — for a NONSTRICT evolve conjunction (kernel-decided
  `evolveNonstrict`), the lowered domain is satisfaction-EQUIVALENT to its emitted face
  box (`evolveFacesR`, the same lowering the tool's viability probes quote);
* `hostFacesR` + `getD`-level wrappers (`hostFaces_dom_iff`, `hostFacesR_fv_side`) in
  the instance idiom (lowering-success side facts by `simp`+`decide`);
* `uniform_picard_data` — one `K, L` for all anchors of a bounded region: any anchor
  ball sits inside the enlarged ball around the region center, where the polynomial
  field is Lipschitz (`odeField_lipschitzOnWith`) and norm-bounded (compactness).
-/
import RelCertifier.Trusted.OracleAPI
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Proofs.Flow.ViabilityWiring
import RelCertifier.Proofs.Soundness.UniformEvol

namespace RelCertifier
open DL Parse Set RelCertifier.Oracle

variable {n : ℕ}

/-! ## Nonstrict evolve forms and face soundness -/

/-- The evolve form uses only nonstrict comparisons (kernel-decided per benchmark). -/
def evolveNonstrict : PForm → Bool
  | .tt => true
  | .cmp op _ _ => op == "<=" || op == ">="
  | .and x y => evolveNonstrict x && evolveNonstrict y
  | _ => false

/-- **Face soundness.** A nonstrict evolve conjunction's lowering is satisfaction-
equivalent to its emitted face box. -/
theorem evolveFacesR_sound {vars : List String} {f : PForm}
    (hns : evolveNonstrict f = true) :
    ∀ {fI : IForm n} {faces : List (ITerm n)},
      Run.lowerF vars n Side.R f = some fI →
      evolveFacesR vars n f = some faces →
      ∀ x : DL.State (Var n),
        Formula.sat fI.toHost x ↔ ∀ g ∈ faces, Term.eval g.toHost x ≤ 0 := by
  induction f with
  | tt =>
      intro fI faces hf hfaces x
      unfold Run.lowerF at hf
      unfold evolveFacesR at hfaces
      injection hf with h1
      injection hfaces with h2
      subst h1; subst h2
      simp [IForm.toHost, Formula.sat]
  | cmp op a b =>
      intro fI faces hf hfaces x
      have hop : op = "<=" ∨ op = ">=" := by
        unfold evolveNonstrict at hns
        rcases Bool.or_eq_true .. |>.mp hns with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simpa using h)
      unfold Run.lowerF at hf
      rcases hea : Run.lowerE vars n Side.R a with _ | ea <;> rw [hea] at hf
      · simp at hf
      rcases heb : Run.lowerE vars n Side.R b with _ | eb <;> rw [heb] at hf
      · simp at hf
      rcases hop with rfl | rfl
      · simp only [reduceIte] at hf
        unfold evolveFacesR at hfaces
        simp only [hea, heb, reduceIte, Option.bind_eq_bind, Option.bind_eq_bind, Option.bind] at hfaces
        injection hf with h1
        injection hfaces with h2
        subst h1; subst h2
        simp only [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
          AOp.interp, List.mem_singleton, forall_eq]
        constructor
        · intro h; linarith
        · intro h; linarith
      · simp only [reduceIte] at hf
        unfold evolveFacesR at hfaces
        simp only [hea, heb, reduceIte, Option.bind_eq_bind, Option.bind_eq_bind, Option.bind] at hfaces
        injection hf with h1
        injection hfaces with h2
        subst h1; subst h2
        simp only [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
          AOp.interp, List.mem_singleton, forall_eq]
        constructor
        · intro h; linarith
        · intro h; linarith
  | and p q ihp ihq =>
      intro fI faces hf hfaces x
      have hnsp : evolveNonstrict p = true := by
        unfold evolveNonstrict at hns
        exact (Bool.and_eq_true .. |>.mp hns).1
      have hnsq : evolveNonstrict q = true := by
        unfold evolveNonstrict at hns
        exact (Bool.and_eq_true .. |>.mp hns).2
      unfold Run.lowerF at hf
      rcases hp : Run.lowerF vars n Side.R p with _ | pI <;> rw [hp] at hf
      · simp at hf
      rcases hq : Run.lowerF vars n Side.R q with _ | qI <;> rw [hq] at hf
      · simp at hf
      unfold evolveFacesR at hfaces
      rcases hfp : evolveFacesR vars n p with _ | facesP <;> rw [hfp] at hfaces
      · simp at hfaces
      rcases hfq : evolveFacesR vars n q with _ | facesQ <;> rw [hfq] at hfaces
      · simp at hfaces
      injection hf with h1
      injection hfaces with h2
      subst h1; subst h2
      have hP := ihp hnsp hp hfp x
      have hQ := ihq hnsq hq hfq x
      simp only [IForm.toHost, Formula.sat]
      constructor
      · rintro ⟨hsp, hsq⟩ g hg
        rcases List.mem_append.mp hg with h | h
        · exact (hP.mp hsp) g h
        · exact (hQ.mp hsq) g h
      · intro h
        exact ⟨hP.mpr (fun g hg => h g (List.mem_append_left _ hg)),
          hQ.mpr (fun g hg => h g (List.mem_append_right _ hg))⟩
  | or p q ihp ihq =>
      intro fI faces hf hfaces
      exact absurd hns (by simp [evolveNonstrict])
  | not p ihp =>
      intro fI faces hf hfaces
      exact absurd hns (by simp [evolveNonstrict])

/-- Face lowerings live on the right side (mirror of `lowerE_fv_side`, list level). -/
theorem evolveFacesR_fv_side {vars : List String} {f : PForm}
    (hnf : PForm.namesFree "L_" f = true) :
    ∀ {faces : List (ITerm n)}, evolveFacesR vars n f = some faces →
      ∀ g ∈ faces, ∀ v ∈ (ITerm.toHost g : Term (Var n)).fv, v.1 = Side.R := by
  induction f with
  | tt =>
      intro faces hfaces g hg
      unfold evolveFacesR at hfaces
      injection hfaces with h
      subst h
      exact absurd hg (List.not_mem_nil)
  | cmp op a b =>
      intro faces hfaces g hg v hv
      unfold evolveFacesR at hfaces
      have hnfa : PExpr.namesFree "L_" a = true := by
        unfold PForm.namesFree at hnf
        exact (Bool.and_eq_true .. |>.mp hnf).1
      have hnfb : PExpr.namesFree "L_" b = true := by
        unfold PForm.namesFree at hnf
        exact (Bool.and_eq_true .. |>.mp hnf).2
      split at hfaces
      · rcases hea : Run.lowerE vars n Side.R a with _ | ea <;> rw [hea] at hfaces
        · simp at hfaces
        rcases heb : Run.lowerE vars n Side.R b with _ | eb <;> rw [heb] at hfaces
        · simp at hfaces
        simp only [Option.bind_eq_bind, Option.bind] at hfaces
        injection hfaces with h
        subst h
        rw [List.mem_singleton] at hg
        subst hg
        simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv
        rcases hv with hv | hv
        · exact Run.lowerE_fv_side (resolvesTo_R vars) hnfa hea v hv
        · exact Run.lowerE_fv_side (resolvesTo_R vars) hnfb heb v hv
      · split at hfaces
        · rcases hea : Run.lowerE vars n Side.R a with _ | ea <;> rw [hea] at hfaces
          · simp at hfaces
          rcases heb : Run.lowerE vars n Side.R b with _ | eb <;> rw [heb] at hfaces
          · simp at hfaces
          simp only [Option.bind_eq_bind, Option.bind] at hfaces
          injection hfaces with h
          subst h
          rw [List.mem_singleton] at hg
          subst hg
          simp only [ITerm.toHost, Term.fv, Set.mem_union] at hv
          rcases hv with hv | hv
          · exact Run.lowerE_fv_side (resolvesTo_R vars) hnfb heb v hv
          · exact Run.lowerE_fv_side (resolvesTo_R vars) hnfa hea v hv
        · simp at hfaces
  | and p q ihp ihq =>
      intro faces hfaces g hg
      have hnfp : PForm.namesFree "L_" p = true := by
        unfold PForm.namesFree at hnf
        exact (Bool.and_eq_true .. |>.mp hnf).1
      have hnfq : PForm.namesFree "L_" q = true := by
        unfold PForm.namesFree at hnf
        exact (Bool.and_eq_true .. |>.mp hnf).2
      unfold evolveFacesR at hfaces
      rcases hfp : evolveFacesR vars n p with _ | facesP <;> rw [hfp] at hfaces
      · simp at hfaces
      rcases hfq : evolveFacesR vars n q with _ | facesQ <;> rw [hfq] at hfaces
      · simp at hfaces
      injection hfaces with h
      subst h
      rcases List.mem_append.mp hg with hm | hm
      · exact ihp hnfp hfp g hm
      · exact ihq hnfq hfq g hm
  | or p q ihp ihq =>
      intro faces hfaces
      unfold evolveFacesR at hfaces
      simp at hfaces
  | not p ihp =>
      intro faces hfaces
      unfold evolveFacesR at hfaces
      simp at hfaces

/-! ## Host-level faces and the instance wrappers -/

/-- The lowered face box of a mode (getD level, like `hostEvolve`). -/
noncomputable def hostFacesR (vars : List String) (n : ℕ) (m : PMode) :
    List (Term (Var n)) :=
  ((evolveFacesR vars n m.evolve).map (·.map ITerm.toHost)).getD []

/-- The domain ↔ face-box equivalence, getD level. -/
theorem hostFaces_dom_iff {vars : List String} {m : PMode}
    (hns : evolveNonstrict m.evolve = true)
    (hsome : (Run.lowerF vars n Side.R m.evolve : Option (IForm n)).isSome = true)
    (hsomeF : (evolveFacesR vars n m.evolve : Option (List (ITerm n))).isSome = true) :
    ∀ x : DL.State (Var n), Formula.sat (hostEvolve vars n Side.R m) x ↔
      ∀ g ∈ hostFacesR vars n m, Term.eval g x ≤ 0 := by
  intro x
  obtain ⟨fI, hf⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨faces, hfaces⟩ := Option.isSome_iff_exists.mp hsomeF
  unfold hostEvolve hostFacesR
  rw [hf, hfaces]
  simp only [Option.map_some, Option.getD_some]
  rw [evolveFacesR_sound hns hf hfaces x]
  constructor
  · intro h g hg
    obtain ⟨gI, hgI, rfl⟩ := List.mem_map.mp hg
    exact h gI hgI
  · intro h gI hgI
    exact h (gI.toHost) (List.mem_map.mpr ⟨gI, hgI, rfl⟩)

/-- Host faces live on the right side, getD level. -/
theorem hostFacesR_fv_side {vars : List String} {m : PMode}
    (hnf : PForm.namesFree "L_" m.evolve = true) :
    ∀ g ∈ hostFacesR vars n m, ∀ v ∈ (g : Term (Var n)).fv, v.1 = Side.R := by
  intro g hg
  unfold hostFacesR at hg
  rcases hfaces : evolveFacesR vars n m.evolve with _ | faces <;> rw [hfaces] at hg
  · exact absurd hg (by simp)
  simp only [Option.map_some, Option.getD_some] at hg
  obtain ⟨gI, hgI, rfl⟩ := List.mem_map.mp hg
  exact evolveFacesR_fv_side hnf hfaces gI hgI

/-! ## Uniform Picard data over a bounded anchor region -/

/-- **One `K, L` for every anchor of a bounded region**: anchor balls sit inside the
enlarged ball around the region center, where the polynomial field is Lipschitz and
norm-bounded by compactness. -/
theorem uniform_picard_data {V : Type*} [Fintype V] [DecidableEq V]
    (sys : ODESystem V) (x₀ : DL.State V) (R a : ℝ) (hR : 0 ≤ R) :
    ∃ K L : NNReal,
      (∀ ν : DL.State V, ν ∈ Metric.closedBall x₀ R →
        LipschitzOnWith K (odeField sys) (Metric.closedBall ν a))
      ∧ (∀ ν : DL.State V, ν ∈ Metric.closedBall x₀ R →
        ∀ x ∈ Metric.closedBall ν a, ‖odeField sys x‖ ≤ (L : ℝ)) := by
  obtain ⟨K, hK⟩ := odeField_lipschitzOnWith sys x₀ (R + a)
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ (R + a)).exists_bound_of_continuousOn
    ((odeField_contDiff sys).continuous.continuousOn)
  have hsub : ∀ ν : DL.State V, ν ∈ Metric.closedBall x₀ R →
      Metric.closedBall ν a ⊆ Metric.closedBall x₀ (R + a) := by
    intro ν hν x hx
    rw [Metric.mem_closedBall] at *
    calc dist x x₀ ≤ dist x ν + dist ν x₀ := dist_triangle _ _ _
      _ ≤ a + R := add_le_add hx hν
      _ = R + a := add_comm _ _
  refine ⟨K, C.toNNReal, ?_, ?_⟩
  · intro ν hν
    exact hK.mono (hsub ν hν)
  · intro ν hν x hx
    calc ‖odeField sys x‖ ≤ C := hC x (hsub ν hν hx)
      _ ≤ max C 0 := le_max_left _ _
      _ = (C.toNNReal : ℝ) := (Real.coe_toNNReal' C).symm
/-! ## `WellFormedFlowB` transfer along pointwise-equal fields

The contract witnesses (`WellFormedFlowB_contract`, the explicit exponential) are
stated over the syntactic shape `contractF`/`bandDom`; benchmark instances carry the
`getD`-lowered `hostDyn`/`hostEvolve`. The bounded flow well-formedness is purely
semantic in the field values and the domain's satisfaction, so it transfers. -/

theorem WellFormedFlowB_transfer {fR fR' : Fin n → Term (Var n)}
    {lam lam' : Term (Var n)} {domR domR' : Formula (Var n)} {dt : ℝ}
    (hev : ∀ (i : Fin n) (x : DL.State (Var n)),
      Term.eval (Term.binop .mul lam' (fR' i)) x
        = Term.eval (Term.binop .mul lam (fR i)) x)
    (hdom : ∀ x : DL.State (Var n), Formula.sat domR' x ↔ Formula.sat domR x)
    (h : WellFormedFlowB fR lam domR dt) :
    WellFormedFlowB fR' lam' domR' dt := by
  intro base hb s hs hsdt
  obtain ⟨ΦR, hΦR0, hRder, hRmask, hRdom⟩ := h base ((hdom base).mp hb) s hs hsdt
  refine ⟨ΦR, hΦR0, ?_, ?_, ?_⟩
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    have horig := hRder t ht (Rv i, Term.binop .mul lam (fR i)) (by
      simp only [rightBlock, List.mem_map, List.mem_finRange]
      exact ⟨i, trivial, rfl⟩)
    simpa only [hev i (ΦR t)] using horig
  · intro t ht x hx
    refine hRmask t ht x ?_
    intro hb'
    refine hx ?_
    simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map,
      List.mem_finRange] at hb' ⊢
    obtain ⟨i, -, hi⟩ := hb'
    exact ⟨i, trivial, hi⟩
  · intro t ht
    exact (hdom (ΦR t)).mpr (hRdom t ht)

end RelCertifier
