/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S2 dischargers — `CoverCertMC` fields from the emitted cut certificates

Per-benchmark instances feed `CoverCertMC` from three ingredient kinds:

* **`hiff`** — `hostAtom_iff`: the lowered atom formula ≡ its safe-side term `≤ 0`,
  fully generic (the failure branches of the two lowerings align, so the `getD`
  defaults `⊤`/`0` keep the equivalence);
* **O1 entry** — `hostGuard_cutAtoms_sat`: the mode guard's lowering implies each cut
  atom's lowering, given the guard's lowering succeeds (a per-benchmark `simp`+`decide`
  kernel fact) — atom membership in `cutAtoms` is kernel-decided (`evolStrengtheningWF`);
* **staying** — the route adapters from `CutLift` (`atom_boxle_{L,R}_{strict,nonstrict}`,
  `AtomFact.ofLie`), plus `atomsStay_L_frozen_dyn` here: LEFT atoms along the
  frozen-left dynamic-reposition flows are constant (every field is `0` where the atom
  reads), a Lean fact needing no Z3.
-/
import RelCertifier.Proofs.Soundness.CutCover
import RelCertifier.Proofs.Encoding.CoverInstance

namespace RelCertifier
open DL Parse Set RelCertifier.Oracle

variable {n : ℕ}

/-! ## Host-level atom data (`getD`-wrapped, like `hostGuard`/`hostEvolve`) -/

/-- The lowered atom formula. -/
noncomputable def hostAtomF (vars : List String) (n : ℕ) (side : Side) (a : PForm) :
    Formula (Var n) :=
  ((Run.lowerF vars n side a).map IForm.toHost).getD Formula.tt

/-- The lowered atom's safe-side term. -/
noncomputable def hostAtomG (vars : List String) (n : ℕ) (side : Side) (a : PForm) :
    Term (Var n) :=
  ((cutAtomG vars n side a).map ITerm.toHost).getD (Term.const 0)

/-! ## `hiff` -/

/-- The lowered atom formula is satisfaction-equivalent to `hostAtomG ≤ 0`, with the
lowering-failure branches aligned (`⊤` ↔ `0 ≤ 0`). -/
theorem hostAtom_iff {vars : List String} {side : Side} {op : String} {x y : PExpr}
    (hop : op = "<=" ∨ op = ">=") (ν : DL.State (Var n)) :
    Formula.sat (hostAtomF vars n side (.cmp op x y)) ν
      ↔ Term.eval (hostAtomG vars n side (.cmp op x y)) ν ≤ 0 := by
  unfold hostAtomF hostAtomG
  rcases hex : Run.lowerE vars n side x with _ | ex
  · have hf : Run.lowerF vars n side (.cmp op x y) = none := by
      simp [Run.lowerF, hex]
    have hg : cutAtomG vars n side (.cmp op x y) = (none : Option (ITerm n)) := by
      rcases hop with rfl | rfl <;> simp [cutAtomG, hex]
    rw [hf, hg]
    simp [Formula.sat, Term.eval]
  · rcases hey : Run.lowerE vars n side y with _ | ey
    · have hf : Run.lowerF vars n side (.cmp op x y) = none := by
        simp [Run.lowerF, hex, hey]
      have hg : cutAtomG vars n side (.cmp op x y) = (none : Option (ITerm n)) := by
        rcases hop with rfl | rfl <;> simp [cutAtomG, hex, hey]
      rw [hf, hg]
      simp [Formula.sat, Term.eval]
    · rcases hop with rfl | rfl
      · have hf : Run.lowerF vars n side (.cmp "<=" x y)
            = some (IForm.cmp CompOp.le ex ey) := by
          simp [Run.lowerF, hex, hey]
        have hg : cutAtomG vars n side (.cmp "<=" x y)
            = some (ITerm.bin .sub ex ey) := by
          simp [cutAtomG, hex, hey]
        rw [hf, hg]
        simpa using cutAtomG_sat (Or.inl rfl) hf hg ν
      · have hf : Run.lowerF vars n side (.cmp ">=" x y)
            = some (IForm.cmp CompOp.ge ex ey) := by
          simp [Run.lowerF, hex, hey]
        have hg : cutAtomG vars n side (.cmp ">=" x y)
            = some (ITerm.bin .sub ey ex) := by
          simp [cutAtomG, hex, hey]
        rw [hf, hg]
        simpa using cutAtomG_sat (Or.inr rfl) hf hg ν

/-! ## O1 -/

/-- A cut atom of a successfully-lowered formula lowers too. -/
theorem lowerF_cutAtom_isSome {vars : List String} {side : Side} {f a : PForm}
    (ha : a ∈ cutAtoms f) :
    ∀ {fI : IForm n}, Run.lowerF vars n side f = some fI →
      ∃ aI : IForm n, Run.lowerF vars n side a = some aI := by
  induction f with
  | and p q ihp ihq =>
      intro fI hf
      unfold Run.lowerF at hf
      rcases hp : Run.lowerF vars n side p with _ | pI <;> rw [hp] at hf
      · simp at hf
      rcases hq : Run.lowerF vars n side q with _ | qI <;> rw [hq] at hf
      · simp at hf
      unfold cutAtoms at ha
      rcases List.mem_append.mp ha with h | h
      · exact ihp h hp
      · exact ihq h hq
  | cmp op x y =>
      intro fI hf
      unfold cutAtoms at ha
      split at ha
      · rw [List.mem_singleton.mp ha]
        exact ⟨fI, hf⟩
      · exact absurd ha (by simp)
  | tt => intro fI hf; exact absurd ha (by simp [cutAtoms])
  | or p q ihp ihq => intro fI hf; exact absurd ha (by simp [cutAtoms])
  | not p ihp => intro fI hf; exact absurd ha (by simp [cutAtoms])

/-- **O1, `getD`-level.** Wherever the mode guard's lowering holds, each of its cut
atoms' lowerings holds — given the guard lowers (per-benchmark kernel fact). -/
theorem hostGuard_cutAtoms_sat {vars : List String} {side : Side} {m : PMode}
    {a : PForm} (ha : a ∈ cutAtoms m.guard)
    (hsome : (Run.lowerF vars n side m.guard : Option (IForm n)).isSome = true) :
    ∀ ν : DL.State (Var n), Formula.sat (hostGuard vars n side m) ν →
      Formula.sat (hostAtomF vars n side a) ν := by
  intro ν hν
  obtain ⟨fI, hf⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨aI, haI⟩ := lowerF_cutAtom_isSome ha hf
  unfold hostGuard at hν
  rw [hf] at hν
  unfold hostAtomF
  rw [haI]
  exact cutAtoms_sat ha hf haI ν (by simpa using hν)

/-! ## Left atoms are frozen along the dynamic-reposition flows -/

/-- The Lie derivative with both fields zeroed evaluates to `0`. -/
theorem eval_lieDeriv_zero (g : Term (Var n)) (x : DL.State (Var n)) :
    Term.eval (lieDeriv g (fun _ => Term.const 0) (fun _ => Term.const 0)
      (Term.const 1)) x = 0 := by
  unfold lieDeriv
  induction (List.finRange n) with
  | nil => simp [sumTerm, Term.eval]
  
  | cons i l ih => simp [sumTerm, Term.eval, AOp.interp, ih]

/-- **Left atoms stay along the frozen-left dynamic flows** — every field is `0` where
the atom reads (`Lv`-only, and the left block of `dynSys` is the zero field), so the
atom is constant. No Z3. -/
theorem atomsStay_L_frozen_dyn (fR : Fin n → Term (Var n)) (dom : Formula (Var n))
    (atoms : List (CutAtomP n))
    (hfv : ∀ a ∈ atoms, ∀ i : Fin n, Rv i ∉ a.2.fv) :
    AtomsStay atoms (jointSys (fun _ => Term.const 0) fR (Term.const 1)) dom := by
  intro a ha ν hb
  refine atom_boxle_L_nonstrict a.2 (fun _ => Term.const 0) fR (Term.const 1) dom
    Formula.tt (hfv a ha) (fun x _ => by simp [Formula.sat]) ?_ hb
  intro σ hσ
  obtain ⟨-, hgt⟩ := hσ
  rw [show Formula.sat (Formula.cmp .gt (lieDeriv a.2 (fun _ => Term.const 0)
      (fun _ => Term.const 0) (Term.const 1)) (Term.const 0)) σ ↔
    Term.eval (lieDeriv a.2 (fun _ => Term.const 0) (fun _ => Term.const 0)
      (Term.const 1)) σ > 0 from by simp [Formula.sat, CompOp.interp, Term.eval]] at hgt
  rw [eval_lieDeriv_zero] at hgt
  exact lt_irrefl 0 hgt

/-! ## Side split of the atom's safe-side term, and small assembly helpers -/

/-- `hostAtomG` of an opposite-prefix-free atom lives on its lowering side. -/
theorem hostAtomG_fv_side {vars : List String} {s : Side} {bad : String}
    (hres : ResolvesTo vars n s bad) {op : String} {x y : PExpr}
    (hop : op = "<=" ∨ op = ">=")
    (hfx : PExpr.namesFree bad x = true) (hfy : PExpr.namesFree bad y = true) :
    ∀ v ∈ (hostAtomG vars n s (.cmp op x y) : Term (Var n)).fv, v.1 = s := by
  intro v hv
  unfold hostAtomG at hv
  rcases hex : Run.lowerE vars n s x with _ | ex
  · rcases hop with rfl | rfl <;>
      · rw [show cutAtomG vars n s (.cmp _ x y) = (none : Option (ITerm n)) from by
          simp [cutAtomG, hex]] at hv
        exact absurd hv (by simp [Term.fv])
  · rcases hey : Run.lowerE vars n s y with _ | ey
    · rcases hop with rfl | rfl <;>
        · rw [show cutAtomG vars n s (.cmp _ x y) = (none : Option (ITerm n)) from by
            simp [cutAtomG, hex, hey]] at hv
          exact absurd hv (by simp [Term.fv])
    · have hvx := Run.lowerE_fv_side hres hfx hex
      have hvy := Run.lowerE_fv_side hres hfy hey
      rcases hop with rfl | rfl
      · rw [show cutAtomG vars n s (.cmp "<=" x y) = some (ITerm.bin .sub ex ey) from by
          simp [cutAtomG, hex, hey]] at hv
        simp only [Option.map_some, Option.getD_some, ITerm.toHost, Term.fv,
          Set.mem_union] at hv
        rcases hv with hv | hv
        · exact hvx v hv
        · exact hvy v hv
      · rw [show cutAtomG vars n s (.cmp ">=" x y) = some (ITerm.bin .sub ey ex) from by
          simp [cutAtomG, hex, hey]] at hv
        simp only [Option.map_some, Option.getD_some, ITerm.toHost, Term.fv,
          Set.mem_union] at hv
        rcases hv with hv | hv
        · exact hvy v hv
        · exact hvx v hv

/-- The empty atom family stays along anything (windows without left cuts). -/
theorem atomsStay_nil (sys : ODESystem (Var n)) (dom : Formula (Var n)) :
    AtomsStay ([] : List (CutAtomP n)) sys dom := by
  intro a ha
  exact absurd ha (List.not_mem_nil)

theorem atomsIff_nil : AtomsIff ([] : List (CutAtomP n)) := by
  intro a ha
  exact absurd ha (List.not_mem_nil)

/-- Transport `SegPreservesAllOn` across satisfaction-equivalent domains (the tool
skips `⊤` cut conjuncts in its fold; the certificate's shape keeps them). -/
theorem segPresAll_dom_congr {gs : List (Term (Var n))} {sys : ODESystem (Var n)}
    {D D' : Formula (Var n)} (h : ∀ x, Formula.sat D x ↔ Formula.sat D' x)
    (hp : SegPreservesAllOn gs sys D') : SegPreservesAllOn gs sys D :=
  fun ν hν ω hsem => hp ν hν ω (sem_ode_congr h hsem)

/-! ## Frozen and contract-shape staying (Lean facts, no Z3)

The tool's `frozen` and `shape` cut routes take no Z3 probe: frozen atoms read only
zero-field coordinates; shape atoms are the contract tangent case (`v ≥ lo` under
`v' = k(c−v)` with `lo ≤ c`, or `v ≤ hi` with `c ≤ hi`) — a superlevel-DI fact
(`Lie ≤ 0` on the atom's superlevel set), no exponential needed. -/

/-- The Lie sum collapses to the `j`-summand when the atom reads only `Rv j`. -/
theorem eval_lieDeriv_single_R (g : Term (Var n)) (j : Fin n)
    (hLv : ∀ i : Fin n, Lv i ∉ g.fv) (hRv : ∀ i : Fin n, i ≠ j → Rv i ∉ g.fv)
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (x : DL.State (Var n)) :
    Term.eval (lieDeriv g fL fR lam) x
      = Term.eval (tderiv g (Rv j)) x * (Term.eval lam x * Term.eval (fR j) x) := by
  unfold lieDeriv
  rw [eval_sumTerm, List.map_map, ← Fin.sum_univ_def]
  rw [Finset.sum_eq_single j]
  · simp [Term.eval, AOp.interp, tderiv_not_free (hLv j)]
  · intro b _ hb
    simp [Term.eval, AOp.interp, tderiv_not_free (hLv b), tderiv_not_free (hRv b hb)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The Lie sum collapses to the `j`-summand when the atom reads only `Lv j`. -/
theorem eval_lieDeriv_single_L (g : Term (Var n)) (j : Fin n)
    (hRv : ∀ i : Fin n, Rv i ∉ g.fv) (hLv : ∀ i : Fin n, i ≠ j → Lv i ∉ g.fv)
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (x : DL.State (Var n)) :
    Term.eval (lieDeriv g fL fR lam) x
      = Term.eval (tderiv g (Lv j)) x * Term.eval (fL j) x := by
  unfold lieDeriv
  rw [eval_sumTerm, List.map_map, ← Fin.sum_univ_def]
  rw [Finset.sum_eq_single j]
  · simp [Term.eval, AOp.interp, tderiv_not_free (hRv j)]
  · intro b _ hb
    simp [Term.eval, AOp.interp, tderiv_not_free (hLv b hb), tderiv_not_free (hRv b)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **Frozen R-atom staying**: every coordinate the atom reads carries the zero field. -/
theorem atom_boxle_R_frozen (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (dom : Formula (Var n))
    (hLv : ∀ i : Fin n, Lv i ∉ g.fv)
    (hfz : ∀ i : Fin n, Rv i ∈ g.fv → fR i = Term.const 0)
    {ν : DL.State (Var n)} (hinit : Term.eval g ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom) (fun ω => Term.eval g ω) ν := by
  refine DI_nonstrict_domain (jointSys_wellFormed fL fR lam)
    (term_differentiable g) ?_ hinit
  intro x hx
  rw [← lieDeriv_correct]
  have hz : Term.eval (lieDeriv g fL fR lam) x = 0 := by
    unfold lieDeriv
    rw [eval_sumTerm, List.map_map]
    refine List.sum_eq_zero ?_
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
    by_cases hi : Rv i ∈ g.fv
    · simp [Term.eval, AOp.interp, tderiv_not_free (hLv i), hfz i hi]
    · simp [Term.eval, AOp.interp, tderiv_not_free (hLv i), tderiv_not_free hi]
  rw [hz]

/-- **Contract-shape R-atom, `≥` direction**: `v ≥ lo` (safe side `lo − v ≤ 0`) under
the contract field `v' = k(c − v)` with `0 ≤ k`, `lo ≤ c`, `0 ≤ λ` — superlevel DI. -/
theorem atom_boxle_R_contract_ge (j : Fin n) (lo c k lamv : ℝ)
    (fL fR : Fin n → Term (Var n)) (dom : Formula (Var n))
    (hk : 0 ≤ k) (hcl : lo ≤ c) (hlam : 0 ≤ lamv)
    (hfj : fR j = Term.binop .mul (Term.const k)
      (Term.binop .sub (Term.const c) (Term.var (Rv j))))
    {ν : DL.State (Var n)}
    (hinit : Term.eval (Term.binop .sub (Term.const lo) (Term.var (Rv j))) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (Term.binop .sub (Term.const lo) (Term.var (Rv j))) ω) ν := by
  set g : Term (Var n) := Term.binop .sub (Term.const lo) (Term.var (Rv j)) with hg
  refine DI_nonstrict_superlevel (jointSys_wellFormed fL fR (Term.const lamv))
    (term_differentiable g) ?_ hinit
  intro x hx hge
  rw [← lieDeriv_correct]
  rw [eval_lieDeriv_single_R g j
    (fun i h => by simp [hg, Term.fv, Lv, Rv, Prod.ext_iff] at h)
    (fun i hij h => by
      simp only [hg, Term.fv, Set.mem_union, Set.mem_empty_iff_false, false_or,
        Set.mem_singleton_iff] at h
      exact hij (by simpa [Rv, Prod.ext_iff] using h)) fL fR (Term.const lamv) x]
  rw [hfj]
  have hv : x (Rv j) ≤ lo := by
    simpa [hg, Term.eval, AOp.interp] using hge
  have htd : Term.eval (tderiv g (Rv j)) x = -1 := by
    simp [hg, tderiv, Term.eval, AOp.interp]
  rw [htd]
  have hcv : (0:ℝ) ≤ c - x (Rv j) := by linarith
  simp only [Term.eval, AOp.interp]
  nlinarith [mul_nonneg hk hcv, mul_nonneg hlam (mul_nonneg hk hcv)]

/-- **Contract-shape R-atom, `≤` direction**: `v ≤ hi` (safe side `v − hi ≤ 0`) under
`v' = k(c − v)` with `0 ≤ k`, `c ≤ hi`, `0 ≤ λ`. -/
theorem atom_boxle_R_contract_le (j : Fin n) (hi c k lamv : ℝ)
    (fL fR : Fin n → Term (Var n)) (dom : Formula (Var n))
    (hk : 0 ≤ k) (hch : c ≤ hi) (hlam : 0 ≤ lamv)
    (hfj : fR j = Term.binop .mul (Term.const k)
      (Term.binop .sub (Term.const c) (Term.var (Rv j))))
    {ν : DL.State (Var n)}
    (hinit : Term.eval (Term.binop .sub (Term.var (Rv j)) (Term.const hi)) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (Term.binop .sub (Term.var (Rv j)) (Term.const hi)) ω) ν := by
  set g : Term (Var n) := Term.binop .sub (Term.var (Rv j)) (Term.const hi) with hg
  refine DI_nonstrict_superlevel (jointSys_wellFormed fL fR (Term.const lamv))
    (term_differentiable g) ?_ hinit
  intro x hx hge
  rw [← lieDeriv_correct]
  rw [eval_lieDeriv_single_R g j
    (fun i h => by simp [hg, Term.fv, Lv, Rv, Prod.ext_iff] at h)
    (fun i hij h => by
      simp only [hg, Term.fv, Set.mem_union, Set.mem_empty_iff_false, or_false,
        Set.mem_singleton_iff] at h
      exact hij (by simpa [Rv, Prod.ext_iff] using h)) fL fR (Term.const lamv) x]
  rw [hfj]
  have hv : hi ≤ x (Rv j) := by
    simpa [hg, Term.eval, AOp.interp] using hge
  have htd : Term.eval (tderiv g (Rv j)) x = 1 := by
    simp [hg, tderiv, Term.eval, AOp.interp]
  rw [htd]
  have hcv : c - x (Rv j) ≤ 0 := by linarith
  simp only [Term.eval, AOp.interp]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hk hcv,
    mul_nonpos_of_nonneg_of_nonpos hlam (mul_nonpos_of_nonneg_of_nonpos hk hcv)]

/-- **Contract-shape L-atom, `≥` direction** (stretch-free left field). -/
theorem atom_boxle_L_contract_ge (j : Fin n) (lo c k : ℝ)
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (dom : Formula (Var n))
    (hk : 0 ≤ k) (hcl : lo ≤ c)
    (hfj : fL j = Term.binop .mul (Term.const k)
      (Term.binop .sub (Term.const c) (Term.var (Lv j))))
    {ν : DL.State (Var n)}
    (hinit : Term.eval (Term.binop .sub (Term.const lo) (Term.var (Lv j))) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (Term.binop .sub (Term.const lo) (Term.var (Lv j))) ω) ν := by
  set g : Term (Var n) := Term.binop .sub (Term.const lo) (Term.var (Lv j)) with hg
  refine DI_nonstrict_superlevel (jointSys_wellFormed fL fR lam)
    (term_differentiable g) ?_ hinit
  intro x hx hge
  rw [← lieDeriv_correct]
  rw [eval_lieDeriv_single_L g j
    (fun i h => by simp [hg, Term.fv, Lv, Rv, Prod.ext_iff] at h)
    (fun i hij h => by
      simp only [hg, Term.fv, Set.mem_union, Set.mem_empty_iff_false, false_or,
        Set.mem_singleton_iff] at h
      exact hij (by simpa [Lv, Prod.ext_iff] using h)) fL fR lam x]
  rw [hfj]
  have hv : x (Lv j) ≤ lo := by
    simpa [hg, Term.eval, AOp.interp] using hge
  have htd : Term.eval (tderiv g (Lv j)) x = -1 := by
    simp [hg, tderiv, Term.eval, AOp.interp]
  rw [htd]
  have hcv : (0:ℝ) ≤ c - x (Lv j) := by linarith
  simp only [Term.eval, AOp.interp]
  nlinarith [mul_nonneg hk hcv]

/-- **Contract-shape L-atom, `≤` direction**. -/
theorem atom_boxle_L_contract_le (j : Fin n) (hi c k : ℝ)
    (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (dom : Formula (Var n))
    (hk : 0 ≤ k) (hch : c ≤ hi)
    (hfj : fL j = Term.binop .mul (Term.const k)
      (Term.binop .sub (Term.const c) (Term.var (Lv j))))
    {ν : DL.State (Var n)}
    (hinit : Term.eval (Term.binop .sub (Term.var (Lv j)) (Term.const hi)) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (Term.binop .sub (Term.var (Lv j)) (Term.const hi)) ω) ν := by
  set g : Term (Var n) := Term.binop .sub (Term.var (Lv j)) (Term.const hi) with hg
  refine DI_nonstrict_superlevel (jointSys_wellFormed fL fR lam)
    (term_differentiable g) ?_ hinit
  intro x hx hge
  rw [← lieDeriv_correct]
  rw [eval_lieDeriv_single_L g j
    (fun i h => by simp [hg, Term.fv, Lv, Rv, Prod.ext_iff] at h)
    (fun i hij h => by
      simp only [hg, Term.fv, Set.mem_union, Set.mem_empty_iff_false, or_false,
        Set.mem_singleton_iff] at h
      exact hij (by simpa [Lv, Prod.ext_iff] using h)) fL fR lam x]
  rw [hfj]
  have hv : hi ≤ x (Lv j) := by
    simpa [hg, Term.eval, AOp.interp] using hge
  have htd : Term.eval (tderiv g (Lv j)) x = 1 := by
    simp [hg, tderiv, Term.eval, AOp.interp]
  rw [htd]
  have hcv : c - x (Lv j) ≤ 0 := by linarith
  simp only [Term.eval, AOp.interp]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hk hcv]

/-- Right-sided atom, superlevel route (C): the O2 UNSAT (`evR ∧ g ≥ 0 ∧ ġ > 0`,
one-sided, λ = 1) gives flow-invariance for any λ ≥ 0. Subsumes the tool's bespoke
contract-shape check: a shape atom's superlevel probe is UNSAT by the contract sign. -/
theorem atom_boxle_R_superlevel (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (c : ℝ) (hc : 0 ≤ c) (dom evR : Formula (Var n))
    (hfv : ∀ i : Fin n, Lv i ∉ g.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat evR x)
    (hunsat : ∀ σ, ¬ Formula.sat
      (flowQuerySuperlevel ⟨g, fun _ => Term.const 0, fR, Term.const 1, evR⟩) σ)
    {ν : DL.State (Var n)} (hinit : Term.eval g ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const c)) dom)
      (fun ω => Term.eval g ω) ν := by
  refine DI_nonstrict_superlevel (jointSys_wellFormed fL fR (Term.const c))
    (term_differentiable g) ?_ hinit
  intro x hx hge
  rw [← lieDeriv_correct, lieDeriv_one_sided_R g fL fR c hfv]
  have hle : Term.eval (lieDeriv g (fun _ => Term.const 0) fR (Term.const 1)) x ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    exact hunsat x ⟨hdomImp x hx,
      by simpa [Formula.sat, CompOp.interp, Term.eval] using hge,
      by simpa [Formula.sat, CompOp.interp, Term.eval] using hpos⟩
  exact mul_nonpos_of_nonneg_of_nonpos hc hle

/-- Left-sided atom, superlevel route (C) — the stretch is immaterial. -/
theorem atom_boxle_L_superlevel (g : Term (Var n)) (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (dom evL : Formula (Var n))
    (hfv : ∀ i : Fin n, Rv i ∉ g.fv)
    (hdomImp : ∀ x, Formula.sat dom x → Formula.sat evL x)
    (hunsat : ∀ σ, ¬ Formula.sat
      (flowQuerySuperlevel ⟨g, fL, fun _ => Term.const 0, Term.const 1, evL⟩) σ)
    {ν : DL.State (Var n)} (hinit : Term.eval g ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom) (fun ω => Term.eval g ω) ν := by
  refine DI_nonstrict_superlevel (jointSys_wellFormed fL fR lam)
    (term_differentiable g) ?_ hinit
  intro x hx hge
  rw [← lieDeriv_correct, lieDeriv_one_sided_L g fL fR lam hfv]
  by_contra hpos
  rw [not_le] at hpos
  exact hunsat x ⟨hdomImp x hx,
    by simpa [Formula.sat, CompOp.interp, Term.eval] using hge,
    by simpa [Formula.sat, CompOp.interp, Term.eval] using hpos⟩

end RelCertifier


