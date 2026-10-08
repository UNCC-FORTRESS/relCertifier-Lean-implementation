/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `plant_fan_mid` — the DECLARED invariant, with the checked cut as `Hold`'s region

`PlantFanMidModal.plant_fan_mid_modal` states Theorem 3 at `θ_R ≥ 0.6 ∧ θ_L ≤ θ_R
+ 0.25`: the `Hold` guard atom — the tool's CHECKED CUT for the `Hold` pairing (route C
there: `Hold`'s field `θ' = ½(0.6 − θ)` is asymptotic, not frozen) — conjoined to the
declared invariant for every right mode. This leaf states the declared invariant `θ_L ≤
θ_R + 0.25` itself, with the cut carried only where the tool checked it: as the region
of the `Hold` mode in the mode-region bookkeeping `mvRegionR` (`regionsA 2 = ⌊θ_R ≥
0.6⌋`, `⊤` at `ApproachFast/Slow`). From every state satisfying the declared invariant
with the right in `ApproachFast` or `ApproachSlow` — any `θ_R` in the evolve domain —
and from every state in `Hold` inside its region, the refinement is maintained.

The plain-`mvValid` form is FALSE: at `mv = Hold`, `θ_R = 0.3`, `θ_L = 0.6`, `v_L =
0.3` the invariant holds, the left `Accelerate` window raises `θ_L` immediately, and
`Hold`'s field `θ' = ½(0.6 − θ)` from `θ_R = 0.3` grows `θ_R` by at most `0.15·t` while
the gap is already closed to zero — the right cannot keep up (`docs/CUT-COMPOSITION.md`
has the precise countermodel). The region at `Hold` is what the two cut obligations
compose to: O1 (entry — a switch into `Hold` satisfies its guard, the trust base's
guard-gated switching) and O2 (invariance along `Hold`'s own field: `θ ≥ 0.6` is a
sublevel set the contraction never leaves).

**The response (catch-up, Z3-free).** After the left window, the right flows in its
start mode at that mode's constant rate (`½`, `3/10`) for exactly the duration that
brings `θ_R` to `0.6` (zero if already there — then also from `Hold`, whose region gives
it), then hops — zero-duration runs — along the declared chain into `Hold`. The
invariant at the end is endpoint arithmetic: `θ_L ≤ 0.65` (the window ends in its evolve
domain), `θ_R ≥ 0.6`, and `0.65 ≤ 0.6 + 0.3`. No verdict hypothesis remains.
-/
import RelCertifier.Instances.PlantFanMidModal
import RelCertifier.Proofs.Encoding.EnvelopeChainR
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.CutComposition

namespace RelCertifier
namespace PlantFanMidDeclared

open DL DLCalTiming DLRel Parse Set PlantFanMidModal

/-! ## The mode regions: the checked cut at `Hold` (index 2), `⊤` elsewhere -/

noncomputable def regionsA (q : ℕ) : Formula (Var 2) :=
  if q = 2 then invLe regA else Formula.tt

theorem regionsA_fv (q : ℕ) : (regionsA q).fv ⊆ range Rv := by
  intro x hx
  unfold regionsA at hx
  split at hx
  · simp only [invLe, Formula.fv, Term.fv, regA, Set.union_empty, Set.empty_union,
      Set.mem_singleton_iff] at hx
    subst hx; exact ⟨0, rfl⟩
  · exact absurd hx (by simp [Formula.fv])

theorem hmvregA : ∀ q, mvA ∉ (regionsA q).fv := fun q h =>
  aux_notin_range_Rv 0 (regionsA_fv q h)

theorem sat_regionsA2 (x : State (Var 2)) :
    Formula.sat (regionsA 2) x ↔ (3:ℝ)/5 ≤ x (Rv 0) := by
  simp [regionsA, regA, Term.eval, AOp.interp]

theorem hmvFA' : mvA ∉ (FM gA []).fv := notMem_FM_fv (by
  intro g' hg' h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
  subst hg'
  exact hmvgA h)

/-! ## Parse pins (the base file supplies `hpr00`, `hpr12`, `hpr05`, `hpr06`) -/

theorem hprD065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hprDm045 : Run.parseRat "-0.45" = some (-(9:ℚ)/20) := by
  have h : parseQ "-0.45" = some (⟨-45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hprD045 : Run.parseRat "0.45" = some ((9:ℚ)/20) := by
  have h : parseQ "0.45" = some (⟨45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hprDm005 : Run.parseRat "-0.05" = some (-(1:ℚ)/20) := by
  have h : parseQ "-0.05" = some (⟨-5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hprD025 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hprD03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## Shape pins: the domains, the invariant term, the right rates -/

theorem sat_domLA (x : State (Var 2)) : Formula.sat domLA x ↔
    (-(1:ℝ)/20 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 13/20 ∧ -(9:ℝ)/20 ≤ x (Lv 1) ∧
      x (Lv 1) ≤ 9/20) := by
  simp only [domLA, hostEvolve, mLA, plant_fan_mid_IR, vsA]
  simp [Run.lowerF, Run.lowerE, hprDm005, hprD065, hprDm045, hprD045, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp,
    Term.eval, Lv]
  tauto

theorem sat_domRA (x : State (Var 2)) : Formula.sat domRA x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 6/5) := by
  rw [domRA_shape]
  simp [Formula.sat, CompOp.interp, Term.eval, Rv]

/-- The declared tolerance: `θ_L − (θ_R + 3/10)`. -/
theorem eval_gA (x : State (Var 2)) :
    Term.eval gA x = x (Lv 0) - (x (Rv 0) + 3/10) := by
  have hdL : ("L_theta".drop 2).copy = "theta" := by decide
  have hdR : ("R_theta".drop 2).copy = "theta" := by decide
  simp [gA, plant_fan_mid_IR, Run.invToG, Run.lowerE, vsA, hprD03,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, ITerm.toHost,
    Term.eval, AOp.interp, Lv, Rv]

/-- The approach modes' constant rates: `½`, `3/10`. -/
noncomputable def cA (q : ℕ) : ℝ := if q = 0 then 1/2 else if q = 1 then 3/10 else 0

theorem cA_nonneg (q : ℕ) : 0 ≤ cA q := by
  unfold cA; split_ifs <;> norm_num

theorem cA_pos (q : ℕ) (hq : q < 2) : 0 < cA q := by
  interval_cases q <;> simp [cA]

theorem fRA0_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fRA q 0) x = cA q := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, plant_fan_mid_IR, vsA, Run.dynOf, Run.lowerE, hpr05,
      hprD03, List.finRange, ITerm.toHost, Term.eval, cA]

theorem fRA1_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fRA q 1) x = 0 := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, plant_fan_mid_IR, vsA, Run.dynOf, Run.lowerE, hpr05,
      hprD03, hpr06, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval]

/-! ## Window facts -/

theorem leftBlock_wf (fL : Fin 2 → Term (Var 2)) : (leftBlock fL).WellFormed := by
  have hLinj : Function.Injective (Lv (n := 2)) := by
    intro a b h; simpa [Lv, Prod.ext_iff] using h
  unfold ODESystem.WellFormed leftBlock
  simp only [List.map_map, Function.comp_def]
  exact (List.nodup_finRange 2).map hLinj

theorem htg_leftBlock (fL : Fin 2 → Term (Var 2)) : tgA ∉ (leftBlock fL).bound := by
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub fL _ h
  exact aux_ne_Lv 1 i hi

theorem window_maskA (l : ℕ) (dt : ℝ) {σ ν : State (Var 2)}
    (hsem : Program.sem (windowSeg (leftBlock (fLA l)) domLA tgA dt 1) σ ν) :
    ∀ j : Fin 2, ν (Rv j) = σ (Rv j) := by
  intro j
  refine windowSeg_mask (leftBlock (fLA l)) domLA tgA dt 1 (leftBlock_wf (fLA l))
    (htg_leftBlock (fLA l)) hsem (Rv j) ?_
  intro h
  simp only [DLCalTiming.clk, ODESystem.bound, List.map_append, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLA l) _ (by simpa [ODESystem.bound] using h)
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact absurd h (by simp [Rv, tgA, Prod.ext_iff])

/-! ## The right-only repositioning run -/

theorem sem_rate_run (q : ℕ) (hq : q < 2) (τ : ℝ) (hτ : 0 ≤ τ) {μ : State (Var 2)}
    (hdom : Formula.sat domRA μ) (hend : μ (Rv 0) + cA q * τ ≤ 6/5) :
    Program.sem (Program.ode (rightBlock (fRA q) (Term.const 1)) domRA) μ
      (rateCurve 0 (cA q) μ τ) := by
  refine sem_rightBlock_rate (fRA q) 0 (cA q) (fRA0_eval q hq) ?_ domRA τ hτ μ ?_
  · intro j hj x
    have : j = 1 := by
      fin_cases j
      · exact absurd rfl hj
      · rfl
    subst this
    exact fRA1_eval q (by omega) x
  · intro t ht
    rw [sat_domRA, rateCurve_at]
    have h0 := (sat_domRA μ).mp hdom
    have hc := cA_nonneg q
    constructor
    · nlinarith [ht.1]
    · nlinarith [ht.2]

/-- **Reach the cut.** From any `domR` state in mode `q` (at `Hold`, inside its region),
one run of mode `q` ends at a `domR` state with `θ_R ≥ 0.6`, the left untouched: the
identity run if already there, else the rate run to exactly `0.6`. -/
theorem reachA (q : ℕ) (hq : q < 3) {ν : State (Var 2)} (hdom : Formula.sat domRA ν)
    (hreg : q = 2 → (3:ℝ)/5 ≤ ν (Rv 0)) :
    ∃ μ' : State (Var 2),
      Program.sem (Program.ode (rightBlock (fRA q) (Term.const 1)) domRA) ν μ' ∧
      Formula.sat domRA μ' ∧ (∀ j : Fin 2, μ' (Lv j) = ν (Lv j)) ∧
      (3:ℝ)/5 ≤ μ' (Rv 0) := by
  by_cases h : (3:ℝ)/5 ≤ ν (Rv 0)
  · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRA q) (lam := Term.const 1)
      (domR := domRA) hdom
    rw [hρ] at hsem
    exact ⟨ν, hsem, hdom, fun _ => rfl, h⟩
  · rw [not_le] at h
    have hq2 : q < 2 := by
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · exact hq2
      · exfalso
        have : q = 2 := by omega
        linarith [hreg this]
    have hc := cA_pos q hq2
    set τ : ℝ := (3/5 - ν (Rv 0)) / cA q with hτdef
    have hτ : 0 ≤ τ := div_nonneg (by linarith) hc.le
    have hend : ν (Rv 0) + cA q * τ = 3/5 := by
      rw [hτdef, mul_div_cancel₀ _ hc.ne']; ring
    have hrun := sem_rate_run q hq2 τ hτ hdom (by rw [hend]; norm_num)
    refine ⟨rateCurve 0 (cA q) ν τ, hrun, sem_ode_ends_in_domain hrun, ?_, ?_⟩
    · intro j
      exact rateCurve_other 0 (cA q) ν τ (by simp [Lv, Rv, Prod.ext_iff])
    · rw [rateCurve_at, hend]

/-! ## The response -/

theorem respondA (l : ℕ) (_hl : l < 2) (dt : ℝ) (_hdt : 0 ≤ dt) (q : ℕ) (hq : q < 3)
    (rest : List (Program (Var 2)))
    (hrest : ∀ Q ∈ rest, ∀ μ : State (Var 2), Formula.sat domRA μ → Program.sem Q μ μ)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (FM gA []) envA) σ)
    (hreg : Formula.sat (regionsA q) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLA l)) domLA tgA dt 1)
      (bigSeq (Program.ode (rightBlock (fRA q) (Term.const 1)) domRA :: rest))
      (Formula.and (Formula.and (FM gA []) envA) (regionsA 2))) σ := by
  rw [faModal_sat]
  intro ν hleft
  have hdomLν : Formula.sat domLA ν :=
    windowSeg_end_domL (leftBlock (fLA l)) domLA tgA dt 1 (by norm_num) hleft
  have hmask := window_maskA l dt hleft
  have hθL : ν (Lv 0) ≤ 13/20 := ((sat_domLA ν).mp hdomLν).2.1
  have hdomRν : Formula.sat domRA ν := by
    rw [sat_domRA, hmask 0]; exact (sat_domRA σ).mp hσ.2.2
  obtain ⟨μfin, hrun, hdomμ, hLeq, hR⟩ := reachA q hq hdomRν (by
    intro hq2; subst hq2
    rw [hmask 0]; exact (sat_regionsA2 σ).mp hreg)
  have hseq : Program.sem
      (bigSeq (Program.ode (rightBlock (fRA q) (Term.const 1)) domRA :: rest)) ν μfin :=
    ⟨μfin, hrun, sem_bigSeq_identity domRA rest hrest μfin hdomμ⟩
  refine ⟨μfin, by rw [Program.rename_refl]; exact hseq, ⟨⟨?_, ?_, hdomμ⟩, ?_⟩⟩
  · rw [sat_FM_iff]
    intro g' hg'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    subst hg'
    rw [eval_gA, hLeq 0]
    linarith
  · rw [sat_domLA, hLeq 0, hLeq 1]
    exact (sat_domLA ν).mp hdomLν
  · rw [sat_regionsA2]
    exact hR

/-! ## The step provider -/

theorem GrA_modeAt' (q : ℕ) (hq : q < 3) : GrA.modeAt q = some (modeA q) := by
  interval_cases q <;> rfl

theorem HmultiA (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ P ∈ leftProgsA dt, ∀ (q : ℕ), q < GrA.modes.length → ∀ σ, σ mvA = (q : ℝ) →
      Formula.sat (Formula.and (FM gA []) envA) σ → Formula.sat (regionsA q) σ →
      ∃ segs : List (ℕ × RMode (Var 2) × REdge (Var 2)),
        (∀ s ∈ segs, GrA.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrA.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 2)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FM gA []) envA) (regionsA (qfOf segs q)))) σ := by
  intro P hP q hq σ hmv hσ hreg
  have hq3 : q < 3 := by simpa [GrA] using hq
  simp only [leftProgsA, leftDataA, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  have hsingle : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2)),
      List.IsChain (fun a b => a.2.2.tgt = b.1) [a] := by
    intro a; simp
  have hstep : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2))
      (b : ℕ × RMode (Var 2) × REdge (Var 2)) rest,
      a.2.2.tgt = b.1 → List.IsChain (fun x y => x.2.2.tgt = y.1) (b :: rest) →
      List.IsChain (fun x y => x.2.2.tgt = y.1) (a :: b :: rest) := by
    intro a b rest hab hrest
    refine hrest.cons ?_
    intro y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact hab
  have hhead1 : ∀ (a : ℕ × RMode (Var 2) × REdge (Var 2)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  have halign : ∀ st tg, edgeA st tg ∈ GrA.edges → st < 3 →
      GrA.modeAt st = some (modeA st) ∧ edgeA st tg ∈ GrA.edgesFrom st := by
    intro st tg he hst
    exact ⟨GrA_modeAt' st hst, edgeA_from he⟩
  have hid : ∀ q', q' < 3 → ∀ μ : State (Var 2), Formula.sat domRA μ →
      Program.sem (Program.ode (rightBlock (fRA q') (Term.const 1)) domRA) μ μ := by
    intro q' _ μ hμ
    obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRA q') (lam := Term.const 1)
      (domR := domRA) hμ
    rwa [hρ] at hsem
  have hbuild : ∀ (l : ℕ), l < 2 → P = windowSeg (leftBlock (fLA l)) domLA tgA dt 1 →
      ∃ segs : List (ℕ × RMode (Var 2) × REdge (Var 2)),
        (∀ s ∈ segs, GrA.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrA.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 2)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FM gA []) envA) (regionsA (qfOf segs q)))) σ := by
    intro l hl hPeq
    subst hPeq
    interval_cases q
    · -- ApproachFast: flow to 0.6, hop Slow, Hold
      refine ⟨[(0, modeA 0, edgeA 0 1), (1, modeA 1, edgeA 1 2), (2, modeA 2, edgeA 2 2)],
        ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact halign 0 1 (by simp [GrA]) (by norm_num)
        · exact halign 1 2 (by simp [GrA]) (by norm_num)
        · exact halign 2 2 (by simp [GrA]) (by norm_num)
      · exact hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _))
      · exact fun s hs => by rw [hhead1 _ _ _ hs]
      · have hq2 : qfOf [(0, modeA 0, edgeA 0 1), (1, modeA 1, edgeA 1 2),
            (2, modeA 2, edgeA 2 2)] 0 = 2 := rfl
        rw [hq2]
        have := respondA l hl dt hdt 0 (by norm_num)
          [Program.ode (rightBlock (fRA 1) (Term.const 1)) domRA,
           Program.ode (rightBlock (fRA 2) (Term.const 1)) domRA]
          (by
            intro Q hQ μ hμ
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            rcases hQ with rfl | rfl
            · exact hid 1 (by norm_num) μ hμ
            · exact hid 2 (by norm_num) μ hμ)
          hσ hreg
        simpa [modeA] using this
    · -- ApproachSlow: flow to 0.6, hop Hold
      refine ⟨[(1, modeA 1, edgeA 1 2), (2, modeA 2, edgeA 2 2)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact halign 1 2 (by simp [GrA]) (by norm_num)
        · exact halign 2 2 (by simp [GrA]) (by norm_num)
      · exact hstep _ _ _ rfl (hsingle _)
      · exact fun s hs => by rw [hhead1 _ _ _ hs]
      · have hq2 : qfOf [(1, modeA 1, edgeA 1 2), (2, modeA 2, edgeA 2 2)] 1 = 2 := rfl
        rw [hq2]
        have := respondA l hl dt hdt 1 (by norm_num)
          [Program.ode (rightBlock (fRA 2) (Term.const 1)) domRA]
          (by
            intro Q hQ μ hμ
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            subst hQ
            exact hid 2 (by norm_num) μ hμ)
          hσ hreg
        simpa [modeA] using this
    · -- Hold: already in the region; the self-edge piece (identity run)
      refine ⟨[(2, modeA 2, edgeA 2 2)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact halign 2 2 (by simp [GrA]) (by norm_num)
      · exact hsingle _
      · exact fun s hs => by rw [hhead1 _ _ _ hs]
      · have hq2 : qfOf [(2, modeA 2, edgeA 2 2)] 2 = 2 := rfl
        rw [hq2]
        have := respondA l hl dt hdt 2 (by norm_num) [] (by simp) hσ hreg
        simpa [modeA] using this
  rcases hP with rfl | rfl
  · exact hbuild 0 (by norm_num) rfl
  · exact hbuild 1 (by norm_num) rfl

/-! ## The gate -/

/-- **`plant_fan_mid`, modal Theorem 3 at the DECLARED invariant** `θ_L ≤ θ_R + 0.3`,
with the checked cut `θ_R ≥ 0.6` carried as the region of the `Hold` mode only
(`mvRegionR mvA regionsA 3`; `⊤` at the approach modes). Right-only catch-up response;
no Z3 verdict is involved. -/
theorem plant_fan_mid_declared (dt : ℝ) (hdt : 0 ≤ dt) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInvM gA []) (envLR domLA domRA))
        (mvRegionR mvA regionsA GrA.modes.length))) := by
  refine theorem3_faithful_multiR_LR GrA mvA (FM gA []) domLA domRA regionsA
    (leftProgsA dt) (canonInvM gA []) (encode_canonInvM gA []) ?_ ?_ ?_
  · exact hdis_multi GrA 0 1 dt leftDataA (by decide) httA hRvA hLA
  · exact hstep_assembled_multiR GrA mvA (FM gA []) envA regionsA (leftProgsA dt)
      hmvFA' hmvenvA hmvregA hfreshA httA hltA (hframesA dt) (HmultiA dt hdt)
  · exact hddF_multiR_plain GrA 0 1 dt leftDataA regionsA (canonInvM gA []) domLA domRA
      (by decide) httA hRvA hLA (fun q _ => regionsA_fv q)
      (canonInvM_varsL gA [] (by
        intro g' hg'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        subst hg'; exact hgA))
      (canonInvM_varsR gA []) hdomLA hdomRA

end PlantFanMidDeclared
end RelCertifier
