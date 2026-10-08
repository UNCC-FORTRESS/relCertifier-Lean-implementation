/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `plant_fan_high` (identical right system to `arm_chain_rung3`) — the DECLARED invariant, with the checked cut as `Hold`'s region

`PlantFanHighModal.plant_fan_high_modal` states Theorem 3 at `θ_R ≥ 0.6 ∧ θ_L ≤ θ_R +
0.15`: the `Hold` guard atom — the tool's CHECKED CUT for the `Hold` pairing — conjoined
to the declared invariant for every right mode. This leaf states the declared invariant
`θ_L ≤ θ_R + 0.15` itself, with the cut carried only where the tool checked it: as the
region of the `Hold` mode in the mode-region bookkeeping `mvRegionR` (`regionsA 3 = ⌊θ_R
≥ 0.6⌋`, `⊤` at `ApproachA/B/C`). From every state satisfying the declared invariant with
the right in `ApproachA`, `ApproachB` or `ApproachC` — any `θ_R` in the evolve domain —
and from every state in `Hold` inside its region, the refinement is maintained.

The plain-`mvValid` form (no region anywhere) is FALSE: at `mv = Hold`, `θ_R = 0.3`,
`θ_L = 0.45`, `v_L = 0.3` the invariant holds, the left `Accelerate` window raises `θ_L`
immediately, and `Hold`'s field `θ' = 0` with `next = [Hold]` leaves the right no run
that moves — so no response exists (`docs/CUT-COMPOSITION.md`). The region at `Hold`
is exactly what the two cut obligations compose to: O1 (entry — a switch into `Hold`
satisfies its guard, the trust base's guard-gated switching) and O2 (invariance along
`Hold`'s own field).

**The response (catch-up, Z3-free).** `faModal`'s `⟨…⟩` side runs after the left window,
so the right answers with a right-only flow: in the start mode `q` it flows at that
mode's constant rate (`½`, `7/20`, `⅕`; `0` in `Hold`) for exactly the duration that
brings `θ_R` to `0.6` (zero if already there), then hops — zero-duration runs along the
declared chain — into `Hold`. The invariant at the end is endpoint arithmetic: the left
window ends inside its evolve domain (`θ_L ≤ 0.65`, `windowSeg_end_domL`), the right has
`θ_R ≥ 0.6`, and `0.65 ≤ 0.6 + 0.15`. The repositioning is the tool's `checkDynRepo`
route-A certificate (`Lie(θ_L − θ_R − 0.15) = −c_q ≤ 0` with the left frozen) written
down as the explicit curve `rateCurve` (`Proofs/Encoding/CutComposition.lean`) instead
of taken from Z3; the `Hold` phase is the same arithmetic that makes the conditioned
instance's route-B/C `Hold` queries unsat. No verdict hypothesis remains: the theorem
audits to the three standard axioms.

The hop into `Hold` is always taken at `θ_R ≥ 0.6` — the lower bound of `Hold`'s guard.
The statement's automaton carries `⊤` edge guards like every other modal instance
(`docs/COVER-AUDIT.md`, the ⊤-guard note), so intermediate hops are not guard-tested.
-/
import RelCertifier.Instances.PlantFanHighModal
import RelCertifier.Proofs.Encoding.EnvelopeChainR
import RelCertifier.Proofs.Encoding.RepoPrefixR
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.CutComposition

namespace RelCertifier
namespace PlantFanHighDeclared

open DL DLCalTiming DLRel Parse Set PlantFanHighModal

/-! ## The mode regions: the checked cut at `Hold` (index 3), `⊤` elsewhere -/

/-- `Hold`'s region is its guard atom `θ_R ≥ 0.6` — `invLe regA`, the cut the tool
checked (O1 entry, O2 invariance); the approach modes carry no region. -/
noncomputable def regionsA (q : ℕ) : Formula (Var 2) :=
  if q = 3 then invLe regA else Formula.tt

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

theorem sat_regionsA3 (x : State (Var 2)) :
    Formula.sat (regionsA 3) x ↔ (3:ℝ)/5 ≤ x (Rv 0) := by
  simp [regionsA, regA, Term.eval, AOp.interp]

theorem hmvFA' : mvA ∉ (FM gA []).fv := notMem_FM_fv (by
  intro g' hg' h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
  subst hg'
  exact hmvgA h)

/-! ## Parse pins -/

theorem hpr065 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hprm045 : Run.parseRat "-0.45" = some (-(9:ℚ)/20) := by
  have h : parseQ "-0.45" = some (⟨-45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpr045 : Run.parseRat "0.45" = some ((9:ℚ)/20) := by
  have h : parseQ "0.45" = some (⟨45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpr015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpr05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpr035 : Run.parseRat "0.35" = some ((7:ℚ)/20) := by
  have h : parseQ "0.35" = some (⟨35, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpr02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Shape pins: the domains, the invariant term, the right rates -/

theorem sat_domLA (x : State (Var 2)) : Formula.sat domLA x ↔
    (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 13/20 ∧ -(9:ℝ)/20 ≤ x (Lv 1) ∧ x (Lv 1) ≤ 9/20) := by
  simp only [domLA, hostEvolve, mLA, plant_fan_high_IR, vsA]
  simp [Run.lowerF, Run.lowerE, hpr00, hpr065, hprm045, hpr045, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp,
    Term.eval, Lv]
  tauto

theorem sat_domRA (x : State (Var 2)) : Formula.sat domRA x ↔
    (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 6/5) := by
  rw [domRA_shape]
  simp [Formula.sat, CompOp.interp, Term.eval, Rv]

theorem eval_gA (x : State (Var 2)) :
    Term.eval gA x = x (Lv 0) - (x (Rv 0) + 3/20) := by
  have hdL : ("L_theta".drop 2).copy = "theta" := by decide
  have hdR : ("R_theta".drop 2).copy = "theta" := by decide
  simp [gA, plant_fan_high_IR, Run.invToG, Run.lowerE, vsA, hpr015,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, ITerm.toHost,
    Term.eval, AOp.interp, Lv, Rv]

/-- The right modes' constant rates: `½`, `7/20`, `⅕`, `0`. -/
noncomputable def cA (q : ℕ) : ℝ :=
  if q = 0 then 1/2 else if q = 1 then 7/20 else if q = 2 then 1/5 else 0

theorem cA_nonneg (q : ℕ) : 0 ≤ cA q := by
  unfold cA; split_ifs <;> norm_num

theorem cA_pos (q : ℕ) (hq : q < 3) : 0 < cA q := by
  interval_cases q <;> simp [cA]

theorem fRA0_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fRA q 0) x = cA q := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, plant_fan_high_IR, vsA, Run.dynOf, Run.lowerE, hpr05,
      hpr035, hpr02, hpr0, List.finRange, ITerm.toHost, Term.eval, cA]

theorem fRA1_eval (q : ℕ) (hq : q < 4) (x : State (Var 2)) :
    Term.eval (fRA q 1) x = 0 := by
  interval_cases q <;>
    simp [fRA, hostDyn, mRA, plant_fan_high_IR, vsA, Run.dynOf, Run.lowerE, hpr05,
      hpr035, hpr02, hpr0, List.finRange, ITerm.toHost, Term.eval]

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

/-- The right coordinates survive the left window verbatim. -/
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

/-- In mode `q`, from `μ ∈ domR`, flowing for `τ` keeps the domain whenever the endpoint
does (the curve is monotone in `θ_R`). -/
theorem sem_rate_run (q : ℕ) (hq : q < 4) (τ : ℝ) (hτ : 0 ≤ τ) {μ : State (Var 2)}
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
    exact fRA1_eval q hq x
  · intro t ht
    rw [sat_domRA, rateCurve_at]
    have h0 := (sat_domRA μ).mp hdom
    have hc := cA_nonneg q
    constructor
    · nlinarith [ht.1]
    · nlinarith [ht.2]

/-! ## The response: reposition to `θ_R ≥ 0.6`, hop into `Hold`, endpoint arithmetic -/

/-- Window `l`, start mode `q`: one rate run in `q` to `θ_R ≥ 0.6`, then any list of
zero-duration hops (identity runs on `domR` states). The target carries `Hold`'s region.
`hreg` is the start region: at `Hold` (`q = 3`) the region `θ_R ≥ 0.6` is given. -/
theorem respondA (l : ℕ) (_hl : l < 2) (dt : ℝ) (_hdt : 0 ≤ dt) (q : ℕ) (hq : q < 4)
    (rest : List (Program (Var 2)))
    (hrest : ∀ Q ∈ rest, ∀ μ : State (Var 2), Formula.sat domRA μ → Program.sem Q μ μ)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (FM gA []) envA) σ)
    (hreg : Formula.sat (regionsA q) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fLA l)) domLA tgA dt 1)
      (bigSeq (Program.ode (rightBlock (fRA q) (Term.const 1)) domRA :: rest))
      (Formula.and (Formula.and (FM gA []) envA) (regionsA 3))) σ := by
  rw [faModal_sat]
  intro ν hleft
  have hdomLν : Formula.sat domLA ν :=
    windowSeg_end_domL (leftBlock (fLA l)) domLA tgA dt 1 (by norm_num) hleft
  have hmask := window_maskA l dt hleft
  have hθL : ν (Lv 0) ≤ 13/20 := ((sat_domLA ν).mp hdomLν).2.1
  have hdomRσ : Formula.sat domRA σ := hσ.2.2
  have hdomRν : Formula.sat domRA ν := by
    rw [sat_domRA, hmask 0]; exact (sat_domRA σ).mp hdomRσ
  have hRν := (sat_domRA ν).mp hdomRν
  -- the repositioning duration
  obtain ⟨τ, hτ, hlo, hhi⟩ : ∃ τ : ℝ, 0 ≤ τ ∧ (3:ℝ)/5 ≤ ν (Rv 0) + cA q * τ ∧
      ν (Rv 0) + cA q * τ ≤ 6/5 := by
    by_cases h : (3:ℝ)/5 ≤ ν (Rv 0)
    · exact ⟨0, le_rfl, by simpa using h, by simpa using hRν.2⟩
    · rw [not_le] at h
      have hq3 : q < 3 := by
        rcases Nat.lt_or_ge q 3 with hq3 | hq3
        · exact hq3
        · exfalso
          have : q = 3 := by omega
          subst this
          have := (sat_regionsA3 σ).mp hreg
          rw [hmask 0] at h
          linarith
      have hc := cA_pos q hq3
      refine ⟨(3/5 - ν (Rv 0)) / cA q, div_nonneg (by linarith) hc.le, ?_, ?_⟩
      · rw [mul_div_cancel₀ _ hc.ne']; linarith
      · rw [mul_div_cancel₀ _ hc.ne']; norm_num
  have hrun := sem_rate_run q hq τ hτ hdomRν hhi
  set μfin := rateCurve 0 (cA q) ν τ with hμfin
  have hdomμ : Formula.sat domRA μfin := sem_ode_ends_in_domain hrun
  have hseq : Program.sem
      (bigSeq (Program.ode (rightBlock (fRA q) (Term.const 1)) domRA :: rest)) ν μfin :=
    ⟨μfin, hrun, sem_bigSeq_identity domRA rest hrest μfin hdomμ⟩
  have hL0 : μfin (Lv 0) = ν (Lv 0) :=
    rateCurve_other 0 (cA q) ν τ (by simp [Lv, Rv, Prod.ext_iff])
  have hL1 : μfin (Lv 1) = ν (Lv 1) :=
    rateCurve_other 0 (cA q) ν τ (by simp [Lv, Rv, Prod.ext_iff])
  have hR0 : μfin (Rv 0) = ν (Rv 0) + cA q * τ := rateCurve_at 0 (cA q) ν τ
  refine ⟨μfin, by rw [Program.rename_refl]; exact hseq, ⟨⟨?_, ?_, hdomμ⟩, ?_⟩⟩
  · -- the declared invariant at the endpoint
    rw [sat_FM_iff]
    intro g' hg'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    subst hg'
    rw [eval_gA, hL0, hR0]
    linarith
  · -- the left evolve domain at the endpoint (left coordinates untouched)
    rw [sat_domLA, hL0, hL1]
    exact (sat_domLA ν).mp hdomLν
  · -- `Hold`'s region at the endpoint
    rw [sat_regionsA3, hR0]
    exact hlo

/-! ## The step provider -/

theorem GrA_modeAt' (q : ℕ) (hq : q < 4) : GrA.modeAt q = some (modeA q) := by
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
  have hq4 : q < 4 := by simpa [GrA] using hq
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
  have halign : ∀ st tg, edgeA st tg ∈ GrA.edges → st < 4 →
      GrA.modeAt st = some (modeA st) ∧ edgeA st tg ∈ GrA.edgesFrom st := by
    intro st tg he hst
    exact ⟨GrA_modeAt' st hst, edgeA_from he⟩
  -- the zero-duration hops: identity runs of the modes' own programs
  have hid : ∀ q', q' < 4 → ∀ μ : State (Var 2), Formula.sat domRA μ →
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
    · -- ApproachA: flow to 0.6, hop B, C, Hold
      refine ⟨[(0, modeA 0, edgeA 0 1), (1, modeA 1, edgeA 1 2), (2, modeA 2, edgeA 2 3),
        (3, modeA 3, edgeA 3 3)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl
        · exact halign 0 1 (by simp [GrA]) (by norm_num)
        · exact halign 1 2 (by simp [GrA]) (by norm_num)
        · exact halign 2 3 (by simp [GrA]) (by norm_num)
        · exact halign 3 3 (by simp [GrA]) (by norm_num)
      · exact hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _)))
      · exact fun s hs => by rw [hhead1 _ _ _ hs]
      · have hq3 : qfOf [(0, modeA 0, edgeA 0 1), (1, modeA 1, edgeA 1 2),
            (2, modeA 2, edgeA 2 3), (3, modeA 3, edgeA 3 3)] 0 = 3 := rfl
        rw [hq3]
        have := respondA l hl dt hdt 0 (by norm_num)
          [Program.ode (rightBlock (fRA 1) (Term.const 1)) domRA,
           Program.ode (rightBlock (fRA 2) (Term.const 1)) domRA,
           Program.ode (rightBlock (fRA 3) (Term.const 1)) domRA]
          (by
            intro Q hQ μ hμ
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            rcases hQ with rfl | rfl | rfl
            · exact hid 1 (by norm_num) μ hμ
            · exact hid 2 (by norm_num) μ hμ
            · exact hid 3 (by norm_num) μ hμ)
          hσ hreg
        simpa [modeA] using this
    · -- ApproachB: flow to 0.6, hop C, Hold
      refine ⟨[(1, modeA 1, edgeA 1 2), (2, modeA 2, edgeA 2 3), (3, modeA 3, edgeA 3 3)],
        ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact halign 1 2 (by simp [GrA]) (by norm_num)
        · exact halign 2 3 (by simp [GrA]) (by norm_num)
        · exact halign 3 3 (by simp [GrA]) (by norm_num)
      · exact hstep _ _ _ rfl (hstep _ _ _ rfl (hsingle _))
      · exact fun s hs => by rw [hhead1 _ _ _ hs]
      · have hq3 : qfOf [(1, modeA 1, edgeA 1 2), (2, modeA 2, edgeA 2 3),
            (3, modeA 3, edgeA 3 3)] 1 = 3 := rfl
        rw [hq3]
        have := respondA l hl dt hdt 1 (by norm_num)
          [Program.ode (rightBlock (fRA 2) (Term.const 1)) domRA,
           Program.ode (rightBlock (fRA 3) (Term.const 1)) domRA]
          (by
            intro Q hQ μ hμ
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            rcases hQ with rfl | rfl
            · exact hid 2 (by norm_num) μ hμ
            · exact hid 3 (by norm_num) μ hμ)
          hσ hreg
        simpa [modeA] using this
    · -- ApproachC: flow to 0.6, hop Hold
      refine ⟨[(2, modeA 2, edgeA 2 3), (3, modeA 3, edgeA 3 3)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact halign 2 3 (by simp [GrA]) (by norm_num)
        · exact halign 3 3 (by simp [GrA]) (by norm_num)
      · exact hstep _ _ _ rfl (hsingle _)
      · exact fun s hs => by rw [hhead1 _ _ _ hs]
      · have hq3 : qfOf [(2, modeA 2, edgeA 2 3), (3, modeA 3, edgeA 3 3)] 2 = 3 := rfl
        rw [hq3]
        have := respondA l hl dt hdt 2 (by norm_num)
          [Program.ode (rightBlock (fRA 3) (Term.const 1)) domRA]
          (by
            intro Q hQ μ hμ
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
            subst hQ
            exact hid 3 (by norm_num) μ hμ)
          hσ hreg
        simpa [modeA] using this
    · -- Hold: already in the region; the self-edge piece (zero rate)
      refine ⟨[(3, modeA 3, edgeA 3 3)], ?_, ?_, ?_, ?_⟩
      · intro s hs
        rw [List.mem_singleton] at hs
        subst hs
        exact halign 3 3 (by simp [GrA]) (by norm_num)
      · exact hsingle _
      · exact fun s hs => by rw [hhead1 _ _ _ hs]
      · have hq3 : qfOf [(3, modeA 3, edgeA 3 3)] 3 = 3 := rfl
        rw [hq3]
        have := respondA l hl dt hdt 3 (by norm_num) [] (by simp) hσ hreg
        simpa [modeA] using this
  rcases hP with rfl | rfl
  · exact hbuild 0 (by norm_num) rfl
  · exact hbuild 1 (by norm_num) rfl

/-! ## The gate -/

/-- **`plant_fan_high`, modal Theorem 3 at the DECLARED invariant** `θ_L ≤ θ_R + 0.15`,
with the checked cut `θ_R ≥ 0.6` carried as the region of the `Hold` mode only
(`mvRegionR mvA regionsA 4`; `⊤` at the approach modes). The response is the right-only
catch-up above; no Z3 verdict is involved. -/
theorem plant_fan_high_declared (dt : ℝ) (hdt : 0 ≤ dt) :
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

end PlantFanHighDeclared
end RelCertifier
