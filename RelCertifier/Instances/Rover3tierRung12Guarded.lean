/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_rung12` over the GUARDED right automaton — Theorem 3 by catch-up

`Rover3tierRung12Handoff` states the mode-keyed Theorem 3 over the `⊤`-guarded right graph
`GrQ`: its response stays in the start mode for 7 (`ACCEL`) or 4 (`COAST`) coupled pieces with
a self-loop between pieces, and a stay `ACCEL → ACCEL` needs `0.3 ≤ v_R < 0.6`, which the
right leaves while accelerating (and the bookkeeping `mvValid` does not even place `v_R` in
`[0.3, 0.6)` at the start).

This file states the same theorem (the declared mode-keyed rows, the left automaton
`ACCEL ↔ COAST` of the file, the envelope, `mvValid`) over the GUARDED graph `GrG` — every
edge tests the lowered guard of the mode it enters (`GrG_guards`) — and builds the response
directly from the model: both right modes have `v' = a`, `s' = v`, `a' = 0` with
`a ∈ [0.5, 1]`, and both rows bound the left from above by an increasing function of `v_R`
(`v_L ≤ v_R + 0.5`, `3 v_L + a_L ≤ 3 v_R + 1.2`). After the left window the right flows in its
current mode (explicit solution) until `v_R = b`, the least value `≥ max(v_R, 0.3)` that makes
the row hold, and switches there into the mode whose guard contains `b` (`ACCEL` below `0.6`,
`COAST` from `0.6`): a legal switch by the explicit end state. No verdict pack is needed.
-/
import RelCertifier.Instances.Rover3tierRung12Handoff
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.LadderReplay
import RelCertifier.Proofs.Encoding.ReplayComps
import RelCertifier.Proofs.Encoding.ReplayModeKeyed
import RelCertifier.InstancesV2.Cuts.rover3tier_rung12

namespace RelCertifier
namespace Rover3tierRung12Guarded

open DL DLCalTiming DLRel Parse Set Rover3tierRung12Modal Rover3tierRung12Handoff RelCertifier.Oracle

/-! ## The guarded right graph -/

/-- The declared edge `st → tgt` tests the lowered guard of the mode it enters. -/
noncomputable def edgeG (st tgt : ℕ) : REdge (Var 3) :=
  { src := st, tgt := tgt, guard := hostGuard vsQ 3 Side.R (mRQ tgt), pruned := false }

noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeQ 0, modeQ 1],
    edges := [edgeG 0 1, edgeG 0 0, edgeG 1 0, edgeG 1 1] }

/-- **Faithfulness of the graph**: its edges are the file's `next` lists, resolved. -/
theorem GrG_edges_IR : GrG.edges.map (fun e => (e.src, e.tgt)) =
    (List.range rover3tier_rung12_IR.R.modes.length).flatMap (fun q =>
      (mRQ q).next.map (fun nm => (q, rover3tier_rung12_IR.R.modes.findIdx (·.name == nm)))) := by
  have : (List.range rover3tier_rung12_IR.R.modes.length).flatMap (fun q =>
      (mRQ q).next.map (fun nm => (q, rover3tier_rung12_IR.R.modes.findIdx (·.name == nm))))
      = [(0, 1), (0, 0), (1, 0), (1, 1)] := by decide
  rw [this]; rfl

/-- **The graph is the guarded automaton**: every declared edge tests the lowered guard of the
mode it enters. -/
theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q,
    e.guard = hostGuard vsQ 3 Side.R (mRQ e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 2) : GrG.modeAt q = some (modeQ q) := by
  interval_cases q <;> rfl

theorem GrG_len : GrG.modes.length = 2 := rfl

theorem hltG : ∀ q, ∀ e ∈ GrG.edgesFrom q, e.tgt < GrG.modes.length := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> norm_num [GrG, edgeG]

theorem hRvG : ∀ q m, GrG.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  have hqm : q < 2 ∧ m = modeQ q := by
    match q with
    | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
    | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])
  obtain ⟨hq2, rfl⟩ := hqm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fRQ q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fRQ q) (Term.const 1) (hfRQ q hq2)
      (by simp [Term.fv]) hy
  · exact hdomRQ hy

theorem hfreshG : ∀ q m, GrG.modeAt q = some m →
    mvQ ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardRQ (q : ℕ) (hq : q < 2) : (hostGuard vsQ 3 Side.R (mRQ q)).fv ⊆ range Rv :=
  hostGuard_fv_R vsQ (mRQ q) (by
    interval_cases q <;>
      simp [mRQ, rover3tier_rung12_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree])

theorem hgRG : GuardsRight GrG := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hguardRQ 1 (by norm_num)
  · exact hguardRQ 0 (by norm_num)
  · exact hguardRQ 0 (by norm_num)
  · exact hguardRQ 1 (by norm_num)

theorem edgeG_mem (st tgt : ℕ) (hst : st < 2) (htgt : tgt < 2) :
    edgeG st tgt ∈ GrG.edgesFrom st := by
  refine List.mem_filter.mpr ⟨?_, by simp [edgeG]⟩
  interval_cases st <;> interval_cases tgt <;> simp [GrG]

/-- The right guards, evaluated (`ACCEL`: `0.3 ≤ v < 0.6`; `COAST`: `v ≥ 0.6`). -/
theorem sat_guardRQ (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Formula.sat (hostGuard vsQ 3 Side.R (mRQ q)) x ↔
      (if q = 0 then 3/10 ≤ x (Rv 0) ∧ x (Rv 0) < 3/5 else 3/5 ≤ x (Rv 0)) := by
  interval_cases q <;>
    simp [hostGuard, mRQ, rover3tier_rung12_IR, Run.lowerF, Run.lowerE, hq03, hq06, vsQ,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

/-! ## The explicit right run: `v' = a`, `s' = v`, `a' = 0` -/

noncomputable def runEnd (ρ : State (Var 3)) (τ : ℝ) : State (Var 3) :=
  fun x => if x = Rv 0 then ρ (Rv 0) + ρ (Rv 2) * τ
    else if x = Rv 1 then ρ (Rv 1) + ρ (Rv 0) * τ + ρ (Rv 2) * τ ^ 2 / 2 else ρ x

theorem runEnd_ne (ρ : State (Var 3)) (τ : ℝ) {x : Var 3} (h0 : x ≠ Rv 0) (h1 : x ≠ Rv 1) :
    runEnd ρ τ x = ρ x := by simp [runEnd, h0, h1]

theorem runEnd_R0 (ρ : State (Var 3)) (τ : ℝ) : runEnd ρ τ (Rv 0) = ρ (Rv 0) + ρ (Rv 2) * τ := by
  simp [runEnd]
theorem runEnd_R1 (ρ : State (Var 3)) (τ : ℝ) :
    runEnd ρ τ (Rv 1) = ρ (Rv 1) + ρ (Rv 0) * τ + ρ (Rv 2) * τ ^ 2 / 2 := by
  simp [runEnd, show (Rv 1 : Var 3) ≠ Rv 0 from by simp [Rv, Prod.ext_iff]]
theorem runEnd_R2 (ρ : State (Var 3)) (τ : ℝ) : runEnd ρ τ (Rv 2) = ρ (Rv 2) :=
  runEnd_ne ρ τ (by simp [Rv, Prod.ext_iff]) (by simp [Rv, Prod.ext_iff])
theorem runEnd_L (ρ : State (Var 3)) (τ : ℝ) (i : Fin 3) : runEnd ρ τ (Lv i) = ρ (Lv i) :=
  runEnd_ne ρ τ (by simp [Lv, Rv, Prod.ext_iff]) (by simp [Lv, Rv, Prod.ext_iff])


/-- The explicit solution is a run of either right mode, for any duration. -/
theorem run_sol (q : ℕ) (hq : q < 2) (ρ : State (Var 3)) (hdom : Formula.sat domRQ ρ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ODESol (modeQ q).sys (modeQ q).dom ρ τ (fun t => runEnd ρ t) := by
  have hD := (sat_domRQ ρ).mp hdom
  refine ⟨hτ, ?_, ?_, ?_, ?_⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; simp [runEnd]
    · by_cases h1 : x = Rv 1
      · subst h1; simp [runEnd_R1]
      · exact runEnd_ne ρ 0 h0 h1
  · intro t ht p hp
    simp only [modeQ, rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    fin_cases i
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRQ q ⟨0, by norm_num⟩))
          (runEnd ρ t) = ρ (Rv 2) := by
        simp only [Term.eval, AOp.interp]
        rw [show fRQ q ⟨0, by norm_num⟩ = fRQ q 0 from rfl, fRQ0_eval q hq, runEnd_R2]
        ring
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => ρ (Rv 0) + ρ (Rv 2) * u) (ρ (Rv 2) * 1)
          (Set.Icc 0 τ) t :=
        ((hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)).const_mul (ρ (Rv 2))).const_add (ρ (Rv 0))
      rw [mul_one] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp [runEnd_R0]
      · simp [runEnd_R0]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRQ q ⟨1, by norm_num⟩))
          (runEnd ρ t) = ρ (Rv 0) + ρ (Rv 2) * t := by
        simp only [Term.eval, AOp.interp]
        rw [show fRQ q ⟨1, by norm_num⟩ = fRQ q 1 from rfl, fRQ1_eval q hq, runEnd_R0]
        ring
      simp only [heval]
      have h2 : HasDerivWithinAt (fun u : ℝ => ρ (Rv 1) + ρ (Rv 0) * u + ρ (Rv 2) * u ^ 2 / 2)
          (ρ (Rv 0) * 1 + ρ (Rv 2) * (2 * t ^ 1 * 1) / 2) (Set.Icc 0 τ) t := by
        have hu := hasDerivWithinAt_id t (Set.Icc (0:ℝ) τ)
        exact ((hu.const_mul (ρ (Rv 0))).const_add (ρ (Rv 1))).add
          (((hu.pow 2).const_mul (ρ (Rv 2))).div_const 2)
      have he : ρ (Rv 0) * 1 + ρ (Rv 2) * (2 * t ^ 1 * 1) / 2 = ρ (Rv 0) + ρ (Rv 2) * t := by
        ring
      rw [he] at h2
      refine HasDerivWithinAt.congr h2 ?_ ?_
      · intro y _; simp [runEnd_R1]
      · simp [runEnd_R1]
    · have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (fRQ q ⟨2, by norm_num⟩))
          (runEnd ρ t) = 0 := by
        simp only [Term.eval, AOp.interp]
        rw [show fRQ q ⟨2, by norm_num⟩ = fRQ q 2 from rfl, fRQ2_eval q hq]
        ring
      simp only [heval]
      refine HasDerivWithinAt.congr (hasDerivWithinAt_const t (Set.Icc (0:ℝ) τ) (ρ (Rv 2)))
        ?_ ?_
      · intro y _; simp [runEnd_R2]
      · simp [runEnd_R2]
  · intro t ht x hx
    have h0 : x ≠ Rv 0 := by
      rintro rfl
      exact hx (List.mem_map.mpr ⟨(Rv 0, _), List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩,
        rfl⟩)
    have h1 : x ≠ Rv 1 := by
      rintro rfl
      exact hx (List.mem_map.mpr ⟨(Rv 1, _), List.mem_map.mpr ⟨1, List.mem_finRange 1, rfl⟩,
        rfl⟩)
    exact runEnd_ne ρ t h0 h1
  · intro t ht
    refine (sat_domRQ _).mpr ?_
    simp only [runEnd_R2, runEnd_R1, runEnd_R0]
    obtain ⟨ha1, ha2, hs, hv⟩ := hD
    have ht0 := ht.1
    refine ⟨ha1, ha2, ?_, ?_⟩
    · have : 0 ≤ ρ (Rv 0) * t := mul_nonneg hv ht0
      have : 0 ≤ ρ (Rv 2) * t ^ 2 / 2 := by positivity
      linarith
    · have : 0 ≤ ρ (Rv 2) * t := mul_nonneg (by linarith) ht0
      linarith

/-! ## The emitted cover's data: the extended cut certificate, concretely -/

noncomputable def guardQ (l : ℕ) : Formula (Var 3) := hostGuard vsQ 3 Side.L (mLQ l)

theorem hguardL (l : ℕ) (hl : l < 2) : (guardQ l).fv ⊆ range Lv :=
  hostGuard_fv_L vsQ (mLQ l) (by
    interval_cases l <;>
      simp [mLQ, rover3tier_rung12_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree])

noncomputable def cL (l : ℕ) : List (CutAtomP 3) :=
  cutPairsX vsQ 3 Side.L (cutAtomsOfX rover3tier_rung12_cutsV2X.L (mLQ l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 3) :=
  cutPairsX vsQ 3 Side.R (cutAtomsOfX rover3tier_rung12_cutsV2X.R (mRQ q).name)

def aV (k : String) : PForm := .cmp ">=" (.var "v") (.num k)
def vStr (q : ℕ) : String := if q = 0 then "0.3" else "0.6"
noncomputable def vK (q : ℕ) : ℝ := if q = 0 then 3/10 else 3/5

theorem cL_nil (l : ℕ) (hl : l < 2) : cL l = [] := by interval_cases l <;> rfl

theorem gR_v (q : ℕ) (hq : q < 2) : hostAtomG vsQ 3 Side.R (aV (vStr q)) = thrGe (Rv 0) (vK q) := by
  interval_cases q <;>
  simp [aV, vStr, vK, hostAtomG, cutAtomG, Run.lowerE, hq03, hq06, vsQ,
    Run.resolveVar, List.findIdx?_cons, ITerm.toHost, thrGe, Rv]

theorem cR_eq (q : ℕ) (hq : q < 2) :
    cR q = [(hostAtomF vsQ 3 Side.R (aV (vStr q)), thrGe (Rv 0) (vK q))] := by
  rw [← gR_v q hq]; interval_cases q <;> rfl

theorem hiffL (l : ℕ) (hl : l < 2) : AtomsIff (cL l) := by
  rw [cL_nil l hl]; intro a ha; simp at ha

theorem hiffR (q : ℕ) (hq : q < 2) : AtomsIff (cR q) := by
  rw [cR_eq q hq]
  intro a ha ν
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  rw [← gR_v q hq]; exact hostAtom_iff (Or.inr rfl) ν

theorem cutSat_nil (ν : State (Var 3)) : CutSat ([] : List (CutAtomP 3)) ν := by
  intro a ha; simp at ha

/-! ## O1: the right guards imply the kept atoms (the extended certificate, kernel-checked) -/

theorem hO1R (q : ℕ) (hq : q < 2) :
    ∀ ν, Formula.sat (hostGuard vsQ 3 Side.R (mRQ q)) ν → CutSat (cR q) ν := by
  intro ν hν
  refine cutSatR_of_guard rover3tier_rung12_cutsV2X_wf (mRQ q) ?_ ?_ ?_ ?_ ν hν
  · interval_cases q <;> rfl
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, rover3tier_rung12_cutsV2X, mRQ, rover3tier_rung12_IR] at hx
      rcases hx with rfl <;> simp
  · interval_cases q <;>
    · intro x hx
      simp [cutAtomsOfX, rover3tier_rung12_cutsV2X, mRQ, rover3tier_rung12_IR] at hx
      rcases hx with rfl <;>
        simp [Run.lowerF, Run.lowerE, hq03, hq06, vsQ, Run.resolveVar, List.findIdx?_cons]
  · interval_cases q <;>
      simp [mRQ, rover3tier_rung12_IR, Run.lowerF, Run.lowerE, hq03, hq06, vsQ,
        Run.resolveVar, List.findIdx?_cons]

/-! ## O2: the kept atoms stay along the flows the cover certifies -/

theorem stayL (l q : ℕ) (hl : l < 2) (c : ℝ) :
    AtomsStayC (cL l) (jointSys (fLQ l) (fRQ q) (Term.const c)) (Formula.and domLQ domRQ) := by
  intro a ha; rw [cL_nil l hl] at ha; simp at ha

theorem stayR_gen (q : ℕ) (hq : q < 2) (fL : Fin 3 → Term (Var 3)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 3)) (hD : ∀ z, Formula.sat D z → Formula.sat domRQ z) :
    AtomsStayC (cR q) (jointSys fL (fRQ q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  rw [cR_eq q hq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact boxle_thrGe_R 0 (vK q) _ _ c hc D D (fun x h => h)
    (fun z hz _ => by
      rw [fRQ0_eval q hq]; have := ((sat_domRQ z).mp (hD z hz)).1; linarith) hinit

/-! ## The invariant's components, as the tool lowers them: the statement's own rows -/

/-- The rows of window `l` (`ACCEL`: two components, `COAST`: one). -/
noncomputable def rH : ℕ → Term (Var 3)
  | 0 => gQ
  | _ => gQC
noncomputable def rT : ℕ → List (Term (Var 3))
  | 0 => gsQ
  | _ => gsQC

theorem FRow_eq (l : ℕ) : FRow l = FM (rH l) (rT l) := by cases l <;> rfl

/-- The pack's component list of window `l`, in the cover's strata order (`ACCEL`: `[1, 0]`;
`COAST`: `[0]`). -/
noncomputable def packList : ℕ → List (Term (Var 3))
  | 0 => [gAt 1, gAt 0]
  | _ => [gAtC 0]

/-- The cover's stretch of window `l` (`ACCEL`: `7/4`; `COAST`: `1`). -/
noncomputable def lamOf : ℕ → ℝ
  | 0 => 7/4
  | _ => 1

theorem lamOf_pos (l : ℕ) : 0 < lamOf l := by cases l <;> simp [lamOf] <;> norm_num

theorem comps_eq0 : hostComps vsQ 3
    (rover3tier_rung12_IRv2.invariants.getD 0 ("", PForm.tt)).2 = [gAt 0, gAt 1] := by
  have hrow : (rover3tier_rung12_IRv2.invariants.getD 0 ("", PForm.tt)).2 = invQPF := rfl
  have hlist : pAtoms invQPF = [(atomsOf invQPF).getD 0 .tt, (atomsOf invQPF).getD 1 .tt] := by
    decide
  rw [hrow, hostComps_atoms vsQ invQPF ?_, hlist]
  · rfl
  · rw [hlist]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hdrops : ("L_v".drop 2).copy = "v" ∧ ("R_v".drop 2).copy = "v" ∧
        ("L_a".drop 2).copy = "a" := by decide
    rcases ha with rfl | rfl <;>
      exact ⟨⟨_, _, _, rfl⟩, by
        simp [atomsOf, invQPF, rover3tier_rung12_IR, Run.invToG, Run.lowerE,
          vsQ, hq05, hq3, hq12, Run.resolveVar, Parse.dr, hdrops, List.findIdx?_cons]⟩

theorem comps_eq1 : hostComps vsQ 3
    (rover3tier_rung12_IRv2.invariants.getD 1 ("", PForm.tt)).2 = [gAtC 0] := by
  have hrow : (rover3tier_rung12_IRv2.invariants.getD 1 ("", PForm.tt)).2 = invQCPF := rfl
  have hlist : pAtoms invQCPF = [(atomsOf invQCPF).getD 0 .tt] := by decide
  rw [hrow, hostComps_atoms vsQ invQCPF ?_, hlist]
  · rfl
  · rw [hlist]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hdrops : ("L_v".drop 2).copy = "v" ∧ ("R_v".drop 2).copy = "v" ∧
        ("L_a".drop 2).copy = "a" := by decide
    subst ha
    exact ⟨⟨_, _, _, rfl⟩, by
      simp [atomsOf, invQCPF, rover3tier_rung12_IR, Run.invToG, Run.lowerE,
        vsQ, hq05, hq3, hq12, Run.resolveVar, Parse.dr, hdrops, List.findIdx?_cons]⟩

theorem comps_fv (l : ℕ) : ∀ c ∈ rH l :: rT l, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  cases l with
  | zero =>
      simp only [rH, rT, gQ, gsQ, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact hgAt _
  | succ l =>
      simp only [rH, rT, gQC, gsQC, List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; exact hgAtC _

/-! ## The verdict packs (the emitted cover's queries) -/

/-- The joint pack of window `l` at right mode `q`, at the cover's λ and strata order. -/
def Verd : ℕ → ℕ → Prop
  | 0, q => modalVerdX rover3tier_rung12_IRv2 rover3tier_rung12_cutsV2X 3 0 [1, 0] (7/4) 0 q
  | l, q => modalVerdX rover3tier_rung12_IRv2 rover3tier_rung12_cutsV2X 3 l [0] 1 l q

theorem domL_univ (l : ℕ) (hl : l < 2) : hostEvolve vsQ 3 Side.L (mLQ l) = domLQ := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 2) : hostEvolve vsQ 3 Side.R (mRQ q) = domRQ := by
  interval_cases q <;> rfl

theorem verd_core (l q : ℕ) (hl : l < 2) (hq : q < 2) (h : Verd l q) :
    VerdXCore (packList l) (fLQ l) (fRQ q) (lamOf l)
      (domCutX (Formula.and domLQ domRQ) (cL l) (cR q)) := by
  rw [← domL_univ l hl, ← domR_univ q hq]
  interval_cases l
  · have h' : VerdXCore (([1, 0] : List ℕ).map (fun i => (hostComps vsQ 3
        (rover3tier_rung12_IRv2.invariants.getD 0 ("", PForm.tt)).2).getD i (Term.const 0)))
        (fLQ 0) (fRQ q) (7/4) (domCutX (Formula.and (hostEvolve vsQ 3 Side.L (mLQ 0))
          (hostEvolve vsQ 3 Side.R (mRQ q))) (cL 0) (cR q)) := h
    rw [comps_eq0] at h'
    simpa [packList, lamOf] using h'
  · have h' : VerdXCore (([0] : List ℕ).map (fun i => (hostComps vsQ 3
        (rover3tier_rung12_IRv2.invariants.getD 1 ("", PForm.tt)).2).getD i (Term.const 0)))
        (fLQ 1) (fRQ q) 1 (domCutX (Formula.and (hostEvolve vsQ 3 Side.L (mLQ 1))
          (hostEvolve vsQ 3 Side.R (mRQ q))) (cL 1) (cR q)) := h
    rw [comps_eq1] at h'
    simpa [packList, lamOf] using h'

/-! ## The anchors of the cover's pairs -/

noncomputable def anc (l q : ℕ) : Formula (Var 3) := FM (rH l) (rT l ++ atomTerms (cL l) (cR q))

theorem cR_nil (q : ℕ) (hq : 2 ≤ q) : cR q = [] := by
  have : mRQ q = dummyQ :=
    List.getD_eq_default _ _ (by simp [rover3tier_rung12_IR]; omega)
  simp only [cR, this]
  rfl

theorem cR_fv (q : ℕ) : ∀ a ∈ cR q, a.2.fv ⊆ range Rv := by
  intro a ha
  by_cases hq : q < 2
  · rw [cR_eq q hq] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    intro x hx; simp [thrGe, Term.fv] at hx; subst hx; simp
  · rw [cR_nil q (by omega)] at ha; simp at ha

theorem anc_fv (l q : ℕ) (hl : l < 2) : (anc l q).fv ⊆ range Lv ∪ range Rv := by
  intro x hx
  by_contra hS
  refine notMem_FM_fv (fun g' hg' hxg => hS ?_) hx
  rcases List.mem_cons.mp hg' with rfl | hg'
  · exact comps_fv l _ List.mem_cons_self hxg
  rcases List.mem_append.mp hg' with hg' | hg'
  · exact comps_fv l _ (List.mem_cons_of_mem _ hg') hxg
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hg'
  rcases hg' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [cL_nil l hl] at ha; simp at ha
  · exact Or.inr (cR_fv q a ha hxg)

theorem anc_box (l q : ℕ) (hl : l < 2) (hq : q < 2) (hv : Verd l q) :
    ∀ σ ω, Formula.sat (anc l q) σ →
      Program.sem (Program.ode (jointSys (fLQ l) (fRQ q) (Term.const (lamOf l)))
        (Formula.and domLQ domRQ)) σ ω → Formula.sat (anc l q) ω := by
  refine couple_box_cutX (rH l) (rT l) (packList l) (cL l) (cR q) (fLQ l) (fRQ q) (lamOf l)
    domLQ domRQ ?_ ?_ (hiffL l hl) (hiffR q hq) (stayL l q hl _)
    (stayR_gen q hq (fLQ l) _ (lamOf_pos l).le _ (fun z hz => hz.2)) (verd_core l q hl hq hv)
  · interval_cases l <;> intro c hc <;>
      simp only [packList, rH, rT, gQ, gsQ, gQC, gsQC, List.mem_cons, List.not_mem_nil,
        or_false] at hc ⊢ <;> tauto
  · interval_cases l <;> intro c hc <;>
      simp only [packList, rH, rT, gQ, gsQ, gQC, gsQC, List.mem_cons, List.not_mem_nil,
        or_false] at hc ⊢ <;> tauto

theorem anc_hand (l q : ℕ) (hl : l < 2) (hq : q < 2) :
    ∀ e ∈ GrG.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have ht : e.tgt < 2 := hltG q e he
  have hg : Formula.sat (hostGuard vsQ 3 Side.R (mRQ e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [GrG_guards q e he] at this
  exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)

theorem anc_iff (l q : ℕ) (hl : l < 2) (hq : q < 2) (x : State (Var 3)) :
    Formula.sat (anc l q) x ↔ Formula.sat (FRow l) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  unfold anc
  rw [FRow_eq, sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

theorem FRow_fv (l : ℕ) : (FRow l).fv ⊆ range Lv ∪ range Rv := by
  rw [FRow_eq]
  intro v hv
  by_contra hn
  exact notMem_FM_fv (fun c hc hvc => hn (comps_fv l c hc hvc)) hv

/-! ## The right's moves: flow in the current mode, switch `ACCEL → COAST` at `v_R = 0.6` -/

/-- A right state of mode `q`: in its guard and the envelope. -/
def PreQ (q : ℕ) (x : State (Var 3)) : Prop :=
  q < 2 ∧ Formula.sat (hostGuard vsQ 3 Side.R (mRQ q)) x ∧ Formula.sat domRQ x

theorem preQ_R (q : ℕ) (x y : State (Var 3)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : PreQ q x) : PreQ q y := by
  obtain ⟨hq, hg, hd⟩ := h
  refine ⟨hq, ?_, ?_⟩
  · refine (Formula.coincidence _ (fun v hv => ?_)).mp hg
    obtain ⟨i, rfl⟩ := hguardRQ q hq hv
    exact hxy i
  · refine (Formula.coincidence domRQ (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomRQ hv
    exact hxy i

/-- The cover's joint nodes: both modes, for both windows; no reposition node. -/
def J (q : ℕ) : Prop := q < 2
def D (_q : ℕ) : Prop := False

theorem runEnd_pre (q : ℕ) (hq : q < 2) (ρ : State (Var 3)) (hd : Formula.sat domRQ ρ)
    (τ : ℝ) (hτ : 0 ≤ τ) : Formula.sat domRQ (runEnd ρ τ) := by
  have h := (run_sol q hq ρ hd τ hτ).hdom τ ⟨hτ, le_rfl⟩
  simpa [modeQ] using h

theorem hmoveQ (E : ℕ → State (Var 3) → Prop) (hE : ∀ q x, J q → PreQ q x → E q x) :
    HMove GrG modeQ J (fun q => q) PreQ E := by
  intro q hJ ρ hpre T hT
  obtain ⟨hq, hg, hd⟩ := hpre
  have hD := (sat_domRQ ρ).mp hd
  have ha : 0 < ρ (Rv 2) := by linarith [hD.1]
  have hgx := (sat_guardRQ q hq ρ).mp hg
  interval_cases q
  · simp only [if_true] at hgx
    by_cases hlo : ρ (Rv 0) + ρ (Rv 2) * T < 3/5
    · refine Or.inl ⟨fun t => runEnd ρ t, run_sol 0 (by norm_num) ρ hd T hT, edgeG 0 0,
        edgeG_mem 0 0 (by norm_num) (by norm_num), ?_, ?_⟩
      · show Formula.sat (hostGuard vsQ 3 Side.R (mRQ 0)) (runEnd ρ T)
        rw [sat_guardRQ 0 (by norm_num), if_pos rfl, runEnd_R0]
        exact ⟨by nlinarith [mul_nonneg ha.le hT], hlo⟩
      · refine hE 0 _ (show (0:ℕ) < 2 by norm_num) ⟨by norm_num, ?_, runEnd_pre 0 (by norm_num) ρ hd T hT⟩
        show Formula.sat (hostGuard vsQ 3 Side.R (mRQ 0)) (runEnd ρ T)
        rw [sat_guardRQ 0 (by norm_num), if_pos rfl, runEnd_R0]
        exact ⟨by nlinarith [mul_nonneg ha.le hT], hlo⟩
    · push_neg at hlo
      set τ := (3/5 - ρ (Rv 0)) / ρ (Rv 2) with hτdef
      have hτ0 : 0 ≤ τ := div_nonneg (by linarith [hgx.2]) ha.le
      have hτT : τ ≤ T := by
        rw [hτdef, div_le_iff₀ ha]; linarith
      have hend : runEnd ρ τ (Rv 0) = 3/5 := by
        rw [runEnd_R0, hτdef, mul_div_cancel₀ _ ha.ne']; ring
      refine Or.inr ⟨τ, hτ0, hτT, fun t => runEnd ρ t, run_sol 0 (by norm_num) ρ hd τ hτ0,
        edgeG 0 1, edgeG_mem 0 1 (by norm_num) (by norm_num), ?_, (by show (1:ℕ) < 2; norm_num),
        (by show (0:ℕ) < 1; norm_num), ⟨by show (1:ℕ) < 2; norm_num, ?_, runEnd_pre 0 (by norm_num) ρ hd τ hτ0⟩⟩
      · show Formula.sat (hostGuard vsQ 3 Side.R (mRQ 1)) (runEnd ρ τ)
        rw [sat_guardRQ 1 (by norm_num), if_neg one_ne_zero, hend]
      · show Formula.sat (hostGuard vsQ 3 Side.R (mRQ 1)) (runEnd ρ τ)
        rw [sat_guardRQ 1 (by norm_num), if_neg one_ne_zero, hend]
  · simp only [one_ne_zero, if_false] at hgx
    have hv : 3/5 ≤ runEnd ρ T (Rv 0) := by
      rw [runEnd_R0]; nlinarith [mul_nonneg ha.le hT]
    refine Or.inl ⟨fun t => runEnd ρ t, run_sol 1 (by norm_num) ρ hd T hT, edgeG 1 1,
      edgeG_mem 1 1 (by norm_num) (by norm_num), ?_, ?_⟩
    · show Formula.sat (hostGuard vsQ 3 Side.R (mRQ 1)) (runEnd ρ T)
      rw [sat_guardRQ 1 (by norm_num), if_neg one_ne_zero]; exact hv
    · refine hE 1 _ (show (1:ℕ) < 2 by norm_num) ⟨by norm_num, ?_, runEnd_pre 1 (by norm_num) ρ hd T hT⟩
      show Formula.sat (hostGuard vsQ 3 Side.R (mRQ 1)) (runEnd ρ T)
      rw [sat_guardRQ 1 (by norm_num), if_neg one_ne_zero]; exact hv

theorem hexitQ : HExit GrG modeQ J D (fun q => 1 - q) PreQ PreQ := fun _ hD => hD.elim

/-! ## The response to one gated window: the cover's derivation, replayed -/

/-- The window's clocked pieces, less one (`ACCEL`: 7 pieces; `COAST`: 4). -/
def kOf : ℕ → ℕ
  | 0 => 6
  | _ => 3

theorem respondR (l : ℕ) (hl : l < 2) (dt : ℝ) (hJv : ∀ q, J q → Verd l q)
    (q : ℕ) (hq : q < 2) {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FRow l) envQ) σ)
    (hg : Formula.sat (hostGuard vsQ 3 Side.R (mRQ q)) σ) :
    GResp GrG q (gwindowSeg (guardQ l) (leftBlock (fLQ l)) domLQ tgQ dt (kOf l + 1))
      (fun _ => Formula.and (Formula.and (FRow l) envQ) Formula.tt) σ := by
  have hJD : ∀ q, J q ∨ D q → q < 2 := by
    intro q h; rcases h with h | h
    · exact h
    · exact h.elim
  refine replay_gresp GrG modeQ fRQ domRQ (fLQ l) domLQ (guardQ l) aQ
    hgRG (hfLQ l hl) hdomLQ hdomRQ (hguardL l hl) (lamOf l) (lamOf_pos l) J D
    (fun q h => hfRQ q (hJD q h)) (fun q => q) (fun q => 1 - q) 2 (fun q h => h)
    (fun q h => GrG_modeAt q (hJD q h)) (fun _ _ => rfl) (fun _ _ => rfl)
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h (hJv q h))
    (fun q h => (h : False).elim)
    (fun q h => anc_hand l q hl (hJD q h))
    PreQ PreQ PreQ preQ_R preQ_R
    (hmoveQ _ (fun _ _ _ h => h)) (fun _ _ => hmoveQ _ (fun _ _ hJ h => ⟨hJ, h⟩))
    hexitQ dt (kOf l) q σ ?_ hσ.2.1 _ ?_
  · intro _
    refine ⟨Or.inl ⟨hq, hq, hg, hσ.2.2⟩, ?_⟩
    exact (anc_iff l q hl hq σ).mpr ⟨hσ.1, by rw [cL_nil l hl]; exact cutSat_nil σ,
      hO1R q hq σ hg⟩
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domLQ ν :=
      windowSeg_end_domL (leftBlock (fLQ l)) domLQ tgQ dt (kOf l + 1) (by omega) hwin
    have hq' : q' < 2 := hpre.1
    have hA' := ((anc_iff l q' hl hq' _).mp hA).1
    have hF : Formula.sat (FRow l) μ := by
      refine (sat_of_agree (FRow_fv l) (fun i => ?_) (fun i => ?_)).mp hA'
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨hF, ?_, hpre.2.2⟩, trivial⟩
    refine (Formula.coincidence domLQ (fun v hv => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomLQ hv
    exact hμL i

/-! ## The mode-consistent region: the right mode's guard -/

/-- **The mode-consistent region** of right mode `q`: its lowered guard (the cut conjunct is
`⊤`). -/
noncomputable def gregionQ (q : ℕ) : Formula (Var 3) :=
  regionG (fun q => hostGuard vsQ 3 Side.R (mRQ q)) (fun _ => Formula.tt) q

theorem hguardRQ_all (q : ℕ) : (hostGuard vsQ 3 Side.R (mRQ q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vsQ _ dummyQ rfl (by simp [rover3tier_rung12_IR, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem gregionQ_fv (q : ℕ) : (gregionQ q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardRQ_all q) (by simp [Formula.fv])

theorem hmvregQ : ∀ q, mvQ ∉ (gregionQ q).fv := fun q h => aux_notin_range_Rv 0 (gregionQ_fv q h)

theorem hulRG : ulQ ∉ (rightAutomatonBody GrG mvQ).bv :=
  notMem_bv_rightAutomatonBody_G GrG mvQ ulQ (by decide) (aux_notin_range_Rv 2) hgRG hRvG

theorem hulBkG : ulQ ∉ (mvRegion mvQ gregionQ GrG.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mvQ gregionQ GrG.modes.length (fun q _ => gregionQ_fv q) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem AQ_window' (dt : ℝ) (t : ℕ) (ht : t < 2) :
    (AQ dt).window t = windowSeg (leftBlock (fLQ t)) domLQ tgQ dt (kOf t + 1) := by
  interval_cases t <;> rfl

theorem hstepMG (dt : ℝ) (hJv : ∀ l < 2, ∀ q, J q → Verd l q) :
    ∀ t < (AQ dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envQ)
      (mvRegion mvQ gregionQ GrG.modes.length)) σ →
    Formula.sat ((AQ dt).guard t) σ →
    Formula.sat (faModal (Equiv.refl (Var 3)) ((AQ dt).window t)
      (Program.star (rightAutomatonBody GrG mvQ))
      (Formula.and (Formula.and (FRow t) envQ) (mvRegion mvQ gregionQ GrG.modes.length))) σ := by
  intro t ht σ hσ hgL
  rw [AQ_numModes] at ht
  rw [AQ_guard dt t ht] at hgL
  rw [AQ_window' dt t ht]
  refine faModal_ungate (φ := guardQ t) hgL ?_
  have hframe : FramesMv (gwindowSeg (guardQ t) (leftBlock (fLQ t)) domLQ tgQ dt (kOf t + 1))
      mvQ := by
    refine framesMv_gwindow (guardQ t) (fLQ t) domLQ tgQ dt (kOf t + 1) mvQ (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLQ t) _ h
    exact aux_ne_Lv 0 i hi
  refine hstepMode_GR GrG mvQ (FRow t) envQ gregionQ _ (aux_notin_FRow 0 t) hmvenvQ hmvregQ
    hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG hframe ?_ σ hσ
  refine HMode_regionG_ofF GrG mvQ _ (fun _ => Formula.tt) GrG_guards (fun _ _ _ => trivial)
    (FRow t) envQ _ ?_ ?_
  · intro q _ σ ν hrun
    exact frames_right (vars_gwindowSegL_sub (guardQ t) (fLQ t) domLQ aQ dt (kOf t + 1)
      (hguardL t ht) (hfLQ t ht) hdomLQ) (hguardRQ_all q) hrun
  · intro q hq σ _ hσ hg
    rw [GrG_len] at hq
    have h := respondR t ht dt (hJv t ht) q hq hσ hg
    exact gresp_mono (post := fun _ => Formula.and (Formula.and (FRow t) envQ) Formula.tt)
      (post' := fun _ => Formula.and (FRow t) envQ) (fun _ _ h => h.1) h

/-- **`rover3tier_rung12`, Theorem 3 at the DECLARED mode-dependent invariant, over the
GUARDED right automaton, by replaying the emitted cover.** `u_L`-keyed rows (`ACCEL`:
`v[l] ≤ v[r] + 0.5 ∧ 3v[l] + a[l] ≤ 3v[r] + 1.2`; `COAST`: `3v[l] + a[l] ≤ 3v[r] + 1.2`) over
the left automaton of the file (`ACCEL ↔ COAST`, guard-tested, windows of 7 and 4 clocked
pieces), against the file's right automaton with every edge testing the entered mode's guard
(`GrG_guards`). Loop invariant: the rows, the envelope, and the right in the guard of its
current mode (`mvRegionR` at `gregionQ`). Response (`InstancesV2/BenchCovers/rover3tier_rung12.lean`):
the right keeps time with the window at the cover's stretch (`ACCEL` window: λ = 7/4;
`COAST` window: λ = 1) in its current mode, both modes joint nodes of both windows, switching
`ACCEL → COAST` where `v_R` reaches `0.6`; every stretch preserved by its joint pack
`Verd l q` (the emitted cover's queries at the declared row of `l`, strata `[1, 0]` for
`ACCEL`, `[0]` for `COAST`), every switch legal; the explicit runs give only the existence of
the right's runs and the switch instants. For every window length `dt`. -/
theorem rover3tier_rung12_modeKeyed_guarded (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h10 : Verd 1 0) (h11 : Verd 1 1) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AQ dt) ulQ)
      (rightAutomatonBody GrG mvQ)
      (psiK ulQ ϕRow (AQ dt).numModes domLQ domRQ
        (mvRegionR mvQ gregionQ GrG.modes.length))) := by
  have hJv : ∀ l < 2, ∀ q, J q → Verd l q := by
    intro l hl q hq
    change q < 2 at hq
    match l, q, hl, hq with
    | 0, 0, _, _ => exact h00
    | 0, 1, _, _ => exact h01
    | 1, 0, _, _ => exact h10
    | 1, 1, _, _ => exact h11
  refine theorem3_modeKeyed (AQ dt) ulQ GrG mvQ FRow ϕRow domLQ domRQ
    (mvRegion mvQ gregionQ GrG.modes.length) (mvRegionR mvQ gregionQ GrG.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_G (AQ dt) GrG 0 1 2 (by decide) (by decide) (hwinQ dt) (hgrdQ dt)
      (hnextQ dt) hgRG hRvG
  · exact hstep_modeKeyed_g (AQ dt) ulQ (rightAutomatonBody GrG mvQ) FRow envQ
      (mvRegion mvQ gregionQ GrG.modes.length) (aux_notin_FRow 2) hulenvQ hulBkG (hulGQ dt)
      (hframesUlQ dt) hulRG (hnextQ dt) (hstepMG dt hJv) (handoffQ dt)
  · exact hddF_modeKeyed_G (AQ dt) GrG 0 1 2 (by decide) (by decide) ϕRow domLQ domRQ
      (mvRegionR mvQ gregionQ GrG.modes.length) (hwinQ dt) (hgrdQ dt) (hnextQ dt) hgRG hRvG
      (fun m _ => by
        cases m with
        | zero => exact canonInvM_varsL gQ gsQ (fun g' hg' => by
            simp only [gQ, gsQ, List.mem_cons, List.not_mem_nil, or_false] at hg'
            rcases hg' with rfl | rfl <;> exact hgAt _)
        | succ m => exact canonInvM_varsL gQC gsQC (fun g' hg' => by
            simp only [gQC, gsQC, List.mem_cons, List.not_mem_nil, or_false] at hg'
            rcases hg' with rfl <;> exact hgAtC _))
      (fun m _ => by
        cases m with
        | zero => exact canonInvM_varsR gQ gsQ
        | succ m => exact canonInvM_varsR gQC gsQC)
      hdomLQ hdomRQ rfl
      (fun v hv => mvRegion_fv_sub mvQ gregionQ GrG.modes.length (fun q _ => gregionQ_fv q) hv)

end Rover3tierRung12Guarded
end RelCertifier
