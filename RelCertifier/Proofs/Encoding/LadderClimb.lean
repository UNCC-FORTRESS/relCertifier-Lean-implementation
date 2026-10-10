/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The guarded climb of the rover ladders' reference chain

Every rover-ladder benchmark's reference (right) automaton is the one-way chain
`STEEP → MODER → FLAT` with `v' = 3 (c_q − v)` (`c = 0.3, 0.5, 0.65`), an odometer
`s' = v · κ` with `κ` a positive attitude factor, and band guards on `s` (`[0, 0.6)`,
`[0.6, 1.4)`, `[1.4, ∞)`) that also cap `v` by the band's set point. This file abstracts the
climb that answers every left window of these benchmarks over the GUARDED chain: after the left
window the right runs its band to the next band's floor and switches there (legal: the
odometer is exactly at the floor and `v` is below the band's cap), then holds `FLAT` until
`v_R ≥ V` (any target below `0.65`, or already reached) and `s_R ≥ S`, and takes the
self-loop.

`LadderRun` bundles what a benchmark supplies: the band runs (explicit, of every duration, from
every envelope state), the exponential law of `v`, a lower bound on the odometer's growth, and
the legality of the three switches the climb takes (`STEEP → MODER` at `s = 0.6`,
`MODER → FLAT` at `s = 1.4`, `FLAT → FLAT` anywhere in `FLAT`'s guard).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.GuardedClimb

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-- The bands' set points (`STEEP` 0.3, `MODER` 0.5, `FLAT` 0.65). -/
noncomputable def ladC (q : ℕ) : ℝ := if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20

theorem ladC_bounds (q : ℕ) : 3/10 ≤ ladC q ∧ ladC q ≤ 13/20 := by
  unfold ladC; split_ifs <;> norm_num

/-- **What a ladder benchmark supplies for the climb.** `v = Rv 0`, `s = Rv 1`. -/
structure LadderRun (G : SearchGraph (Var (n+2))) (dom : Formula (Var (n+2))) where
  m : ℕ → RMode (Var (n+2))
  run : ℕ → State (Var (n+2)) → ℝ → State (Var (n+2))
  κ : ℝ
  hκ : 0 < κ
  modeAt : ∀ q < 3, G.modeAt q = some (m q)
  sem : ∀ q < 3, ∀ ρ, Formula.sat dom ρ → ∀ τ, 0 ≤ τ →
    Program.sem (Program.ode (m q).sys (m q).dom) ρ (run q ρ τ)
  v_eq : ∀ q < 3, ∀ ρ τ, run q ρ τ (Rv 0) = ladC q + (ρ (Rv 0) - ladC q) * Real.exp (-(3 * τ))
  s_low : ∀ q < 3, ∀ ρ, Formula.sat dom ρ → ∀ τ, 0 ≤ τ →
    ρ (Rv 1) + κ * (ladC q * τ - ladC q / 3) ≤ run q ρ τ (Rv 1) ∧ ρ (Rv 1) ≤ run q ρ τ (Rv 1)
  s_cont : ∀ q < 3, ∀ ρ, Continuous (fun τ => run q ρ τ (Rv 1))
  left : ∀ q ρ τ (i : Fin (n+2)), run q ρ τ (Lv i) = ρ (Lv i)
  zero : ∀ q ρ, run q ρ 0 (Rv 1) = ρ (Rv 1)
  v_nonneg : ∀ ρ, Formula.sat dom ρ → 0 ≤ ρ (Rv 0)
  dom_m : ∀ q < 3, (m q).dom = dom
  e01 : REdge (Var (n+2))
  e12 : REdge (Var (n+2))
  e22 : REdge (Var (n+2))
  e01_mem : e01 ∈ G.edgesFrom 0
  e12_mem : e12 ∈ G.edgesFrom 1
  e22_mem : e22 ∈ G.edgesFrom 2
  e01_tgt : e01.tgt = 1
  e12_tgt : e12.tgt = 2
  e22_tgt : e22.tgt = 2
  leg01 : ∀ x, x (Rv 1) = 3/5 → x (Rv 0) ≤ 3/10 → SwitchLegal e01 x
  leg12 : ∀ x, x (Rv 1) = 7/5 → x (Rv 0) ≤ 1/2 → SwitchLegal e12 x
  leg22 : ∀ x, 7/5 ≤ x (Rv 1) → x (Rv 0) ≤ 13/20 → SwitchLegal e22 x

namespace LadderRun

variable {G : SearchGraph (Var (n+2))} {dom : Formula (Var (n+2))} (LR : LadderRun G dom)
include LR

theorem end_dom (q : ℕ) (hq : q < 3) (ρ : State (Var (n+2))) (hρ : Formula.sat dom ρ) (τ : ℝ)
    (hτ : 0 ≤ τ) : Formula.sat dom (LR.run q ρ τ) := by
  have h := sem_ode_ends_in_domain (LR.sem q hq ρ hρ τ hτ)
  rwa [LR.dom_m q hq] at h

/-- Along a band run that starts at or below the band's set point, `v` only grows and stays at
or below the set point. -/
theorem v_mono (q : ℕ) (hq : q < 3) (ρ : State (Var (n+2))) (hv : ρ (Rv 0) ≤ ladC q) {t : ℝ}
    (ht : 0 ≤ t) : ρ (Rv 0) ≤ LR.run q ρ t (Rv 0) ∧ LR.run q ρ t (Rv 0) ≤ ladC q := by
  have hb := exp_approach_between 3 (ladC q) (ρ (Rv 0)) t (by norm_num) ht
  rw [LR.v_eq q hq]
  rw [min_eq_left hv, max_eq_right hv] at hb
  exact hb

/-- **Reaching an odometer level** in band `q` (from `s₀ ≤ L`). -/
theorem reach (q : ℕ) (hq : q < 3) (ρ : State (Var (n+2))) (hρ : Formula.sat dom ρ) (L : ℝ)
    (hL : ρ (Rv 1) ≤ L) : ∃ τ, 0 ≤ τ ∧ LR.run q ρ τ (Rv 1) = L := by
  have hc := ladC_bounds q
  have hcpos : 0 < ladC q := by linarith
  have hκ := LR.hκ
  set T : ℝ := ((L - ρ (Rv 1)) / LR.κ + ladC q / 3) / ladC q with hT
  have hT0 : 0 ≤ T := by
    apply div_nonneg _ hcpos.le
    have : 0 ≤ (L - ρ (Rv 1)) / LR.κ := div_nonneg (by linarith) hκ.le
    linarith
  have hcont : ContinuousOn (fun t => LR.run q ρ t (Rv 1)) (Icc 0 T) :=
    (LR.s_cont q hq ρ).continuousOn
  have hTv : L ≤ LR.run q ρ T (Rv 1) := by
    have h1 := (LR.s_low q hq ρ hρ T hT0).1
    have hcT : ladC q * T - ladC q / 3 = (L - ρ (Rv 1)) / LR.κ := by
      rw [hT]; field_simp; ring
    rw [hcT] at h1
    have : LR.κ * ((L - ρ (Rv 1)) / LR.κ) = L - ρ (Rv 1) := by field_simp
    linarith
  obtain ⟨τ, hτ, hτv⟩ := intermediate_value_Icc hT0 hcont
    ⟨by rw [LR.zero q ρ]; exact hL, hTv⟩
  exact ⟨τ, hτ.1, hτv⟩

/-- **The `FLAT` hold**: from a `FLAT` state in its guard (`s ≥ 1.4`, `v ≤ 0.65`), run until
`v_R ≥ V` (`V` strictly below the set point, or already reached) and `s_R ≥ S`, then the
self-loop. -/
theorem climbFlat {post : ℕ → Formula (Var (n+2))} (ρ : State (Var (n+2))) (hdom : Formula.sat dom ρ)
    (hg : 7/5 ≤ ρ (Rv 1) ∧ ρ (Rv 0) ≤ 13/20) (V S : ℝ) (hV : V < 13/20 ∨ V ≤ ρ (Rv 0))
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat dom μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ρ (Rv 0) ≤ μ (Rv 0) → V ≤ μ (Rv 0) →
      S ≤ μ (Rv 1) → Formula.sat (post 2) μ) :
    RResp G 2 post ρ := by
  have hc2 : ladC 2 = 13/20 := by norm_num [ladC]
  have hv0 := LR.v_nonneg ρ hdom
  have hκ := LR.hκ
  set δ : ℝ := if V < 13/20 then 13/20 - V else 1 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; split_ifs with h
    · linarith
    · norm_num
  set τ : ℝ := (13/20) / (3 * δ) + max 0 ((S - ρ (Rv 1)) / LR.κ * (20/13) + 1) with hτ
  have hτ1 : 0 ≤ (13/20) / (3 * δ) := by positivity
  have hτ2 : 0 ≤ max 0 ((S - ρ (Rv 1)) / LR.κ * (20/13) + 1) := le_max_left _ _
  have hτ0 : 0 ≤ τ := by linarith
  have hrun := LR.sem 2 (by norm_num) ρ hdom τ hτ0
  set μ := LR.run 2 ρ τ with hμ
  have hmono := LR.v_mono 2 (by norm_num) ρ (by rw [hc2]; exact hg.2) hτ0
  rw [hc2] at hmono
  have hslow := LR.s_low 2 (by norm_num) ρ hdom τ hτ0
  rw [hc2] at hslow
  have hμdom : Formula.sat dom μ := LR.end_dom 2 (by norm_num) ρ hdom τ hτ0
  have hμL : ∀ i, μ (Lv i) = ρ (Lv i) := LR.left 2 ρ τ
  have hvV : V ≤ μ (Rv 0) := by
    rcases hV with hV | hV
    · have hδV : δ = 13/20 - V := by rw [hδ, if_pos hV]
      have he := Real.add_one_le_exp (3 * τ)
      have hinv : Real.exp (-(3 * τ)) * Real.exp (3 * τ) = 1 := by
        rw [← Real.exp_add]; simp
      have h3τ : (13/20) / δ ≤ 3 * τ := by
        have : 3 * ((13/20) / (3 * δ)) = (13/20) / δ := by field_simp
        linarith
      have h1 : (13/20) < δ * Real.exp (3 * τ) := by
        have : (13/20) / δ * δ = 13/20 := by field_simp
        nlinarith
      have hle : Real.exp (-(3 * τ)) * (13/20) < δ := by
        nlinarith [Real.exp_pos (-(3 * τ))]
      rw [hμ, LR.v_eq 2 (by norm_num), hc2]
      nlinarith [Real.exp_pos (-(3 * τ))]
    · exact le_trans hV hmono.1
  have hsS : S ≤ μ (Rv 1) := by
    have hm : (S - ρ (Rv 1)) / LR.κ * (20/13) + 1 ≤ max 0 ((S - ρ (Rv 1)) / LR.κ * (20/13) + 1) :=
      le_max_right _ _
    have hτge : (S - ρ (Rv 1)) / LR.κ * (20/13) + 1 ≤ τ := by linarith
    have h13 : 13/20 * τ - 13/20/3 ≥ (S - ρ (Rv 1)) / LR.κ := by nlinarith
    have hkk : LR.κ * ((S - ρ (Rv 1)) / LR.κ) = S - ρ (Rv 1) := by field_simp
    nlinarith [hslow.1]
  have hs14 : 7/5 ≤ μ (Rv 1) := le_trans hg.1 hslow.2
  have hleg := LR.leg22 μ hs14 hmono.2
  have hstep := rresp_step (post := post) (LR.modeAt 2 (by norm_num)) LR.e22_mem hrun hleg
  rw [LR.e22_tgt] at hstep
  exact hstep (rresp_stop (hpost μ hμL hμdom hs14 hmono.2 hmono.1 hvV hsS))

/-- **The climb from `MODER`** (`0.6 ≤ s < 1.4`, `v ≤ 0.5`). -/
theorem climbModer {post : ℕ → Formula (Var (n+2))} (ρ : State (Var (n+2))) (hdom : Formula.sat dom ρ)
    (hg : 3/5 ≤ ρ (Rv 1) ∧ ρ (Rv 1) < 7/5 ∧ ρ (Rv 0) ≤ 1/2) (V S : ℝ)
    (hV : V < 13/20 ∨ V ≤ ρ (Rv 0))
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat dom μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ρ (Rv 0) ≤ μ (Rv 0) → V ≤ μ (Rv 0) →
      S ≤ μ (Rv 1) → Formula.sat (post 2) μ) :
    RResp G 1 post ρ := by
  have hc1 : ladC 1 = 1/2 := by norm_num [ladC]
  obtain ⟨τ, hτ, hτs⟩ := LR.reach 1 (by norm_num) ρ hdom (7/5) (le_of_lt hg.2.1)
  have hrun := LR.sem 1 (by norm_num) ρ hdom τ hτ
  set κ := LR.run 1 ρ τ with hκdef
  have hmono := LR.v_mono 1 (by norm_num) ρ (by rw [hc1]; exact hg.2.2) hτ
  rw [hc1] at hmono
  have hκdom : Formula.sat dom κ := LR.end_dom 1 (by norm_num) ρ hdom τ hτ
  have hleg := LR.leg12 κ hτs (by linarith [hmono.2])
  have hstep := rresp_step (post := post) (LR.modeAt 1 (by norm_num)) LR.e12_mem hrun hleg
  rw [LR.e12_tgt] at hstep
  refine hstep (LR.climbFlat κ hκdom ⟨le_of_eq hτs.symm, by linarith [hmono.2]⟩ V S
    (hV.imp_right (fun h => le_trans h hmono.1)) ?_)
  intro μ hμL hμd h1 h2 h3 h4 h5
  exact hpost μ (fun i => (hμL i).trans (LR.left 1 ρ τ i)) hμd h1 h2 (le_trans hmono.1 h3) h4 h5

/-- **The climb from `STEEP`** (`s < 0.6`, `v ≤ 0.3`). -/
theorem climbSteep {post : ℕ → Formula (Var (n+2))} (ρ : State (Var (n+2))) (hdom : Formula.sat dom ρ)
    (hg : ρ (Rv 1) < 3/5 ∧ ρ (Rv 0) ≤ 3/10) (V S : ℝ)
    (hV : V < 13/20 ∨ V ≤ ρ (Rv 0))
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat dom μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ρ (Rv 0) ≤ μ (Rv 0) → V ≤ μ (Rv 0) →
      S ≤ μ (Rv 1) → Formula.sat (post 2) μ) :
    RResp G 0 post ρ := by
  have hc0 : ladC 0 = 3/10 := by norm_num [ladC]
  obtain ⟨τ, hτ, hτs⟩ := LR.reach 0 (by norm_num) ρ hdom (3/5) (le_of_lt hg.1)
  have hrun := LR.sem 0 (by norm_num) ρ hdom τ hτ
  set κ := LR.run 0 ρ τ with hκdef
  have hmono := LR.v_mono 0 (by norm_num) ρ (by rw [hc0]; exact hg.2) hτ
  rw [hc0] at hmono
  have hκdom : Formula.sat dom κ := LR.end_dom 0 (by norm_num) ρ hdom τ hτ
  have hleg := LR.leg01 κ hτs hmono.2
  have hstep := rresp_step (post := post) (LR.modeAt 0 (by norm_num)) LR.e01_mem hrun hleg
  rw [LR.e01_tgt] at hstep
  refine hstep (LR.climbModer κ hκdom ⟨le_of_eq hτs.symm, by rw [hτs]; norm_num,
    by linarith [hmono.2]⟩ V S (hV.imp_right (fun h => le_trans h hmono.1)) ?_)
  intro μ hμL hμd h1 h2 h3 h4 h5
  exact hpost μ (fun i => (hμL i).trans (LR.left 0 ρ τ i)) hμd h1 h2 (le_trans hmono.1 h3) h4 h5

/-- **The climb from any band** `q < 3`, in its guard (`STEEP`: `s < 0.6`, `v ≤ 0.3`; `MODER`:
`0.6 ≤ s < 1.4`, `v ≤ 0.5`; `FLAT`: `s ≥ 1.4`, `v ≤ 0.65`). -/
theorem climb {post : ℕ → Formula (Var (n+2))} (q : ℕ) (hq : q < 3) (ρ : State (Var (n+2)))
    (hdom : Formula.sat dom ρ)
    (hg : (q = 0 → ρ (Rv 1) < 3/5 ∧ ρ (Rv 0) ≤ 3/10) ∧
      (q = 1 → 3/5 ≤ ρ (Rv 1) ∧ ρ (Rv 1) < 7/5 ∧ ρ (Rv 0) ≤ 1/2) ∧
      (q = 2 → 7/5 ≤ ρ (Rv 1) ∧ ρ (Rv 0) ≤ 13/20))
    (V S : ℝ) (hV : V < 13/20 ∨ V ≤ ρ (Rv 0))
    (hpost : ∀ μ, (∀ i, μ (Lv i) = ρ (Lv i)) → Formula.sat dom μ →
      7/5 ≤ μ (Rv 1) → μ (Rv 0) ≤ 13/20 → ρ (Rv 0) ≤ μ (Rv 0) → V ≤ μ (Rv 0) →
      S ≤ μ (Rv 1) → Formula.sat (post 2) μ) :
    RResp G q post ρ := by
  interval_cases q
  · exact LR.climbSteep ρ hdom (hg.1 rfl) V S hV hpost
  · exact LR.climbModer ρ hdom (hg.2.1 rfl) V S hV hpost
  · exact LR.climbFlat ρ hdom (hg.2.2 rfl) V S hV hpost

end LadderRun

/-! ## The decoupled-linear ladder: explicit runs

The reference of most ladder benchmarks moves every coordinate other than the odometer along
its own linear law `x_i' = a_i (b_i − x_i)` (`v`: `a = 3`, `b = c_q`; attitude/heave
coordinates: `−x` or `0`), and the odometer integrates `v` (`s' = v`). Its runs are explicit. -/

/-- The explicit coordinates of band `q`'s run from `ρ`. -/
noncomputable def phiLin (a b : Fin (n+2) → ℝ) (q : ℕ) (ρ : State (Var (n+2))) :
    Fin (n+2) → ℝ → ℝ := fun i t =>
  if i = 0 then ladC q + (ρ (Rv 0) - ladC q) * Real.exp (-(3 * t))
  else if i = 1 then
    ρ (Rv 1) + ladC q * t + (ρ (Rv 0) - ladC q) * (1 - Real.exp (-(3 * t))) / 3
  else b i + (ρ (Rv i) - b i) * Real.exp (-(a i * t))

theorem phiLin_s_low (a b : Fin (n+2) → ℝ) (q : ℕ) (ρ : State (Var (n+2))) (hv0 : 0 ≤ ρ (Rv 0))
    {t : ℝ} (ht : 0 ≤ t) :
    ρ (Rv 1) + 1 * (ladC q * t - ladC q / 3) ≤ phiLin a b q ρ 1 t ∧
      ρ (Rv 1) ≤ phiLin a b q ρ 1 t := by
  have hc := ladC_bounds q
  simp only [phiLin, one_ne_zero, if_false, if_true]
  have he0 : 0 < Real.exp (-(3 * t)) := Real.exp_pos _
  have he1 : Real.exp (-(3 * t)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have he2 : 1 - 3 * t ≤ Real.exp (-(3 * t)) := by
    have := Real.add_one_le_exp (-(3 * t)); linarith
  constructor
  · nlinarith
  · rcases le_total (ρ (Rv 0)) (ladC q) with h | h
    · nlinarith
    · nlinarith

/-- **The decoupled-linear ladder run.** From the fields' laws, the band modes, the guard
facts of the three switches, and the closure of the right domain under the explicit runs. -/
noncomputable def LadderRun.ofLinear (G : SearchGraph (Var (n+2))) (dom : Formula (Var (n+2)))
    (m : ℕ → RMode (Var (n+2))) (fR : ℕ → Fin (n+2) → Term (Var (n+2))) (a b : Fin (n+2) → ℝ)
    (hmodeAt : ∀ q < 3, G.modeAt q = some (m q))
    (hsys : ∀ q < 3, (m q).sys = rightBlock (fR q) (Term.const 1))
    (hdomm : ∀ q < 3, (m q).dom = dom)
    (hfv : ∀ q < 3, ∀ x, Term.eval (fR q 0) x = 3 * (ladC q - x (Rv 0)))
    (hfs : ∀ q < 3, ∀ x, Term.eval (fR q 1) x = x (Rv 0))
    (hfo : ∀ q < 3, ∀ (i : Fin (n+2)), i ≠ 0 → i ≠ 1 → ∀ x,
      Term.eval (fR q i) x = a i * (b i - x (Rv i)))
    (hdomrun : ∀ q < 3, ∀ ρ, Formula.sat dom ρ → ∀ t, 0 ≤ t →
      Formula.sat dom (trajR ρ (phiLin a b q ρ) t))
    (hv0 : ∀ ρ, Formula.sat dom ρ → 0 ≤ ρ (Rv 0))
    (e01 e12 e22 : REdge (Var (n+2)))
    (e01_mem : e01 ∈ G.edgesFrom 0) (e12_mem : e12 ∈ G.edgesFrom 1)
    (e22_mem : e22 ∈ G.edgesFrom 2)
    (e01_tgt : e01.tgt = 1) (e12_tgt : e12.tgt = 2) (e22_tgt : e22.tgt = 2)
    (leg01 : ∀ x, x (Rv 1) = 3/5 → x (Rv 0) ≤ 3/10 → SwitchLegal e01 x)
    (leg12 : ∀ x, x (Rv 1) = 7/5 → x (Rv 0) ≤ 1/2 → SwitchLegal e12 x)
    (leg22 : ∀ x, 7/5 ≤ x (Rv 1) → x (Rv 0) ≤ 13/20 → SwitchLegal e22 x) :
    LadderRun G dom where
  m := m
  run := fun q ρ t => trajR ρ (phiLin a b q ρ) t
  κ := 1
  hκ := one_pos
  modeAt := hmodeAt
  sem := by
    intro q hq ρ hρ τ hτ
    rw [hsys q hq, hdomm q hq]
    refine explicit_run ρ (phiLin a b q ρ) τ hτ ?_ ?_ ?_
    · intro i
      by_cases h0 : i = 0
      · subst h0; simp [phiLin]
      by_cases h1 : i = 1
      · subst h1; simp [phiLin]
      · simp [phiLin, h0, h1]
    · intro i t _ _
      by_cases h0 : i = 0
      · subst h0
        rw [hfv q hq, trajR_R]
        have h := hasDerivAt_expApproach 3 (ladC q) (ρ (Rv 0)) t
        convert h using 1
        · funext u; simp [phiLin]
        · simp [phiLin]
      by_cases h1 : i = 1
      · subst h1
        rw [hfs q hq, trajR_R]
        have h := hasDerivAt_expIntegral 3 (ladC q) (ρ (Rv 0)) (ρ (Rv 1)) t (by norm_num)
        convert h using 1
        · funext u; simp [phiLin]
        · simp [phiLin]
      · rw [hfo q hq i h0 h1, trajR_R]
        have h := hasDerivAt_expApproach (a i) (b i) (ρ (Rv i)) t
        convert h using 1
        · funext u; simp [phiLin, h0, h1]
        · simp [phiLin, h0, h1]
    · intro t ht _
      exact hdomrun q hq ρ hρ t ht
  v_eq := by
    intro q _ ρ τ
    simp [trajR_R, phiLin]
  s_low := by
    intro q _ ρ hρ τ hτ
    rw [trajR_R]
    exact phiLin_s_low a b q ρ (hv0 ρ hρ) hτ
  s_cont := by
    intro q _ ρ
    simp only [trajR_R, phiLin, one_ne_zero, if_false, if_true]
    fun_prop
  left := fun q ρ τ i => trajR_L _ _ _ _
  zero := by
    intro q ρ
    simp [trajR_R, phiLin]
  v_nonneg := hv0
  dom_m := hdomm
  e01 := e01
  e12 := e12
  e22 := e22
  e01_mem := e01_mem
  e12_mem := e12_mem
  e22_mem := e22_mem
  e01_tgt := e01_tgt
  e12_tgt := e12_tgt
  e22_tgt := e22_tgt
  leg01 := leg01
  leg12 := leg12
  leg22 := leg22

theorem LadderRun.ofLinear_run (G : SearchGraph (Var (n+2))) (dom : Formula (Var (n+2)))
    (m : ℕ → RMode (Var (n+2))) (fR : ℕ → Fin (n+2) → Term (Var (n+2))) (a b : Fin (n+2) → ℝ)
    (h1 h2 h3 h4 h5 h6 h7 h8) (e01 e12 e22 : REdge (Var (n+2))) (h9 h10 h11 h12 h13 h14 h15 h16
    h17) (q : ℕ) (ρ : State (Var (n+2))) (t : ℝ) :
    (LadderRun.ofLinear G dom m fR a b h1 h2 h3 h4 h5 h6 h7 h8 e01 e12 e22 h9 h10 h11 h12 h13 h14
      h15 h16 h17).run q ρ t = trajR ρ (phiLin a b q ρ) t := rfl

theorem phiLin_v (a b : Fin (n+2) → ℝ) (q : ℕ) (ρ : State (Var (n+2))) (t : ℝ) :
    phiLin a b q ρ 0 t = ladC q + (ρ (Rv 0) - ladC q) * Real.exp (-(3 * t)) := by
  simp [phiLin]

theorem phiLin_other (a b : Fin (n+2) → ℝ) (q : ℕ) (ρ : State (Var (n+2))) (i : Fin (n+2))
    (h0 : i ≠ 0) (h1 : i ≠ 1) (t : ℝ) :
    phiLin a b q ρ i t = b i + (ρ (Rv i) - b i) * Real.exp (-(a i * t)) := by
  simp [phiLin, h0, h1]

/-- `v` along a band run stays between its start and the band's set point. -/
theorem phiLin_v_between (a b : Fin (n+2) → ℝ) (q : ℕ) (ρ : State (Var (n+2))) {t : ℝ}
    (ht : 0 ≤ t) :
    min (ρ (Rv 0)) (ladC q) ≤ phiLin a b q ρ 0 t ∧ phiLin a b q ρ 0 t ≤ max (ρ (Rv 0)) (ladC q) := by
  rw [phiLin_v]; exact exp_approach_between 3 _ _ t (by norm_num) ht

/-- Every other coordinate stays between its start and its target (`a_i ≥ 0`). -/
theorem phiLin_other_between (a b : Fin (n+2) → ℝ) (q : ℕ) (ρ : State (Var (n+2))) (i : Fin (n+2))
    (h0 : i ≠ 0) (h1 : i ≠ 1) (ha : 0 ≤ a i) {t : ℝ} (ht : 0 ≤ t) :
    min (ρ (Rv i)) (b i) ≤ phiLin a b q ρ i t ∧ phiLin a b q ρ i t ≤ max (ρ (Rv i)) (b i) := by
  rw [phiLin_other a b q ρ i h0 h1]; exact exp_approach_between _ _ _ t ha ht

end RelCertifier
