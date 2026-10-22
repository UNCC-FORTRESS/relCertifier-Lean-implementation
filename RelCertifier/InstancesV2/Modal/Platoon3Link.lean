/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The three-follower CACC string: one damped link, shared by `platoon3_linkloss` and
# `platoon3_profiles`

Every link of both sides is the same second-order loop `x' = y`,
`y' = −(1/8)(x − c) − (3/4) y` (gap `x`, closing rate `y`, set point `c`; roots
`ρ = 1/4, 1/2`). The operating-range guards (`docs/SUITE-REDESIGN.md` §20) contribute four
kept atoms per link: the rated closing rate `−10 ≤ y ≤ 10` and the projected gap
`P ≤ x + 2y ≤ U` (the slow decoupling form `y + (x − c)/2`, scaled); the linear-form chain
contributes four more. This leaf collects, once for both instances:

* the per-link atom families (`guardT`, `linT`) and their O2 lemmas along the joint flows,
  both sides (`stayR_link`, `stayL_link`, `stayR_derGe`, `stayL_derGe`);
* (in `WellFormed/Platoon3Link`, imported here) the link shape (`LinkField`, `pgGe`), the
  explicit link solution and its box (`gS`, `rS`, `link_bounds`), from which the existence
  residual of every joint segment is discharged, and the guard barrier along the reference's
  OWN flow (`gap_floor_Ronly`).

New leaf.
-/
import RelCertifier.Proofs.Encoding.RightOnlyStay
import RelCertifier.InstancesV2.WellFormed.Platoon3Link
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch

set_option linter.unusedSimpArgs false

namespace RelCertifier
open DL DLCalTiming DLRel Set

/-- **`gresp_final` with the left run's end state in hand**: the nonblocking obligation may use
the state the response flow starts from (the end of the left window), e.g. to carry a guard
barrier along the flow. -/
theorem gresp_final_run {n : ℕ} {G : SearchGraph (Var n)} {qs : ℕ} {ms : RMode (Var n)}
    (hm : G.modeAt qs = some ms)
    {P : Program (Var n)} {Post' : Formula (Var n)} {post : ℕ → Formula (Var n)}
    {σ : State (Var n)}
    (hfa : Formula.sat (faModal (Equiv.refl (Var n)) P
      (bigSeq [Program.ode ms.sys ms.dom]) Post') σ)
    (hnb : ∀ ν, Program.sem P σ ν → ∀ μ, Program.sem (Program.ode ms.sys ms.dom) ν μ →
      Formula.sat Post' μ → ∃ e ∈ G.edgesFrom qs, SwitchLegal e μ ∧ Formula.sat (post e.tgt) μ) :
    GResp G qs P post σ := by
  intro ν hν
  rw [faModal_sat] at hfa
  obtain ⟨μ, hrun, hpost⟩ := hfa ν hν
  rw [Program.rename_refl] at hrun
  simp only [bigSeq] at hrun
  obtain ⟨κ, hflow, hκ, -⟩ := hrun
  subst hκ
  obtain ⟨e, he, hleg, hp⟩ := hnb ν hν κ hflow hpost
  refine ⟨[(qs, ms, e)], ?_, by simp, by simp, κ, ?_, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    exact ⟨hm, he⟩
  · simp only [List.map_cons, List.map_nil, bigSeq]
    exact ⟨κ, sem_gseg.mpr ⟨hflow, hleg⟩, rfl, trivial⟩
  · simpa [qfOf] using hp

namespace Platoon3Link

open DL DLCalTiming DLRel Set

/-! ## One link -/

theorem hroot4 : (1/4 : ℝ) * (1/4) - 3/4 * (1/4) + 1/8 = 0 := by norm_num

/-- One link's constants: set point `c`; linear-form boxes `[b, a]` (`ρ = 1/4`) and `[e, d]`
(`ρ = 1/2`); projected-gap bounds `[P, U]`. -/
structure LinkC where
  c : ℝ
  a : ℝ
  b : ℝ
  d : ℝ
  e : ℝ
  P : ℝ
  U : ℝ

def LinkOK (p : LinkC) : Prop :=
  0 ≤ p.a ∧ p.b ≤ 0 ∧ 0 ≤ p.d ∧ p.e ≤ 0 ∧ p.P ≤ p.c ∧ p.c ≤ p.U ∧ 0 ≤ p.c ∧ p.c ≤ 60

/-- Safe-side term of `x + 2y ≤ U`. -/
def pgLe (wx wy : Var 6) (U : ℝ) : Term (Var 6) :=
  Term.binop .sub
    (Term.binop .add (Term.var wx) (Term.binop .mul (Term.const 2) (Term.var wy))) (Term.const U)

theorem eval_pgLe (wx wy : Var 6) (U c : ℝ) (z : State (Var 6)) :
    Term.eval (pgLe wx wy U) z = 2 * Term.eval (linLe wx wy (1/2) c ((U - c)/2)) z := by
  simp only [pgLe, linLe, eval_linQ, Term.eval, AOp.interp]; ring

/-- The four guard atoms of a link (rated closing rate, projected gap). -/
noncomputable def guardT (W : Fin 6 → Var 6) (jx jy : Fin 6) (p : LinkC) :
    List (Term (Var 6)) :=
  [thrGe (W jy) (-10), thrLe (W jy) 10, pgGe (W jx) (W jy) p.P, pgLe (W jx) (W jy) p.U]

/-- The four linear-form atoms of a link. -/
noncomputable def linT (W : Fin 6 → Var 6) (jx jy : Fin 6) (p : LinkC) : List (Term (Var 6)) :=
  [linLe (W jx) (W jy) (1/4) p.c p.a, linGe (W jx) (W jy) (1/4) p.c p.b,
   linLe (W jx) (W jy) (1/2) p.c p.d, linGe (W jx) (W jy) (1/2) p.c p.e]

/-- A mode's kept atoms: the three links' guard atoms, their linear forms, then any derived
bounds (`extra`), in the certificate's order. -/
noncomputable def termsW (W : Fin 6 → Var 6) (p1 p2 p3 : LinkC) (extra : List (Term (Var 6))) :
    List (Term (Var 6)) :=
  guardT W 0 1 p1 ++ guardT W 2 3 p2 ++ guardT W 4 5 p3 ++
    linT W 0 1 p1 ++ linT W 2 3 p2 ++ linT W 4 5 p3 ++ extra

theorem boxle_scale {α : Program (Var 6)} {t t' : Term (Var 6)} {ν : State (Var 6)}
    (h : ∀ z, Term.eval t z = 2 * Term.eval t' z)
    (hb : BoxLe α (fun ω => Term.eval t' ω) ν) : BoxLe α (fun ω => Term.eval t ω) ν := by
  intro ω hω
  have := hb ω hω
  simp only at this ⊢
  rw [h]; linarith

/-! ## O2 along the joint flows, right side -/

section Right
variable (fL fR : Fin 6 → Term (Var 6)) (lamv : ℝ) (hlam : 0 ≤ lamv) (dom : Formula (Var 6))

include hlam in
theorem stayR_linLe (jx jy : Fin 6) (r c K : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : 0 ≤ K) (hF : LinkField Rv fR jx jy c)
    (ν : State (Var 6)) (h : Term.eval (linLe (Rv jx) (Rv jy) r c K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (linLe (Rv jx) (Rv jy) r c K) ω) ν :=
  boxle_R_of_super _ fL fR lamv hlam dom dom
    (fun i hi => by simp [linLe, linQ, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (super_linear_le_R (a := 1/8) (b := 3/4) hroot hσ hK fR dom (fun z _ => hF.1 z)
      (fun z _ => hF.2 z)) h

include hlam in
theorem stayR_linGe (jx jy : Fin 6) (r c K : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : K ≤ 0) (hF : LinkField Rv fR jx jy c)
    (ν : State (Var 6)) (h : Term.eval (linGe (Rv jx) (Rv jy) r c K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (linGe (Rv jx) (Rv jy) r c K) ω) ν :=
  boxle_R_of_super _ fL fR lamv hlam dom dom
    (fun i hi => by simp [linGe, linQ, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (super_linear_ge_R (a := 1/8) (b := 3/4) hroot hσ hK fR dom (fun z _ => hF.1 z)
      (fun z _ => hF.2 z)) h

include hlam in
theorem stayR_derGe (jx jy : Fin 6) (r c K K' : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : K ≤ 0) (hr : 0 ≤ r) (hKK : r * (K' - c) ≤ K)
    (hF : LinkField Rv fR jx jy c)
    (ν : State (Var 6)) (hq : Term.eval (linGe (Rv jx) (Rv jy) r c K) ν ≤ 0)
    (h : Term.eval (thrGe (Rv jx) K') ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (thrGe (Rv jx) K') ω) ν :=
  stay_given (Fq := leF (linGe (Rv jx) (Rv jy) r c K)) (fun z => sat_leF _ z)
    (fun ν' h' => stayR_linGe fL fR lamv hlam dom jx jy r c K hroot hσ hK hF ν' h')
    (fun ν' h' => boxle_R_of_super _ fL fR lamv hlam _ _
      (fun i hi => by simp [thrGe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
      (super_derived_ge_R hr hKK fR (Formula.and dom (leF (linGe (Rv jx) (Rv jy) r c K)))
        (fun z _ => hF.1 z) (fun z hz => (sat_leF _ z).mp hz.2)) h') ν hq h

include hlam in
/-- The rated closing rate's lower face: at `y = −10`, `y' > 0` on the evolve box. -/
theorem stayR_ylo (jx jy : Fin 6) (c : ℝ) (hc : 0 ≤ c) (hF : LinkField Rv fR jx jy c)
    (hbox : ∀ z, Formula.sat dom z → z (Rv jx) ≤ 60)
    (ν : State (Var 6)) (h : Term.eval (thrGe (Rv jy) (-10)) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (thrGe (Rv jy) (-10)) ω) ν :=
  boxle_R_of_super _ fL fR lamv hlam dom dom
    (fun i hi => by simp [thrGe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (by
      intro z hz hge
      rw [eval_lie1R_thr jy _ (-1) (fun w z => tderiv_thrGe _ _ w z), hF.2 z]
      have hy : z (Rv jy) ≤ -10 := by simp [thrGe, Term.eval, AOp.interp] at hge; linarith
      have hx := hbox z hz
      nlinarith) h

include hlam in
/-- The rated closing rate's upper face: at `y = 10`, `y' < 0` on the evolve box. -/
theorem stayR_yhi (jx jy : Fin 6) (c : ℝ) (hc : c ≤ 60) (hF : LinkField Rv fR jx jy c)
    (hbox : ∀ z, Formula.sat dom z → 0 ≤ z (Rv jx))
    (ν : State (Var 6)) (h : Term.eval (thrLe (Rv jy) 10) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
      (fun ω => Term.eval (thrLe (Rv jy) 10) ω) ν :=
  boxle_R_of_super _ fL fR lamv hlam dom dom
    (fun i hi => by simp [thrLe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (by
      intro z hz hge
      rw [eval_lie1R_thr jy _ 1 (fun w z => tderiv_thrLe _ _ w z), hF.2 z]
      have hy : 10 ≤ z (Rv jy) := by simp [thrLe, Term.eval, AOp.interp] at hge; linarith
      have hx := hbox z hz
      nlinarith) h

include hlam in
/-- **One link's eight atoms stay** (guard atoms and linear forms; each from a base where
the link's linear forms and the atom hold). Right side. -/
theorem stayR_link (jx jy : Fin 6) (p : LinkC) (ok : LinkOK p) (hF : LinkField Rv fR jx jy p.c)
    (hbox : ∀ z, Formula.sat dom z → 0 ≤ z (Rv jx) ∧ z (Rv jx) ≤ 60) :
    ∀ t ∈ guardT Rv jx jy p ++ linT Rv jx jy p, ∀ ν, Term.eval t ν ≤ 0 →
      BoxLe (Program.ode (jointSys fL fR (Term.const lamv)) dom)
        (fun ω => Term.eval t ω) ν := by
  obtain ⟨ka, kb, kd, ke, kP, kU, kc0, kc1⟩ := ok
  intro t ht ν ht0
  simp only [guardT, linT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  have hs4 : (0:ℝ) ≤ 3/4 - 1/4 := by norm_num
  have hs2 : (0:ℝ) ≤ 3/4 - 1/2 := by norm_num
  rcases ht with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · exact stayR_ylo fL fR lamv hlam dom jx jy p.c kc0 hF (fun z hz => (hbox z hz).2) ν ht0
  · exact stayR_yhi fL fR lamv hlam dom jx jy p.c kc1 hF (fun z hz => (hbox z hz).1) ν ht0
  · refine boxle_scale (eval_pgGe _ _ p.P p.c) ?_
    refine stayR_linGe fL fR lamv hlam dom jx jy _ p.c _ hroot2 hs2 (by linarith) hF ν ?_
    have := (eval_pgGe (Rv jx) (Rv jy) p.P p.c ν) ▸ ht0
    linarith
  · refine boxle_scale (eval_pgLe _ _ p.U p.c) ?_
    refine stayR_linLe fL fR lamv hlam dom jx jy _ p.c _ hroot2 hs2 (by linarith) hF ν ?_
    have := (eval_pgLe (Rv jx) (Rv jy) p.U p.c ν) ▸ ht0
    linarith
  · exact stayR_linLe fL fR lamv hlam dom jx jy _ p.c _ hroot4 hs4 ka hF ν ht0
  · exact stayR_linGe fL fR lamv hlam dom jx jy _ p.c _ hroot4 hs4 kb hF ν ht0
  · exact stayR_linLe fL fR lamv hlam dom jx jy _ p.c _ hroot2 hs2 kd hF ν ht0
  · exact stayR_linGe fL fR lamv hlam dom jx jy _ p.c _ hroot2 hs2 ke hF ν ht0

end Right

/-! ## O2 along the joint flows, left side -/

section Left
variable (fL fR : Fin 6 → Term (Var 6)) (lam : Term (Var 6)) (dom : Formula (Var 6))

theorem stayL_linLe (jx jy : Fin 6) (r c K : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : 0 ≤ K) (hF : LinkField Lv fL jx jy c)
    (ν : State (Var 6)) (h : Term.eval (linLe (Lv jx) (Lv jy) r c K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (linLe (Lv jx) (Lv jy) r c K) ω) ν :=
  boxle_L_of_super _ fL fR lam dom dom
    (fun i hi => by simp [linLe, linQ, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (super_linear_le_L (a := 1/8) (b := 3/4) hroot hσ hK fL dom (fun z _ => hF.1 z)
      (fun z _ => hF.2 z)) h

theorem stayL_linGe (jx jy : Fin 6) (r c K : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : K ≤ 0) (hF : LinkField Lv fL jx jy c)
    (ν : State (Var 6)) (h : Term.eval (linGe (Lv jx) (Lv jy) r c K) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (linGe (Lv jx) (Lv jy) r c K) ω) ν :=
  boxle_L_of_super _ fL fR lam dom dom
    (fun i hi => by simp [linGe, linQ, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (super_linear_ge_L (a := 1/8) (b := 3/4) hroot hσ hK fL dom (fun z _ => hF.1 z)
      (fun z _ => hF.2 z)) h

theorem stayL_derGe (jx jy : Fin 6) (r c K K' : ℝ) (hroot : r * r - 3/4 * r + 1/8 = 0)
    (hσ : 0 ≤ 3/4 - r) (hK : K ≤ 0) (hr : 0 ≤ r) (hKK : r * (K' - c) ≤ K)
    (hF : LinkField Lv fL jx jy c)
    (ν : State (Var 6)) (hq : Term.eval (linGe (Lv jx) (Lv jy) r c K) ν ≤ 0)
    (h : Term.eval (thrGe (Lv jx) K') ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (thrGe (Lv jx) K') ω) ν :=
  stay_given (Fq := leF (linGe (Lv jx) (Lv jy) r c K)) (fun z => sat_leF _ z)
    (fun ν' h' => stayL_linGe fL fR lam dom jx jy r c K hroot hσ hK hF ν' h')
    (fun ν' h' => boxle_L_of_super _ fL fR lam _ _
      (fun i hi => by simp [thrGe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
      (super_derived_ge_L hr hKK fL (Formula.and dom (leF (linGe (Lv jx) (Lv jy) r c K)))
        (fun z _ => hF.1 z) (fun z hz => (sat_leF _ z).mp hz.2)) h') ν hq h

theorem stayL_ylo (jx jy : Fin 6) (c : ℝ) (hc : 0 ≤ c) (hF : LinkField Lv fL jx jy c)
    (hbox : ∀ z, Formula.sat dom z → z (Lv jx) ≤ 60)
    (ν : State (Var 6)) (h : Term.eval (thrGe (Lv jy) (-10)) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (thrGe (Lv jy) (-10)) ω) ν :=
  boxle_L_of_super _ fL fR lam dom dom
    (fun i hi => by simp [thrGe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (by
      intro z hz hge
      rw [eval_lie1L_thr jy _ (-1) (fun w z => tderiv_thrGe _ _ w z), hF.2 z]
      have hy : z (Lv jy) ≤ -10 := by simp [thrGe, Term.eval, AOp.interp] at hge; linarith
      have hx := hbox z hz
      nlinarith) h

theorem stayL_yhi (jx jy : Fin 6) (c : ℝ) (hc : c ≤ 60) (hF : LinkField Lv fL jx jy c)
    (hbox : ∀ z, Formula.sat dom z → 0 ≤ z (Lv jx))
    (ν : State (Var 6)) (h : Term.eval (thrLe (Lv jy) 10) ν ≤ 0) :
    BoxLe (Program.ode (jointSys fL fR lam) dom)
      (fun ω => Term.eval (thrLe (Lv jy) 10) ω) ν :=
  boxle_L_of_super _ fL fR lam dom dom
    (fun i hi => by simp [thrLe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
    (by
      intro z hz hge
      rw [eval_lie1L_thr jy _ 1 (fun w z => tderiv_thrLe _ _ w z), hF.2 z]
      have hy : 10 ≤ z (Lv jy) := by simp [thrLe, Term.eval, AOp.interp] at hge; linarith
      have hx := hbox z hz
      nlinarith) h

theorem stayL_link (jx jy : Fin 6) (p : LinkC) (ok : LinkOK p) (hF : LinkField Lv fL jx jy p.c)
    (hbox : ∀ z, Formula.sat dom z → 0 ≤ z (Lv jx) ∧ z (Lv jx) ≤ 60) :
    ∀ t ∈ guardT Lv jx jy p ++ linT Lv jx jy p, ∀ ν, Term.eval t ν ≤ 0 →
      BoxLe (Program.ode (jointSys fL fR lam) dom)
        (fun ω => Term.eval t ω) ν := by
  obtain ⟨ka, kb, kd, ke, kP, kU, kc0, kc1⟩ := ok
  intro t ht ν ht0
  simp only [guardT, linT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  have hs4 : (0:ℝ) ≤ 3/4 - 1/4 := by norm_num
  have hs2 : (0:ℝ) ≤ 3/4 - 1/2 := by norm_num
  rcases ht with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · exact stayL_ylo fL fR lam dom jx jy p.c kc0 hF (fun z hz => (hbox z hz).2) ν ht0
  · exact stayL_yhi fL fR lam dom jx jy p.c kc1 hF (fun z hz => (hbox z hz).1) ν ht0
  · refine boxle_scale (eval_pgGe _ _ p.P p.c) ?_
    refine stayL_linGe fL fR lam dom jx jy _ p.c _ hroot2 hs2 (by linarith) hF ν ?_
    have := (eval_pgGe (Lv jx) (Lv jy) p.P p.c ν) ▸ ht0
    linarith
  · refine boxle_scale (eval_pgLe _ _ p.U p.c) ?_
    refine stayL_linLe fL fR lam dom jx jy _ p.c _ hroot2 hs2 (by linarith) hF ν ?_
    have := (eval_pgLe (Lv jx) (Lv jy) p.U p.c ν) ▸ ht0
    linarith
  · exact stayL_linLe fL fR lam dom jx jy _ p.c _ hroot4 hs4 ka hF ν ht0
  · exact stayL_linGe fL fR lam dom jx jy _ p.c _ hroot4 hs4 kb hF ν ht0
  · exact stayL_linLe fL fR lam dom jx jy _ p.c _ hroot2 hs2 kd hF ν ht0
  · exact stayL_linGe fL fR lam dom jx jy _ p.c _ hroot2 hs2 ke hF ν ht0

end Left

end Platoon3Link
end RelCertifier
