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
* the explicit link solution and its box (`gS`, `rS`, `link_bounds`), from which the
  existence residual of every joint segment is discharged;
* the guard barrier along the reference's OWN flow (`gap_floor_Ronly`): a run that starts
  with `x ≥ G` and `x + 2y ≥ P` (`G ≤ P ≤ c`) ends with `x ≥ G` — the flow repels at the
  AEB floor.

New leaf.
-/
import RelCertifier.Proofs.Encoding.RightOnlyStay
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

/-- The damped link on side `W` at coordinates `jx` (gap), `jy` (closing rate). -/
def LinkField (W : Fin 6 → Var 6) (f : Fin 6 → Term (Var 6)) (jx jy : Fin 6) (c : ℝ) :
    Prop :=
  (∀ z, Term.eval (f jx) z = z (W jy)) ∧
  (∀ z, Term.eval (f jy) z = -(1/8) * (z (W jx) - c) - 3/4 * z (W jy))

/-- The narrowing formula of a term (`t ≤ 0`). -/
def leF (t : Term (Var 6)) : Formula (Var 6) := Formula.cmp CompOp.le t (Term.const 0)

theorem sat_leF (t : Term (Var 6)) (z : State (Var 6)) :
    Formula.sat (leF t) z ↔ Term.eval t z ≤ 0 := by
  simp [leF, Formula.sat, CompOp.interp, Term.eval]

theorem hroot4 : (1/4 : ℝ) * (1/4) - 3/4 * (1/4) + 1/8 = 0 := by norm_num
theorem hroot2 : (1/2 : ℝ) * (1/2) - 3/4 * (1/2) + 1/8 = 0 := by norm_num

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

/-- Safe-side term of `x + 2y ≥ P`. -/
def pgGe (wx wy : Var 6) (P : ℝ) : Term (Var 6) :=
  Term.binop .sub (Term.const P)
    (Term.binop .add (Term.var wx) (Term.binop .mul (Term.const 2) (Term.var wy)))

/-- Safe-side term of `x + 2y ≤ U`. -/
def pgLe (wx wy : Var 6) (U : ℝ) : Term (Var 6) :=
  Term.binop .sub
    (Term.binop .add (Term.var wx) (Term.binop .mul (Term.const 2) (Term.var wy))) (Term.const U)

theorem eval_pgGe (wx wy : Var 6) (P c : ℝ) (z : State (Var 6)) :
    Term.eval (pgGe wx wy P) z = 2 * Term.eval (linGe wx wy (1/2) c ((P - c)/2)) z := by
  simp only [pgGe, linGe, eval_linQ, Term.eval, AOp.interp]; ring

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

/-! ## The explicit link solution and its box -/

noncomputable def E1 (t : ℝ) : ℝ := Real.exp (-(1/2) * t)
noncomputable def E2 (t : ℝ) : ℝ := Real.exp (-(1/4) * t)

theorem hasDerivAt_E1 (t : ℝ) : HasDerivAt E1 (-(1/2) * E1 t) t := by
  have hin : HasDerivAt (fun u : ℝ => -(1/2) * u) (-(1/2)) t := by
    have h := (hasDerivAt_id t).const_mul (-(1/2 : ℝ))
    simp only [id, mul_one] at h
    exact h
  have h := (Real.hasDerivAt_exp (-(1/2) * t)).comp t hin
  rw [mul_comm] at h
  exact h

theorem hasDerivAt_E2 (t : ℝ) : HasDerivAt E2 (-(1/4) * E2 t) t := by
  have hin : HasDerivAt (fun u : ℝ => -(1/4) * u) (-(1/4)) t := by
    have h := (hasDerivAt_id t).const_mul (-(1/4 : ℝ))
    simp only [id, mul_one] at h
    exact h
  have h := (Real.hasDerivAt_exp (-(1/4) * t)).comp t hin
  rw [mul_comm] at h
  exact h

theorem E2_pos (t : ℝ) : 0 < E2 t := Real.exp_pos _
theorem E2_le (t : ℝ) (ht : 0 ≤ t) : E2 t ≤ 1 := by
  unfold E2; rw [Real.exp_le_one_iff]; linarith
theorem E1_zero : E1 0 = 1 := by simp [E1]
theorem E2_zero : E2 0 = 1 := by simp [E2]
theorem E1_sq (t : ℝ) : E1 t = E2 t * E2 t := by
  unfold E1 E2; rw [← Real.exp_add]; ring_nf

/-- The two modal coordinates of a link at set point `c`. -/
noncomputable def Q1 (c x y : ℝ) : ℝ := y + 1/4 * (x - c)
noncomputable def Q2 (c x y : ℝ) : ℝ := y + 1/2 * (x - c)

/-- The explicit link solution. -/
noncomputable def gS (c x y t : ℝ) : ℝ := c + 4 * (Q2 c x y * E2 t - Q1 c x y * E1 t)
noncomputable def rS (c x y t : ℝ) : ℝ := 2 * Q1 c x y * E1 t - Q2 c x y * E2 t

theorem gS_zero (c x y : ℝ) : gS c x y 0 = x := by
  simp only [gS, Q1, Q2, E1_zero, E2_zero]; ring
theorem rS_zero (c x y : ℝ) : rS c x y 0 = y := by
  simp only [rS, Q1, Q2, E1_zero, E2_zero]; ring

theorem gS_hasDeriv (c x y t : ℝ) : HasDerivAt (fun u => gS c x y u) (rS c x y t) t := by
  have h : HasDerivAt (fun u => c + 4 * (Q2 c x y * E2 u - Q1 c x y * E1 u))
      (4 * (Q2 c x y * (-(1/4) * E2 t) - Q1 c x y * (-(1/2) * E1 t))) t :=
    ((((hasDerivAt_E2 t).const_mul (Q2 c x y)).sub
      ((hasDerivAt_E1 t).const_mul (Q1 c x y))).const_mul 4).const_add c
  have e : rS c x y t = 4 * (Q2 c x y * (-(1/4) * E2 t) - Q1 c x y * (-(1/2) * E1 t)) := by
    simp only [rS]; ring
  rw [e]
  exact h

theorem rS_hasDeriv (c x y t : ℝ) : HasDerivAt (fun u => rS c x y u)
    (-(1/8) * (gS c x y t - c) - 3/4 * rS c x y t) t := by
  have h : HasDerivAt (fun u => 2 * Q1 c x y * E1 u - Q2 c x y * E2 u)
      (2 * Q1 c x y * (-(1/2) * E1 t) - Q2 c x y * (-(1/4) * E2 t)) t :=
    ((hasDerivAt_E1 t).const_mul (2 * Q1 c x y)).sub ((hasDerivAt_E2 t).const_mul (Q2 c x y))
  have e : -(1/8) * (gS c x y t - c) - 3/4 * rS c x y t
      = 2 * Q1 c x y * (-(1/2) * E1 t) - Q2 c x y * (-(1/4) * E2 t) := by
    simp only [gS, rS]; ring
  rw [e]
  exact h

theorem gap_hi_aux (a b u K : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hK : 0 ≤ K)
    (h1 : 2 * a ≤ K) (h2 : 4 * (a - b) ≤ K) : 4 * (a * u - b * (u * u)) ≤ K := by
  have huu : 0 ≤ u * (1 - u) := mul_nonneg hu0.le (by linarith)
  have hid : 4 * (a * u - b * (u * u)) = u * (4 * (a - b)) + 4 * b * (u * (1 - u)) := by ring
  rcases le_or_gt b 0 with hb0 | hb0
  · have e1 : 4 * b * (u * (1 - u)) ≤ 0 := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ -(4 * b)) huu; linarith
    rcases le_or_gt (4 * (a - b)) 0 with hn | hn
    · have : u * (4 * (a - b)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0.le hn
      linarith
    · have : u * (4 * (a - b)) ≤ 4 * (a - b) := by
        have := mul_le_mul_of_nonneg_right hu1 hn.le; linarith
      linarith
  · rcases le_or_gt a (2 * b) with hab2 | hab2
    · rcases le_or_gt a 0 with ha0 | ha0
      · have e1 : a * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hu0.le
        have e2 : 0 ≤ b * (u * u) := by positivity
        linarith
      · have e1 : 2 * a * (u * u) ≤ 4 * b * (u * u) := by
          have := mul_le_mul_of_nonneg_right (by linarith : 2 * a ≤ 4 * b) (by positivity : (0:ℝ) ≤ u * u)
          linarith
        have e2 : u * (2 - u) ≤ 1 := by nlinarith [sq_nonneg (1 - u)]
        have e3 : 2 * a * (u * (2 - u)) ≤ 2 * a := by
          have := mul_le_mul_of_nonneg_left e2 (by linarith : (0:ℝ) ≤ 2 * a); linarith
        nlinarith
    · have hid2 : 4 * (a * u - b * (u * u)) - 4 * (a - b) = 4 * ((u - 1) * (a - b * (u + 1))) := by
        ring
      have hx : 0 ≤ a - b * (u + 1) := by
        have : b * (u + 1) ≤ b * 2 := by
          have := mul_le_mul_of_nonneg_left (by linarith : u + 1 ≤ 2) hb0.le; linarith
        linarith
      have : (u - 1) * (a - b * (u + 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hx
      linarith

theorem gap_lo_aux (a b u K : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hK : 0 ≤ K)
    (h1 : -K ≤ 4 * a) (h2 : -K ≤ 4 * (a - b)) : -K ≤ 4 * (a * u - b * (u * u)) := by
  have huu : 0 ≤ u * (1 - u) := mul_nonneg hu0.le (by linarith)
  have hid : 4 * (a * u - b * (u * u)) = u * (4 * (a - b)) + 4 * b * (u * (1 - u)) := by ring
  rcases le_or_gt 0 b with hb0 | hb0
  · have e1 : 0 ≤ 4 * b * (u * (1 - u)) := by positivity
    rcases le_or_gt 0 (4 * (a - b)) with hn | hn
    · have : 0 ≤ u * (4 * (a - b)) := mul_nonneg hu0.le hn
      linarith
    · have : 4 * (a - b) ≤ u * (4 * (a - b)) := by
        have := mul_le_mul_of_nonneg_right hu1 (by linarith : (0:ℝ) ≤ -(4 * (a - b))); linarith
      linarith
  · have e1 : 0 ≤ -(b * (u * u)) := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ -b) (by positivity : (0:ℝ) ≤ u * u); linarith
    rcases le_or_gt 0 a with ha0 | ha0
    · have : 0 ≤ a * u := mul_nonneg ha0 hu0.le
      linarith
    · have : a ≤ a * u := by
        have := mul_le_mul_of_nonneg_right hu1 (by linarith : (0:ℝ) ≤ -a); linarith
      linarith

theorem rate_hi_aux (a b u y : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hy : y = 2 * b - a)
    (hy1 : y ≤ 10) (ha : -10 ≤ a) : 2 * b * (u * u) - a * u ≤ 10 := by
  have huu : 0 ≤ u * (1 - u) := mul_nonneg hu0.le (by linarith)
  rcases le_or_gt 0 b with hb0 | hb0
  · -- convex in `u`: below the chord `u ↦ u y`
    have hid : 2 * b * (u * u) - a * u = u * y - 2 * b * (u * (1 - u)) := by rw [hy]; ring
    have e1 : 0 ≤ 2 * b * (u * (1 - u)) := by positivity
    rcases le_or_gt y 0 with hy0 | hy0
    · have : u * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0.le hy0
      linarith
    · have : u * y ≤ y := by have := mul_le_mul_of_nonneg_right hu1 hy0.le; linarith
      linarith
  · have e1 : 2 * b * (u * u) ≤ 0 := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ -(2 * b)) (by positivity : (0:ℝ) ≤ u * u); linarith
    rcases le_or_gt 0 a with ha0 | ha0
    · have : 0 ≤ a * u := mul_nonneg ha0 hu0.le
      linarith
    · have : -(a * u) ≤ -a := by
        have := mul_le_mul_of_nonneg_right hu1 (by linarith : (0:ℝ) ≤ -a); linarith
      linarith

theorem rate_lo_aux (a b u y : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hy : y = 2 * b - a)
    (hy0 : -10 ≤ y) (ha : a ≤ 20) : -10 ≤ 2 * b * (u * u) - a * u := by
  have huu : 0 ≤ u * (1 - u) := mul_nonneg hu0.le (by linarith)
  rcases le_or_gt b 0 with hb0 | hb0
  · -- concave in `u`: above the chord
    have hid : 2 * b * (u * u) - a * u = u * y - 2 * b * (u * (1 - u)) := by rw [hy]; ring
    have e1 : 2 * b * (u * (1 - u)) ≤ 0 := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ -(2 * b)) huu; linarith
    rcases le_or_gt 0 y with hy0' | hy0'
    · have : 0 ≤ u * y := mul_nonneg hu0.le hy0'
      linarith
    · have : y ≤ u * y := by
        have := mul_le_mul_of_nonneg_right hu1 (by linarith : (0:ℝ) ≤ -y); linarith
      linarith
  · rcases le_or_gt a (4 * b) with ha4 | ha4
    · -- completing the square: `≥ −a² / (8 b) ≥ −a / 2 ≥ −10`
      rcases le_or_gt a 0 with ha0 | ha0
      · have e1 : 0 ≤ 2 * b * (u * u) := by positivity
        have e2 : a * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hu0.le
        linarith
      · have hsq : 0 ≤ (4 * b * u - a) ^ 2 := sq_nonneg _
        -- `8 b (2 b u² − a u) = (4 b u − a)² − a²  ≥ −a² ≥ −4 b a`
        have hkey : 8 * b * (2 * b * (u * u) - a * u) = (4 * b * u - a) ^ 2 - a * a := by ring
        have e1 : a * a ≤ 4 * b * a := by
          have := mul_le_mul_of_nonneg_right ha4 ha0.le; linarith
        have e2 : -(4 * b * a) ≤ 8 * b * (2 * b * (u * u) - a * u) := by nlinarith
        -- divide by `8 b > 0`
        have e3 : -(a / 2) ≤ 2 * b * (u * u) - a * u := by
          by_contra hc
          push_neg at hc
          have := mul_lt_mul_of_pos_left hc (by linarith : (0:ℝ) < 8 * b)
          nlinarith
        linarith
    · -- decreasing on `[0, 1]`: above the value at `u = 1`
      have hid : 2 * b * (u * u) - a * u - y = (u - 1) * (2 * b * (u + 1) - a) := by
        rw [hy]; ring
      have hx : 2 * b * (u + 1) - a ≤ 0 := by
        have : b * (u + 1) ≤ b * 2 := by
          have := mul_le_mul_of_nonneg_left (by linarith : u + 1 ≤ 2) hb0.le; linarith
        linarith
      have : 0 ≤ (u - 1) * (2 * b * (u + 1) - a) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hx
      linarith

/-- **The link stays in the evolve box** (`0 ≤ x ≤ 60`, `|y| ≤ 10`) for all time when it
starts there with the slow form `Q2 = y + (x − c)/2` in `[−K, (60 − c)/2]` (the
projected-gap guard; `4 K ≤ c`, `K ≤ 10`). `u = e^{−t/4}`: `x − c = 4 (Q2 u − Q1 u²)`, `y = 2 Q1 u² − Q2 u`. -/
theorem link_bounds (c K x y t : ℝ) (ht : 0 ≤ t) (hc1 : 20 ≤ c) (hc2 : c ≤ 60)
    (hK1 : 4 * K ≤ c) (hK2 : K ≤ 10)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 60) (hy0 : -10 ≤ y) (hy1 : y ≤ 10)
    (hq0 : -K ≤ Q2 c x y) (hq1 : 2 * Q2 c x y ≤ 60 - c) :
    (0 ≤ gS c x y t ∧ gS c x y t ≤ 60) ∧ (-10 ≤ rS c x y t ∧ rS c x y t ≤ 10) := by
  have hu0 : 0 < E2 t := E2_pos t
  have hu1 : E2 t ≤ 1 := E2_le t ht
  have hab : 4 * (Q2 c x y - Q1 c x y) = x - c := by simp only [Q1, Q2]; ring
  have hyab : y = 2 * Q1 c x y - Q2 c x y := by simp only [Q1, Q2]; ring
  have hg : gS c x y t = c + 4 * (Q2 c x y * E2 t - Q1 c x y * (E2 t * E2 t)) := by
    unfold gS; rw [E1_sq]
  have hr : rS c x y t = 2 * Q1 c x y * (E2 t * E2 t) - Q2 c x y * E2 t := by
    unfold rS; rw [E1_sq]
  rw [hg, hr]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have := gap_lo_aux (Q2 c x y) (Q1 c x y) (E2 t) c hu0 hu1 (by linarith) (by linarith)
      (by linarith)
    linarith
  · have := gap_hi_aux (Q2 c x y) (Q1 c x y) (E2 t) (60 - c) hu0 hu1 (by linarith) hq1
      (by linarith)
    linarith
  · exact rate_lo_aux _ _ _ y hu0 hu1 hyab hy0 (by linarith)
  · exact rate_hi_aux _ _ _ y hu0 hu1 hyab hy1 (by linarith)

/-! ## The guard barrier along the reference's own flow -/

/-- **The AEB floor repels.** Along a run of the reference's own flow (a link at set point
`c`), a gap that starts at `x ≥ G` with `x + 2y ≥ P` (`G ≤ P ≤ c`) stays at `x ≥ G`: the slow
form `y + (x − c)/2 ≥ (P − c)/2` only decays toward `0`, and on it `x' = y ≥ (G − x)/2 + …`
points away from the floor. -/
theorem gap_floor_Ronly (fR : Fin 6 → Term (Var 6)) (dom : Formula (Var 6)) (jx jy : Fin 6)
    (c G P : ℝ) (hGP : G ≤ P) (hPc : P ≤ c) (hF : LinkField Rv fR jx jy c)
    {ν μ : State (Var 6)}
    (hrun : Program.sem (Program.ode (rightBlock fR (Term.const 1)) dom) ν μ)
    (hP : Term.eval (pgGe (Rv jx) (Rv jy) P) ν ≤ 0) (hG : G ≤ ν (Rv jx)) :
    G ≤ μ (Rv jx) := by
  have hs2 : (0:ℝ) ≤ 3/4 - 1/2 := by norm_num
  have hq : Term.eval (linGe (Rv jx) (Rv jy) (1/2) c ((P - c)/2)) ν ≤ 0 := by
    have := (eval_pgGe (Rv jx) (Rv jy) P c ν) ▸ hP
    linarith
  have hx : Term.eval (thrGe (Rv jx) G) ν ≤ 0 := by
    simp only [thrGe, Term.eval, AOp.interp]; linarith
  have hbox := stay_given (sys := rightBlock fR (Term.const 1)) (dom := dom)
    (Fq := leF (linGe (Rv jx) (Rv jy) (1/2) c ((P - c)/2))) (fun z => sat_leF _ z)
    (fun ν' h' => boxle_Ronly_of_super _ fR 1 zero_le_one dom dom
      (fun i hi => by simp [linGe, linQ, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
      (super_linear_ge_R (a := 1/8) (b := 3/4) hroot2 hs2 (by linarith) fR dom
        (fun z _ => hF.1 z) (fun z _ => hF.2 z)) h')
    (fun ν' h' => boxle_Ronly_of_super _ fR 1 zero_le_one _ _
      (fun i hi => by simp [thrGe, Term.fv, Lv, Rv] at hi) (fun x hx => hx)
      (super_derived_ge_R (r := 1/2) (by norm_num) (by linarith) fR
        (Formula.and dom (leF (linGe (Rv jx) (Rv jy) (1/2) c ((P - c)/2))))
        (fun z _ => hF.1 z) (fun z hz => (sat_leF _ z).mp hz.2)) h') ν hq hx
  have := hbox μ hrun
  simp only [thrGe, Term.eval, AOp.interp] at this
  linarith

end Platoon3Link
end RelCertifier
