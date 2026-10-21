/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_linkloss`: Assumption 1 of the right model — PROVED (repaired model)

Over the instance's guarded right automaton `Gr` (the repaired model,
`docs/SUITE-REDESIGN.md` §20, §21), the lowered right guards, `ε_r = 1`.

**`WellFormedR` holds** (`platoon3_linkloss_wellFormedR`, Z3-free), style (a) at every mode:

* `FOLLOW` (`platoon3_linkloss_wellFormedR_follow`): its guard (the operating range) is forward
  invariant under the three damped links (`Platoon3Link.link_guard_Ronly`, plus the evolve box
  every run keeps). Existence: the explicit link solution (`solΦ`, `link_bounds`).
* `BRAKE1`–`BRAKE3`, the LATCHED AEB sinks of the 2026-10-10 repair
  (`platoon3_linkloss_wellFormedR_brake`): guard `g_k < 20`, `0 ≤ g_k + 2 r_k < 20`, the other
  two links in their operating range; flow `r_k' = −r_k/2` (speed matching) on the braking
  link, the damped links elsewhere. The braking link keeps its guard part
  (`Platoon3Link.brake_guard_Ronly`: `g + 2r` conserved, `r` decaying), the other links keep
  theirs (`link_guard_Ronly`). Existence: the explicit solution `Platoon3Link.solB_sol`.

(Until 2026-10-10 the sinks braked at a constant `4 m/s²` on the guard `g_k < 20` alone, and
the model was refuted here: from `g₁ = 19`, `r₁ = 0`, the other links at rest at 30, the run
of duration 1 ends at `g₁ = 21`, outside `BRAKE1`'s guard, its only declared successor.)
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.BenchIR.platoon3_linkloss
import RelCertifier.InstancesV2.WellFormed.Platoon3Link

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Platoon3Linkloss

open DL DLCalTiming DLRel Parse Set Platoon3Link


def vs : List String := ["g1", "r1", "g2", "r2", "g3", "r3"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := platoon3_linkloss_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 6 → Term (Var 6) := hostDyn vs 6 Side.R (mR q)
noncomputable def domR : Formula (Var 6) := hostEvolve vs 6 Side.R (mR 0)
theorem hqm0_125 : Run.parseRat "-0.125" = some ((-1:ℚ)/8) := by
  have h : parseQ "-0.125" = some (⟨-125, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq0_75 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq30_0 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq60_0 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hqm10_0 : Run.parseRat "-10.0" = some (-10 : ℚ) := by
  have h : parseQ "-10.0" = some (⟨-100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq10_0 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq25_0 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq2_0 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq20_0 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq58_0 : Run.parseRat "58.0" = some (58 : ℚ) := by
  have h : parseQ "58.0" = some (⟨580, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq21_0 : Run.parseRat "21.0" = some (21 : ℚ) := by
  have h : parseQ "21.0" = some (⟨210, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq59_0 : Run.parseRat "59.0" = some (59 : ℚ) := by
  have h : parseQ "59.0" = some (⟨590, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num
theorem hq19_0 : Run.parseRat "19.0" = some (19 : ℚ) := by
  have h : parseQ "19.0" = some (⟨190, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; try norm_num


/-! ## Evaluations of the lowered data -/

/-- Three damped links on side `W`, set points `c₁, c₂, c₃`. -/
def PairField3 (W : Fin 6 → Var 6) (f : Fin 6 → Term (Var 6)) (c1 c2 c3 : ℝ) : Prop :=
  ∀ z : State (Var 6),
    Term.eval (f 0) z = z (W 1) ∧
    Term.eval (f 1) z = -(1/8) * (z (W 0) - c1) - 3/4 * z (W 1) ∧
    Term.eval (f 2) z = z (W 3) ∧
    Term.eval (f 3) z = -(1/8) * (z (W 2) - c2) - 3/4 * z (W 3) ∧
    Term.eval (f 4) z = z (W 5) ∧
    Term.eval (f 5) z = -(1/8) * (z (W 4) - c3) - 3/4 * z (W 5)

theorem fR_field : PairField3 Rv (fR 0) 30 30 30 := by
  intro z
  simp [fR, hostDyn, mR, platoon3_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hqm0_125, hq0_75,
    hq30_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]
  refine ⟨by ring, by ring, by ring⟩

/-- The evolve box (both sides): `g_i ∈ [0, 60]`, `r_i ∈ [−10, 10]`. -/
def Box (W : Fin 6 → Var 6) (x : State (Var 6)) : Prop :=
  (0 ≤ x (W 0) ∧ x (W 0) ≤ 60 ∧ -10 ≤ x (W 1) ∧ x (W 1) ≤ 10) ∧
  (0 ≤ x (W 2) ∧ x (W 2) ≤ 60 ∧ -10 ≤ x (W 3) ∧ x (W 3) ≤ 10) ∧
  (0 ≤ x (W 4) ∧ x (W 4) ≤ 60 ∧ -10 ≤ x (W 5) ∧ x (W 5) ≤ 10)

theorem sat_domR (x : State (Var 6)) : Formula.sat domR x ↔ Box Rv x := by
  simp only [domR, hostEvolve, mR, platoon3_linkloss_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hq0_0, hq60_0, hqm10_0, hq10_0, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv,
    Box, and_assoc]

/-! ## O2: the kept atoms stay along the joint flows (`Platoon3Link` shape lemmas) -/

theorem linkFields {W : Fin 6 → Var 6} {f : Fin 6 → Term (Var 6)} {c1 c2 c3 : ℝ}
    (h : PairField3 W f c1 c2 c3) :
    LinkField W f 0 1 c1 ∧ LinkField W f 2 3 c2 ∧ LinkField W f 4 5 c3 :=
  ⟨⟨fun z => (h z).1, fun z => (h z).2.1⟩, ⟨fun z => (h z).2.2.1, fun z => (h z).2.2.2.1⟩,
    ⟨fun z => (h z).2.2.2.2.1, fun z => (h z).2.2.2.2.2⟩⟩

/-! ## Existence: the explicit solution of the (linear) right `FOLLOW` mode -/

noncomputable def solC (c : ℝ) (b : State (Var 6)) (t : ℝ) : Fin 6 → ℝ
  | ⟨0, _⟩ => gS c (b (Rv 0)) (b (Rv 1)) t
  | ⟨1, _⟩ => rS c (b (Rv 0)) (b (Rv 1)) t
  | ⟨2, _⟩ => gS c (b (Rv 2)) (b (Rv 3)) t
  | ⟨3, _⟩ => rS c (b (Rv 2)) (b (Rv 3)) t
  | ⟨4, _⟩ => gS c (b (Rv 4)) (b (Rv 5)) t
  | ⟨5, _⟩ => rS c (b (Rv 4)) (b (Rv 5)) t

noncomputable def solΦ (c : ℝ) (b : State (Var 6)) (t : ℝ) : State (Var 6) :=
  fun x => if x.1 = Side.R then solC c b t x.2 else b x

theorem solΦ_R (c : ℝ) (b : State (Var 6)) (t : ℝ) (j : Fin 6) :
    solΦ c b t (Rv j) = solC c b t j := by simp [solΦ, Rv]

theorem solΦ_zero (c : ℝ) (b : State (Var 6)) : solΦ c b 0 = b := by
  funext x
  obtain ⟨s, j⟩ := x
  by_cases hs : s = Side.R
  · subst hs
    rw [show ((Side.R, j) : Var 6) = Rv j from rfl, solΦ_R]
    fin_cases j <;> simp [solC, gS_zero, rS_zero, Rv]
  · simp [solΦ, hs]

theorem solΦ_frozen (c : ℝ) (b : State (Var 6)) (t : ℝ) (x : Var 6) (hx : x.1 ≠ Side.R) :
    solΦ c b t x = b x := by simp [solΦ, hx]

/-- The link's own box and slow form at the anchor (the evolve box, the projected-gap
guard). -/
def LinkStart (c : ℝ) (x y : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 60 ∧ -10 ≤ y ∧ y ≤ 10 ∧ -(9/2) ≤ Q2 c x y ∧ 2 * Q2 c x y ≤ 60 - c

def QBounds (c : ℝ) (b : State (Var 6)) : Prop :=
  LinkStart c (b (Rv 0)) (b (Rv 1)) ∧ LinkStart c (b (Rv 2)) (b (Rv 3)) ∧
    LinkStart c (b (Rv 4)) (b (Rv 5))

theorem solΦ_box (c : ℝ) (hc1 : 20 ≤ c) (hc2 : c ≤ 60) (b : State (Var 6)) (hb : QBounds c b)
    (t : ℝ) (ht : 0 ≤ t) : Box Rv (solΦ c b t) := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := hb
  have k0 := link_bounds c (9/2) _ _ t ht hc1 hc2 (by linarith) (by norm_num) a1 a2 a3 a4 a5 a6
  have k1 := link_bounds c (9/2) _ _ t ht hc1 hc2 (by linarith) (by norm_num) b1 b2 b3 b4 b5 b6
  have k2 := link_bounds c (9/2) _ _ t ht hc1 hc2 (by linarith) (by norm_num) d1 d2 d3 d4 d5 d6
  simp only [Box, solΦ_R]
  exact ⟨⟨k0.1.1, k0.1.2, k0.2.1, k0.2.2⟩, ⟨k1.1.1, k1.1.2, k1.2.1, k1.2.2⟩,
    ⟨k2.1.1, k2.1.2, k2.2.1, k2.2.2⟩⟩

/-- The explicit solution solves the stretched right block (`λ = 1`). -/
theorem solΦ_deriv (c : ℝ) (fR : Fin 6 → Term (Var 6)) (hF : PairField3 Rv fR c c c)
    (b : State (Var 6)) (s t : ℝ) :
    ∀ p ∈ rightBlock fR (Term.const 1),
      HasDerivWithinAt (fun u => solΦ c b u p.1) (p.2.eval (solΦ c b t)) (Icc 0 s) t := by
  intro p hp
  simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
  obtain ⟨i, rfl⟩ := hp
  have hfun : (fun u => solΦ c b u (Rv i)) = fun u => solC c b u i := by
    funext u; exact solΦ_R c b u i
  simp only [hfun, Term.eval, AOp.interp, one_mul]
  refine HasDerivAt.hasDerivWithinAt ?_
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := hF (solΦ c b t)
  fin_cases i
  · rw [show ((⟨0, by norm_num⟩ : Fin 6)) = (0 : Fin 6) from rfl, f0, solΦ_R]
    exact gS_hasDeriv c _ _ t
  · rw [show ((⟨1, by norm_num⟩ : Fin 6)) = (1 : Fin 6) from rfl, f1, solΦ_R, solΦ_R]
    exact rS_hasDeriv c _ _ t
  · rw [show ((⟨2, by norm_num⟩ : Fin 6)) = (2 : Fin 6) from rfl, f2, solΦ_R]
    exact gS_hasDeriv c _ _ t
  · rw [show ((⟨3, by norm_num⟩ : Fin 6)) = (3 : Fin 6) from rfl, f3, solΦ_R, solΦ_R]
    exact rS_hasDeriv c _ _ t
  · rw [show ((⟨4, by norm_num⟩ : Fin 6)) = (4 : Fin 6) from rfl, f4, solΦ_R]
    exact gS_hasDeriv c _ _ t
  · rw [show ((⟨5, by norm_num⟩ : Fin 6)) = (5 : Fin 6) from rfl, f5, solΦ_R, solΦ_R]
    exact rS_hasDeriv c _ _ t



/-! ## The GUARDED right automaton (the file's modes, declared `next` lists, entered guards) -/

noncomputable def modeW (q : ℕ) : RMode (Var 6) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- An edge tests the lowered guard of the mode it ENTERS (the paper's `?guard_m(x)`). -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 6) :=
  { src := s, tgt := t, guard := hostGuard vs 6 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (FOLLOW 0, BRAKE1 1, BRAKE2 2, BRAKE3 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (2, 2), (3, 3)]

noncomputable def Gr : SearchGraph (Var 6) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 4 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 6)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The reference's `FOLLOW` guard (the operating range), from its parts. -/
theorem guardR0_of (x : State (Var 6))
    (h1 : 20 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 60 ∧ -10 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 10 ∧
      21 ≤ x (Rv 0) + 2 * x (Rv 1) ∧ x (Rv 0) + 2 * x (Rv 1) ≤ 59)
    (h2 : 20 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 60 ∧ -10 ≤ x (Rv 3) ∧ x (Rv 3) ≤ 10 ∧
      21 ≤ x (Rv 2) + 2 * x (Rv 3) ∧ x (Rv 2) + 2 * x (Rv 3) ≤ 59)
    (h3 : 20 ≤ x (Rv 4) ∧ x (Rv 4) ≤ 60 ∧ -10 ≤ x (Rv 5) ∧ x (Rv 5) ≤ 10 ∧
      21 ≤ x (Rv 4) + 2 * x (Rv 5) ∧ x (Rv 4) + 2 * x (Rv 5) ≤ 59) :
    Formula.sat (hostGuard vs 6 Side.R (mR 0)) x := by
  simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, hq19_0, hq59_0, hqm10_0, hq10_0, hq2_0, hq20_0, hq58_0, hq25_0, hq21_0, hq60_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]
  simp only [Rv] at h1 h2 h3
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h3
  repeat' apply And.intro
  all_goals linarith


theorem epsR_eq : epsR platoon3_linkloss_IRv2 = 1 := by
  simp [epsR, platoon3_linkloss_IRv2, hq1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vs 6 Side.R (mR q)

/-- One link's operating range. -/
def LinkOp (x : State (Var 6)) (jx jy : Fin 6) : Prop :=
  20 ≤ x (Rv jx) ∧ x (Rv jx) ≤ 60 ∧ -10 ≤ x (Rv jy) ∧ x (Rv jy) ≤ 10 ∧
    21 ≤ x (Rv jx) + 2 * x (Rv jy) ∧ x (Rv jx) + 2 * x (Rv jy) ≤ 59

theorem sat_guardR0 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 0)) x ↔ LinkOp x 0 1 ∧ LinkOp x 2 3 ∧ LinkOp x 4 5 := by
  constructor
  · intro h
    simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, hq19_0, hq59_0,
      hqm10_0, hq10_0, hq2_0, hq20_0, hq58_0, hq25_0, hq21_0, hq60_0, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, AOp.interp, Rv] at h
    simp only [LinkOp, Rv]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      tauto
  · rintro ⟨h1, h2, h3⟩
    exact guardR0_of x h1 h2 h3

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 6)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- **Assumption 1 at `FOLLOW`** (style (a), Z3-free). -/
theorem platoon3_linkloss_wellFormedR_follow :
    WellFormedRMode Gr guardR (epsR platoon3_linkloss_IRv2) 0 := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  obtain ⟨h1, h2, h3⟩ := (sat_guardR0 x).mp hg
  have hbox := (sat_domR x).mp hd
  obtain ⟨L1, L2, L3⟩ := linkFields fR_field
  refine ⟨?_, ?_⟩
  · have hQ : QBounds 30 x := by
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h3
      obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := hbox
      simp only [QBounds, LinkStart, Q2]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
        linarith
    refine ⟨solΦ 30 x, ⟨by norm_num, solΦ_zero _ _, fun t _ => solΦ_deriv 30 (fR 0) fR_field x 1 t,
      ?_, ?_⟩⟩
    · intro t _ y hy
      refine solΦ_frozen _ _ _ y (fun hyR => hy ?_)
      obtain ⟨sy, j⟩ := y
      simp only at hyR
      subst hyR
      simp only [modeW, rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
    · intro t ht
      show Formula.sat domR _
      rw [sat_domR]
      exact solΦ_box 30 (by norm_num) (by norm_num) _ hQ t ht.1
  · intro t Φ _ H
    have k1 := link_guard_Ronly (fR 0) domR 0 1 30 (by norm_num) (by norm_num) L1 H
      h1.1 h1.2.2.2.2.1 h1.2.2.2.2.2
    have k2 := link_guard_Ronly (fR 0) domR 2 3 30 (by norm_num) (by norm_num) L2 H
      h2.1 h2.2.2.2.2.1 h2.2.2.2.2.2
    have k3 := link_guard_Ronly (fR 0) domR 4 5 30 (by norm_num) (by norm_num) L3 H
      h3.1 h3.2.2.2.2.1 h3.2.2.2.2.2
    obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := (sat_domR _).mp H.end_dom
    exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR0 _).mpr
      ⟨⟨k1.1, x1, y0, y1, k1.2.1, k1.2.2⟩, ⟨k2.1, x3, y2, y3, k2.2.1, k2.2.2⟩,
        ⟨k3.1, x5, y4, y5, k3.2.1, k3.2.2⟩⟩⟩

/-! ## The latched AEB sinks -/

theorem hqm0_5 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem fR_bfield1 : BField3 (fR 1) true false false := by
  intro z
  simp [fR, hostDyn, mR, platoon3_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hqm0_125, hq0_75,
    hq30_0, hqm0_5, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv, lF]
  refine ⟨by ring, by ring, by ring⟩

theorem fR_bfield2 : BField3 (fR 2) false true false := by
  intro z
  simp [fR, hostDyn, mR, platoon3_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hqm0_125, hq0_75,
    hq30_0, hqm0_5, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv, lF]
  refine ⟨by ring, by ring, by ring⟩

theorem fR_bfield3 : BField3 (fR 3) false false true := by
  intro z
  simp [fR, hostDyn, mR, platoon3_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hqm0_125, hq0_75,
    hq30_0, hqm0_5, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv, lF]
  refine ⟨by ring, by ring, by ring⟩

/-- The sink guards, evaluated (`BRAKEk`: the braking link's part, the other two links'
operating range). -/
theorem sat_guardB1 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 1)) x ↔ BrkR x 0 1 ∧ OpR x 2 3 ∧ OpR x 4 5 := by
  simp only [BrkR, OpR, Rv]
  simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, hq2_0, hq20_0, hq0_0,
    hq59_0, hqm10_0, hq10_0, hq21_0, hq60_0, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  constructor
  · intro h; refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      first | tauto | linarith [h]
  · intro h
    obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := h
    repeat' apply And.intro
    all_goals linarith

theorem sat_guardB2 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 2)) x ↔ BrkR x 2 3 ∧ OpR x 0 1 ∧ OpR x 4 5 := by
  simp only [BrkR, OpR, Rv]
  simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, hq2_0, hq20_0, hq0_0,
    hq59_0, hqm10_0, hq10_0, hq21_0, hq60_0, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  constructor
  · intro h; refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      first | tauto | linarith [h]
  · intro h
    obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := h
    repeat' apply And.intro
    all_goals linarith

theorem sat_guardB3 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 3)) x ↔ BrkR x 4 5 ∧ OpR x 0 1 ∧ OpR x 2 3 := by
  simp only [BrkR, OpR, Rv]
  simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, hq2_0, hq20_0, hq0_0,
    hq59_0, hqm10_0, hq10_0, hq21_0, hq60_0, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  constructor
  · intro h; refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      first | tauto | linarith [h]
  · intro h
    obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := h
    repeat' apply And.intro
    all_goals linarith

/-- A link's operating range at the end of a run, from `link_guard_Ronly` and the box. -/
theorem opR_end {fR' : Fin 6 → Term (Var 6)} {x : State (Var 6)} {t : ℝ}
    {Φ : ℝ → State (Var 6)} (jx jy : Fin 6) (hF : LinkField Rv fR' jx jy 30)
    (H : ODESol (rightBlock fR' (Term.const 1)) domR x t Φ) (h : OpR x jx jy)
    (hx1 : Φ t (Rv jx) ≤ 60) (hy0 : -10 ≤ Φ t (Rv jy)) (hy1 : Φ t (Rv jy) ≤ 10) :
    OpR (Φ t) jx jy := by
  have k := link_guard_Ronly fR' domR jx jy 30 (by norm_num) (by norm_num) hF H h.1
    h.2.2.2.2.1 h.2.2.2.2.2
  exact ⟨k.1, hx1, hy0, hy1, k.2.1, k.2.2⟩

/-- **Assumption 1 at the latched AEB sinks `BRAKE1`–`BRAKE3`** (style (a), Z3-free). -/
theorem platoon3_linkloss_wellFormedR_brake (q : ℕ) (hq1 : 1 ≤ q) (hq : q < 4) :
    WellFormedRMode Gr guardR (epsR platoon3_linkloss_IRv2) q := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hbox := (sat_domR x).mp hd
  have hdom : ∀ z, BoxR z → Formula.sat domR z := fun z hz => (sat_domR z).mpr hz
  interval_cases q
  · obtain ⟨hb, h2, h3⟩ := (sat_guardB1 x).mp hg
    have hF := fR_bfield1
    have hB : BrakeField (fR 1) 0 1 := ⟨fun z => (hF z).1, fun z => by simpa [lF] using (hF z).2.1⟩
    have L2 : LinkField Rv (fR 1) 2 3 30 :=
      ⟨fun z => (hF z).2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.1⟩
    have L3 : LinkField Rv (fR 1) 4 5 30 :=
      ⟨fun z => (hF z).2.2.2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.2.2⟩
    refine ⟨⟨_, solB_sol true false false (fR 1) hF domR hdom x hbox
      (by simp; constructor <;> linarith [hb.2.1, hb.2.2])
      (by simp; constructor <;> linarith [h2.2.2.2.2.1, h2.2.2.2.2.2])
      (by simp; constructor <;> linarith [h3.2.2.2.2.1, h3.2.2.2.2.2]) 1 (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    obtain ⟨⟨_, _, _, _⟩, ⟨_, x3, y2, y3⟩, ⟨_, x5, y4, y5⟩⟩ := (sat_domR _).mp H.end_dom
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardB1 _).mpr
      ⟨brake_guard_Ronly (fR 1) domR 0 1 hB H hb, opR_end 2 3 L2 H h2 x3 y2 y3,
        opR_end 4 5 L3 H h3 x5 y4 y5⟩⟩
  · obtain ⟨hb, h1, h3⟩ := (sat_guardB2 x).mp hg
    have hF := fR_bfield2
    have hB : BrakeField (fR 2) 2 3 :=
      ⟨fun z => (hF z).2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.1⟩
    have L1 : LinkField Rv (fR 2) 0 1 30 :=
      ⟨fun z => (hF z).1, fun z => by simpa [lF] using (hF z).2.1⟩
    have L3 : LinkField Rv (fR 2) 4 5 30 :=
      ⟨fun z => (hF z).2.2.2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.2.2⟩
    refine ⟨⟨_, solB_sol false true false (fR 2) hF domR hdom x hbox
      (by simp; constructor <;> linarith [h1.2.2.2.2.1, h1.2.2.2.2.2])
      (by simp; constructor <;> linarith [hb.2.1, hb.2.2])
      (by simp; constructor <;> linarith [h3.2.2.2.2.1, h3.2.2.2.2.2]) 1 (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    obtain ⟨⟨_, x1, y0, y1⟩, ⟨_, _, _, _⟩, ⟨_, x5, y4, y5⟩⟩ := (sat_domR _).mp H.end_dom
    exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_guardB2 _).mpr
      ⟨brake_guard_Ronly (fR 2) domR 2 3 hB H hb, opR_end 0 1 L1 H h1 x1 y0 y1,
        opR_end 4 5 L3 H h3 x5 y4 y5⟩⟩
  · obtain ⟨hb, h1, h2⟩ := (sat_guardB3 x).mp hg
    have hF := fR_bfield3
    have hB : BrakeField (fR 3) 4 5 :=
      ⟨fun z => (hF z).2.2.2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.2.2⟩
    have L1 : LinkField Rv (fR 3) 0 1 30 :=
      ⟨fun z => (hF z).1, fun z => by simpa [lF] using (hF z).2.1⟩
    have L2 : LinkField Rv (fR 3) 2 3 30 :=
      ⟨fun z => (hF z).2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.1⟩
    refine ⟨⟨_, solB_sol false false true (fR 3) hF domR hdom x hbox
      (by simp; constructor <;> linarith [h1.2.2.2.2.1, h1.2.2.2.2.2])
      (by simp; constructor <;> linarith [h2.2.2.2.2.1, h2.2.2.2.2.2])
      (by simp; constructor <;> linarith [hb.2.1, hb.2.2]) 1 (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    obtain ⟨⟨_, x1, y0, y1⟩, ⟨_, x3, y2, y3⟩, ⟨_, _, _, _⟩⟩ := (sat_domR _).mp H.end_dom
    exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardB3 _).mpr
      ⟨brake_guard_Ronly (fR 3) domR 4 5 hB H hb, opR_end 0 1 L1 H h1 x1 y0 y1,
        opR_end 2 3 L2 H h2 x3 y2 y3⟩⟩

/-- **`platoon3_linkloss` satisfies Assumption 1** (every mode, Z3-free). -/
theorem platoon3_linkloss_wellFormedR :
    WellFormedR Gr guardR (epsR platoon3_linkloss_IRv2) := by
  intro q hq
  rw [Gr_len] at hq
  rcases (by omega : q = 0 ∨ 1 ≤ q) with rfl | h
  · exact platoon3_linkloss_wellFormedR_follow
  · exact platoon3_linkloss_wellFormedR_brake q h hq

end V2Platoon3Linkloss
end RelCertifier
