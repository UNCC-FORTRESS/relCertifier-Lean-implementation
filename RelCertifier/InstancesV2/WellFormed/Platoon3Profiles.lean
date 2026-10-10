/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_profiles`: Assumption 1 of the right model — PROVED (repaired model)

Over the instance's guarded right automaton `Gr` (the repaired model,
`docs/SUITE-REDESIGN.md` §20, §21), the lowered right guards, `ε_r = 1`.

**`WellFormedR` holds** (`platoon3_profiles_wellFormedR`, Z3-free), style (a) at every mode:

* `NORMAL`, `CLOSE`, `FAR` (`platoon3_profiles_wellFormedR_modes`): the operating range is
  forward invariant under the three damped links at set point 30, 28, 32
  (`Platoon3Link.link_guard_Ronly`, plus the evolve box every run keeps). Existence: the
  explicit link solution (`solΦ`, `link_bounds`).
* `BRAKE1`–`BRAKE3`, the LATCHED AEB sinks of the 2026-10-10 repair
  (`platoon3_profiles_wellFormedR_brake`): guard `g_k < 20`, `0 ≤ g_k + 2 r_k < 20`, the other
  two links in their operating range; flow `r_k' = −r_k/2` on the braking link, the damped
  links at 30 elsewhere. The braking link keeps its guard part
  (`Platoon3Link.brake_guard_Ronly`), the other links keep theirs (`link_guard_Ronly`).
  Existence: the explicit solution `Platoon3Link.solB_sol`.

(Until 2026-10-10 the sinks braked at a constant `4 m/s²` on the guard `g_k < 20` alone, and
the model was refuted here: from `g₁ = 19`, `r₁ = 0`, the other links at rest at 30, the run
of duration 1 ends at `g₁ = 21`, outside `BRAKE1`'s guard, its only declared successor.)
-/
import RelCertifier.InstancesV2.Modal.Platoon3Profiles
import RelCertifier.InstancesV2.WellFormed.Platoon3Link

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Platoon3Profiles

open DL DLCalTiming DLRel Parse Set Platoon3Link

theorem epsR_eq : epsR platoon3_profiles_IRv2 = 1 := by
  simp [epsR, platoon3_profiles_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vs 6 Side.R (mR q)

/-- One link's operating range. -/
def LinkOp (x : State (Var 6)) (jx jy : Fin 6) : Prop :=
  20 ≤ x (Rv jx) ∧ x (Rv jx) ≤ 60 ∧ -10 ≤ x (Rv jy) ∧ x (Rv jy) ≤ 10 ∧
    21 ≤ x (Rv jx) + 2 * x (Rv jy) ∧ x (Rv jx) + 2 * x (Rv jy) ≤ 59

theorem sat_guardR' (q : ℕ) (hq : q < 3) (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR q)) x ↔
      LinkOp x 0 1 ∧ LinkOp x 2 3 ∧ LinkOp x 4 5 := by
  constructor
  · intro h
    interval_cases q <;>
    · simp [hostGuard, mR, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, hn21_0, hn59_0,
        hpm100, hp100, hn2_0, hn20_0, hn58_0, hp600, vs,
        Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
        CompOp.interp, Term.eval, AOp.interp, Rv] at h
      simp only [LinkOp, Rv]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
        tauto
  · rintro ⟨h1, h2, h3⟩
    exact guardR_of q hq x h1 h2 h3

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 6)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- **Assumption 1 at `NORMAL`, `CLOSE`, `FAR`** (style (a), Z3-free). -/
theorem platoon3_profiles_wellFormedR_modes (q : ℕ) (hq : q < 3) :
    WellFormedRMode Gr guardR (epsR platoon3_profiles_IRv2) q := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  obtain ⟨h1, h2, h3⟩ := (sat_guardR' q hq x).mp hg
  have hbox := (sat_domR x).mp hd
  obtain ⟨L1, L2, L3⟩ := linkFields (fR_field q hq)
  have hc := cRc_lo q
  have hc' := cRc_hi q
  refine ⟨?_, ?_⟩
  · have hQ : QBounds (cRc q) ((cRc q - 21) / 2) x := by
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h3
      obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := hbox
      simp only [QBounds, LinkStart, Q2]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
        linarith
    refine ⟨solΦ (cRc q) x, ⟨by norm_num, solΦ_zero _ _,
      fun t _ => solΦ_deriv (cRc q) (fR q) (fR_field q hq) x 1 t, ?_, ?_⟩⟩
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
      exact solΦ_box (cRc q) ((cRc q - 21) / 2) (by linarith) (by linarith) (by linarith)
        (by linarith) _ hQ t ht.1
  · intro t Φ _ H
    have k1 := link_guard_Ronly (fR q) domR 0 1 (cRc q) (by linarith) (by linarith) L1 H
      h1.1 h1.2.2.2.2.1 h1.2.2.2.2.2
    have k2 := link_guard_Ronly (fR q) domR 2 3 (cRc q) (by linarith) (by linarith) L2 H
      h2.1 h2.2.2.2.2.1 h2.2.2.2.2.2
    have k3 := link_guard_Ronly (fR q) domR 4 5 (cRc q) (by linarith) (by linarith) L3 H
      h3.1 h3.2.2.2.2.1 h3.2.2.2.2.2
    obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := (sat_domR _).mp H.end_dom
    exact ⟨edgeW q q, edge_mem q q (by interval_cases q <;> decide), (sat_guardR' q hq _).mpr
      ⟨⟨k1.1, x1, y0, y1, k1.2.1, k1.2.2⟩, ⟨k2.1, x3, y2, y3, k2.2.1, k2.2.2⟩,
        ⟨k3.1, x5, y4, y5, k3.2.1, k3.2.2⟩⟩⟩

/-! ## The latched AEB sinks -/

theorem hpm05 : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem fR_bfield3 : BField3 (fR 3) true false false := by
  intro z
  simp [fR, hostDyn, mR, platoon3_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hpm0125, hp075,
    hp300, hpm05, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv, lF]
  refine ⟨by ring, by ring, by ring⟩

theorem fR_bfield4 : BField3 (fR 4) false true false := by
  intro z
  simp [fR, hostDyn, mR, platoon3_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hpm0125, hp075,
    hp300, hpm05, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv, lF]
  refine ⟨by ring, by ring, by ring⟩

theorem fR_bfield5 : BField3 (fR 5) false false true := by
  intro z
  simp [fR, hostDyn, mR, platoon3_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hpm0125, hp075,
    hp300, hpm05, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv, lF]
  refine ⟨by ring, by ring, by ring⟩

theorem sat_guardB3 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 3)) x ↔ BrkR x 0 1 ∧ OpR x 2 3 ∧ OpR x 4 5 := by
  simp only [BrkR, OpR, Rv]
  simp [hostGuard, mR, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, hn2_0, hn20_0, hp00,
    hn59_0, hpm100, hp100, hn21_0, hp600, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  constructor
  · intro h; refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      first | tauto | linarith [h]
  · intro h
    obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := h
    repeat' apply And.intro
    all_goals linarith

theorem sat_guardB4 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 4)) x ↔ BrkR x 2 3 ∧ OpR x 0 1 ∧ OpR x 4 5 := by
  simp only [BrkR, OpR, Rv]
  simp [hostGuard, mR, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, hn2_0, hn20_0, hp00,
    hn59_0, hpm100, hp100, hn21_0, hp600, vs, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv]
  constructor
  · intro h; refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      first | tauto | linarith [h]
  · intro h
    obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := h
    repeat' apply And.intro
    all_goals linarith

theorem sat_guardB5 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 5)) x ↔ BrkR x 4 5 ∧ OpR x 0 1 ∧ OpR x 2 3 := by
  simp only [BrkR, OpR, Rv]
  simp [hostGuard, mR, platoon3_profiles_IRv2, Run.lowerF, Run.lowerE, hn2_0, hn20_0, hp00,
    hn59_0, hpm100, hp100, hn21_0, hp600, vs, Run.resolveVar, List.findIdx?_cons,
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
theorem platoon3_profiles_wellFormedR_brake (q : ℕ) (hq1 : 3 ≤ q) (hq : q < 6) :
    WellFormedRMode Gr guardR (epsR platoon3_profiles_IRv2) q := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hbox := (sat_domR x).mp hd
  have hdom : ∀ z, BoxR z → Formula.sat domR z := fun z hz => (sat_domR z).mpr hz
  interval_cases q
  · obtain ⟨hb, h2, h3⟩ := (sat_guardB3 x).mp hg
    have hF := fR_bfield3
    have hB : BrakeField (fR 3) 0 1 := ⟨fun z => (hF z).1, fun z => by simpa [lF] using (hF z).2.1⟩
    have L2 : LinkField Rv (fR 3) 2 3 30 :=
      ⟨fun z => (hF z).2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.1⟩
    have L3 : LinkField Rv (fR 3) 4 5 30 :=
      ⟨fun z => (hF z).2.2.2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.2.2⟩
    refine ⟨⟨_, solB_sol true false false (fR 3) hF domR hdom x hbox
      (by simp; constructor <;> linarith [hb.2.1, hb.2.2])
      (by simp; constructor <;> linarith [h2.2.2.2.2.1, h2.2.2.2.2.2])
      (by simp; constructor <;> linarith [h3.2.2.2.2.1, h3.2.2.2.2.2]) 1 (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    obtain ⟨⟨_, _, _, _⟩, ⟨_, x3, y2, y3⟩, ⟨_, x5, y4, y5⟩⟩ := (sat_domR _).mp H.end_dom
    exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardB3 _).mpr
      ⟨brake_guard_Ronly (fR 3) domR 0 1 hB H hb, opR_end 2 3 L2 H h2 x3 y2 y3,
        opR_end 4 5 L3 H h3 x5 y4 y5⟩⟩
  · obtain ⟨hb, h1, h3⟩ := (sat_guardB4 x).mp hg
    have hF := fR_bfield4
    have hB : BrakeField (fR 4) 2 3 :=
      ⟨fun z => (hF z).2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.1⟩
    have L1 : LinkField Rv (fR 4) 0 1 30 :=
      ⟨fun z => (hF z).1, fun z => by simpa [lF] using (hF z).2.1⟩
    have L3 : LinkField Rv (fR 4) 4 5 30 :=
      ⟨fun z => (hF z).2.2.2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.2.2⟩
    refine ⟨⟨_, solB_sol false true false (fR 4) hF domR hdom x hbox
      (by simp; constructor <;> linarith [h1.2.2.2.2.1, h1.2.2.2.2.2])
      (by simp; constructor <;> linarith [hb.2.1, hb.2.2])
      (by simp; constructor <;> linarith [h3.2.2.2.2.1, h3.2.2.2.2.2]) 1 (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    obtain ⟨⟨_, x1, y0, y1⟩, ⟨_, _, _, _⟩, ⟨_, x5, y4, y5⟩⟩ := (sat_domR _).mp H.end_dom
    exact ⟨edgeW 4 4, edge_mem 4 4 (by decide), (sat_guardB4 _).mpr
      ⟨brake_guard_Ronly (fR 4) domR 2 3 hB H hb, opR_end 0 1 L1 H h1 x1 y0 y1,
        opR_end 4 5 L3 H h3 x5 y4 y5⟩⟩
  · obtain ⟨hb, h1, h2⟩ := (sat_guardB5 x).mp hg
    have hF := fR_bfield5
    have hB : BrakeField (fR 5) 4 5 :=
      ⟨fun z => (hF z).2.2.2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.2.2⟩
    have L1 : LinkField Rv (fR 5) 0 1 30 :=
      ⟨fun z => (hF z).1, fun z => by simpa [lF] using (hF z).2.1⟩
    have L2 : LinkField Rv (fR 5) 2 3 30 :=
      ⟨fun z => (hF z).2.2.1, fun z => by simpa [lF] using (hF z).2.2.2.1⟩
    refine ⟨⟨_, solB_sol false false true (fR 5) hF domR hdom x hbox
      (by simp; constructor <;> linarith [h1.2.2.2.2.1, h1.2.2.2.2.2])
      (by simp; constructor <;> linarith [h2.2.2.2.2.1, h2.2.2.2.2.2])
      (by simp; constructor <;> linarith [hb.2.1, hb.2.2]) 1 (by norm_num)⟩, ?_⟩
    intro t Φ _ H
    obtain ⟨⟨_, x1, y0, y1⟩, ⟨_, x3, y2, y3⟩, ⟨_, _, _, _⟩⟩ := (sat_domR _).mp H.end_dom
    exact ⟨edgeW 5 5, edge_mem 5 5 (by decide), (sat_guardB5 _).mpr
      ⟨brake_guard_Ronly (fR 5) domR 4 5 hB H hb, opR_end 0 1 L1 H h1 x1 y0 y1,
        opR_end 2 3 L2 H h2 x3 y2 y3⟩⟩

/-- **`platoon3_profiles` satisfies Assumption 1** (every mode, Z3-free). -/
theorem platoon3_profiles_wellFormedR :
    WellFormedR Gr guardR (epsR platoon3_profiles_IRv2) := by
  intro q hq
  have hq6 : q < 6 := by simpa [Gr] using hq
  rcases (by omega : q < 3 ∨ 3 ≤ q) with h | h
  · exact platoon3_profiles_wellFormedR_modes q h
  · exact platoon3_profiles_wellFormedR_brake q h hq6

end V2Platoon3Profiles
end RelCertifier
