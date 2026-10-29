/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_latency`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the
file's single right mode `CACC` and its declared `next` list `[CACC]`), the lowered right
guards, and `ε_r = 0.1` read from the file.

The right model is the CACC design follower of the platoon link: gap `g` (coordinate 0),
range rate `r` (coordinate 1), and the latency state `e` (coordinate 2), which the right
declares with `e' = 0`; evolve box `0 ≤ g ≤ 60`, `|r| ≤ 10`, `|e| ≤ 20`. The runs are the
shared `(g, r)` link runs over the `(g, r)` box `domGR`; `e` is frozen along them, so they stay
in the full box (`sol_domR`).
* `CACC` (`g' = r`, `r' = −0.125 (g − 20) − 0.75 r`; guard `|r| ≤ 10`, `5 ≤ g + 2r ≤ 60`).
  (i) The explicit two-exponential solution stays in the box for all time
  (`PlatoonCaccAeb.cacc_exists`). (ii) Style (a), the self-loop (the only declared edge):
  the projected stop gap `w = g + 2r` obeys `w' = −(1/4)(w − 20)`, so `[5, 60]` is kept
  (`cacc_w_band`), and `|r| ≤ 10` is the evolve box at the run's end.
Z3-free; modelled on `TankDos3to1.lean` (layout) and `AccSpoofLag.lean` (modal coordinates);
the run lemmas are the shared `WellFormed/PlatoonCaccAeb.lean`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.platoon_latency
import RelCertifier.InstancesV2.WellFormed.PlatoonCaccAeb

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2PlatoonLatency

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["g", "r", "e"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := platoon_latency_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp0125m : Run.parseRat "-0.125" = some (-(1:ℚ)/8) := by
  have h : parseQ "-0.125" = some (⟨-125, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp075 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp600 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm100 : Run.parseRat "-10.0" = some (-10 : ℚ) := by
  have h : parseQ "-10.0" = some (⟨-100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp100 : Run.parseRat "10.0" = some (10 : ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp0 : Run.parseRat "0" = some (0 : ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hpm200 : Run.parseRat "-20.0" = some (-20 : ℚ) := by
  have h : parseQ "-20.0" = some (⟨-200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## The lowered right fields, domain and guards -/

/-- `CACC`: `g' = r`, `r' = −0.125 (g − 20) − 0.75 r`, coordinate 2 frozen. -/
theorem fR_cacc : PlatoonCaccAeb.CaccField (fR 0) 0 1 := by
  refine ⟨fun z => ?_, fun z => ?_, fun i h0 h1 z => ?_⟩
  · simp [fR, hostDyn, mR, platoon_latency_IRv2, vs, Run.dynOf, Run.lowerE, hp0125m, hp200, hp075,
      hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]
  · simp [fR, hostDyn, mR, platoon_latency_IRv2, vs, Run.dynOf, Run.lowerE, hp0125m, hp200, hp075,
      hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
      Rv]
    ring
  · fin_cases i
    · exact absurd rfl h0
    · exact absurd rfl h1
    · simp [fR, hostDyn, mR, platoon_latency_IRv2, vs, Run.dynOf, Run.lowerE, hp0125m, hp200, hp075,
        hp0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
        AOp.interp, Rv]

/-- The evolve domain: the box `0 ≤ g ≤ 60`, `|r| ≤ 10`, and `|e| ≤ 20`. -/
theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ PlatoonCaccAeb.Box x 0 1 ∧ (-20 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 20) := by
  simp only [domR, hostEvolve, mR, platoon_latency_IRv2, vs, PlatoonCaccAeb.Box]
  simp [Run.lowerF, Run.lowerE, hp00, hp600, hpm100, hp100, hpm200, hp200, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  tauto

/-- The `(g, r)` part of the evolve box, lowered from its literal: the domain in which the
shared link runs of `PlatoonCaccAeb` are built (`e` is not mentioned). -/
noncomputable def domGR : Formula (Var 3) :=
  hostEvolve vs 3 Side.R ⟨"", [], .tt,
    (.and (.and (.and (.cmp ">=" (.var "g") (.num "0.0")) (.cmp "<=" (.var "g") (.num "60.0")))
      (.cmp ">=" (.var "r") (.num "-10.0"))) (.cmp "<=" (.var "r") (.num "10.0"))), []⟩

theorem sat_domGR (x : State (Var 3)) : Formula.sat domGR x ↔ PlatoonCaccAeb.Box x 0 1 := by
  simp only [domGR, hostEvolve, vs, PlatoonCaccAeb.Box]
  simp [Run.lowerF, Run.lowerE, hp00, hp600, hpm100, hp100, Run.resolveVar,
    List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]
  tauto

/-- **The frozen `e` keeps its box**: a `(g, r)`-box run of a field whose coordinate 2
vanishes is a run over the full evolve domain from every state of that domain. -/
theorem sol_domR {f : Fin 3 → Term (Var 3)} (h2 : ∀ z, Term.eval (f 2) z = 0)
    {x : State (Var 3)} (hx : Formula.sat domR x) {τ : ℝ} {Φ : ℝ → State (Var 3)}
    (H : ODESol (rightBlock f (Term.const 1)) domGR x τ Φ) :
    ODESol (rightBlock f (Term.const 1)) domR x τ Φ := by
  refine ⟨H.hr, H.hΦ0, H.hder, H.hmask, fun t ht => ?_⟩
  have he : Φ t (Rv 2) = x (Rv 2) :=
    (H.restrict ht.1 ht.2).const (rightBlock_mem' f (Term.const 1) 2)
      (fun s _ => by rw [eval_unit_mul, h2])
  have hxe := ((sat_domR x).mp hx).2
  exact (sat_domR _).mpr ⟨(sat_domGR _).mp (H.hdom t ht), by rw [he]; exact hxe⟩

/-- `CACC`'s guard: `|r| ≤ 10`, `5 ≤ g + 2r ≤ 60`. -/
theorem sat_guardR0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (-10 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 10) ∧
      (5 ≤ ν (Rv 0) + 2 * ν (Rv 1) ∧ ν (Rv 0) + 2 * ν (Rv 1) ≤ 60) := by
  simp [hostGuard, mR, platoon_latency_IRv2, Run.lowerF, Run.lowerE, hpm100, hp100, hp20, hp50,
    hp600, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv]
  tauto

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (CACC 0). -/
def edgeList : List (ℕ × ℕ) := [(0, 0)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 1) : Gr.modeAt q = some (modeW q) := by
  interval_cases q; rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 1 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 1 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR platoon_latency_IRv2 = 1/10 := by
  simp [epsR, platoon_latency_IRv2, hp01]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem domGR_of_box (z : State (Var 3)) (h : PlatoonCaccAeb.Box z 0 1) :
    Formula.sat domGR z :=
  (sat_domGR z).mpr h

/-- **Assumption 1 for `platoon_latency`**, every mode, Z3-free. -/
theorem platoon_latency_wellFormedR : WellFormedR Gr guardR (epsR platoon_latency_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq1, rfl⟩ := Gr_modeAt_inv hm
  have hdx : PlatoonCaccAeb.Box x 0 1 := ((sat_domR x).mp hd).1
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  interval_cases q
  · -- CACC: existence from the explicit solution; the self-loop keeps the guard
    have hgx := (sat_guardR0 x).mp hg
    obtain ⟨Φ, HΦ⟩ := PlatoonCaccAeb.cacc_exists h01 fR_cacc domGR_of_box x hdx
      (by linarith [hgx.2.1]) hgx.2.2 (1/10) (by norm_num)
    refine ⟨⟨Φ, sol_domR (fR_cacc.2.2 2 (by decide) (by decide)) hd HΦ⟩, ?_⟩
    intro t Φ _ H
    have H' : ODESol (rightBlock (fR 0) (Term.const 1)) domR x t Φ := H
    have hw := PlatoonCaccAeb.cacc_w_band fR_cacc H' 5 60 (by norm_num) (by norm_num)
      hgx.2.1 hgx.2.2
    have he := (sat_domR _).mp H'.end_dom
    exact ⟨edgeW 0 0, edge_mem 0 0 (by decide),
      (sat_guardR0 _).mpr ⟨⟨he.1.2.2.1, he.1.2.2.2⟩, hw⟩⟩

end V2PlatoonLatency
end RelCertifier

