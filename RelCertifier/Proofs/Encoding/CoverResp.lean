/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# From an extended cover to the window response (the proof of Theorem 3, generically)

`coverX_piece` is the induction of Theorem 3's proof: from a configuration covered by
`CoveredX` (Definition 4 with chosen successors and hops, `Checker/CoverX.lean`), the right
answers one clocked left piece of duration `r` with a chain of declared, guard-legal segments,
provided the piece fits the budget (`r − a ≤ B · δ`, `δ` the common segment span). Per case:

* **base**: the joint segment of `q` runs to the piece's end (its right duration `λ_q (r − a)
  ≤ λ_q δ ≤ ε_R`, so Assumption 1 gives the run and, at its end, an enabled declared
  successor); the anchor is preserved by the pairing's flow certificate (`hbox`, Theorem 1);
* **step**: the joint segment runs its span `δ`; Assumption 1 gives an enabled declared
  successor at its end, the non-connection certificate (`hprune`, Theorem 2) excludes the
  pruned ones, so the successor is retained and covered at budget `B − 1`;
* **chosen successors**: as step, but the successor comes from the coverage certificate: the
  end state satisfies the region `RJ q` (the anchor implies it), hence some chosen guard;
* **right-only step**: the right runs alone (left frozen) until a retained exit is enabled
  (`hrepoProg`, the reposition-progress premise; Assumption 1 alone does not provide an exit),
  the anchor preserved by the reposition certificate (`hboxD`);
* **chosen exits / hop**: a zero-duration run of `q`; the start state satisfies the region
  (`RR`/`RS`), so a chosen guard holds and the switch is legal.

Every switch enters its target's guard (`SwitchLegal`), and the entered mode's anchor holds
by the entry condition (`hhand`: the anchor of `q` and the guard of `q'` give the anchor of
`q'`). `coverX_gresp` lifts the piece response to the guarded step obligation `GResp` of the
gated one-piece window, the shape the outer loop rule consumes.
-/
import RelCertifier.Proofs.Encoding.ReplayEngineQ
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Checker.CoverX

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-- A right-only formula holds at a merged state iff at its right part. -/
theorem sat_merge_R {φ : Formula (Var n)} (hφ : φ.fv ⊆ range Rv) (ω₀ y ρ : State (Var n)) :
    Formula.sat φ (mergeLR ω₀ y ρ) ↔ Formula.sat φ ρ := by
  refine Formula.coincidence φ (fun v hv => ?_)
  obtain ⟨j, rfl⟩ := hφ hv
  exact mergeLR_R ω₀ _ _ j

/-- A left-only formula holds at a merged state iff at its left part. -/
theorem sat_merge_L {φ : Formula (Var n)} (hφ : φ.fv ⊆ range Lv) (ω₀ y ρ : State (Var n)) :
    Formula.sat φ (mergeLR ω₀ y ρ) ↔ Formula.sat φ y := by
  refine Formula.coincidence φ (fun v hv => ?_)
  obtain ⟨j, rfl⟩ := hφ hv
  exact mergeLR_L ω₀ _ _ j

theorem modeAt_lt {G : SearchGraph (Var n)} {q : ℕ} {m : RMode (Var n)}
    (hm : G.modeAt q = some m) : q < G.modes.length := by
  unfold SearchGraph.modeAt at hm
  exact (List.getElem?_eq_some_iff.mp hm).1

theorem exitSucc_edge {G : SearchGraph (Var n)} {q q' : ℕ} (h : q' ∈ G.exitSucc q) :
    ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.pruned = false := by
  unfold SearchGraph.exitSucc at h
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  rw [List.mem_filter] at he
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at he
  exact ⟨e, List.mem_filter.mpr ⟨he.1, by simp [he.2.1.1]⟩, rfl, he.2.1.2⟩

theorem declSucc_edge {G : SearchGraph (Var n)} {q q' : ℕ} (h : q' ∈ G.declSucc q) :
    ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.pruned = false := by
  unfold SearchGraph.declSucc at h
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  rw [List.mem_filter] at he
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at he
  exact ⟨e, List.mem_filter.mpr ⟨he.1, by simp [he.2.1]⟩, rfl, he.2.2⟩

theorem mem_retainedSucc_of_edge {G : SearchGraph (Var n)} {q : ℕ} {e : REdge (Var n)}
    (he : e ∈ G.edgesFrom q) (hp : e.pruned = false) : e.tgt ∈ G.retainedSucc q := by
  unfold SearchGraph.retainedSucc
  refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, ?_, rfl⟩)
  unfold SearchGraph.edgesFrom at he
  rw [List.mem_filter] at he ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at he ⊢
  exact ⟨he.1, he.2, hp⟩

theorem mem_exitSucc_of_edge {G : SearchGraph (Var n)} {q : ℕ} {e : REdge (Var n)}
    (he : e ∈ G.edgesFrom q) (hp : e.pruned = false) (hne : e.tgt ≠ q) :
    e.tgt ∈ G.exitSucc q := by
  unfold SearchGraph.exitSucc
  refine List.mem_map.mpr ⟨e, ?_, rfl⟩
  unfold SearchGraph.edgesFrom at he
  rw [List.mem_filter] at he ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at he ⊢
  exact ⟨he.1, ⟨he.2, hp⟩, hne⟩

/-- **Reposition progress** at `q` (setting `pre`): from a start whose merged state `y` carries
the anchor (and the left guard, pre-joint) and whose right part `ρ` is in `q`'s guard, the right
runs declared segments of `q` (self-loops, each a right cycle) to a state where some non-self,
non-pruned successor is enabled, the anchor kept and the left untouched. Discharged per node
from the progress certificate (`Proofs/Encoding/Progress.lean`) or from an explicit solution. -/
def RepoProgress (G : SearchGraph (Var n)) (A : ℕ → Formula (Var n)) (gL guardq : Formula (Var n))
    (q : ℕ) (pre : Bool) : Prop :=
  ∀ ρ y : State (Var n), (∀ i, y (Rv i) = ρ (Rv i)) → Formula.sat (A q) y →
    Formula.sat guardq ρ → (pre = true → Formula.sat gL y) →
    RRespP G q (fun q' μ => q' = q ∧ Formula.sat (A q) (mergeLR y y μ) ∧
      (∀ i, μ (Lv i) = ρ (Lv i)) ∧
      ∃ e ∈ G.edgesFrom q, SwitchLegal e μ ∧ e.tgt ≠ q ∧ e.pruned = false) ρ

section Piece

variable (G : SearchGraph (Var n)) (ch : ChoiceData)
  (fR : ℕ → Fin n → Term (Var n)) (domR : Formula (Var n)) (fL : Fin n → Term (Var n))
  (domL gL : Formula (Var n)) (tg : Var n) (guard : ℕ → Formula (Var n))
  (hgR : GuardsRight G) (hguards : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = guard e.tgt)
  (hguardR : ∀ q, (guard q).fv ⊆ range Rv)
  (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
  (hgL : gL.fv ⊆ range Lv) (hfR : ∀ q, q < G.modes.length → ∀ i, (fR q i).fv ⊆ range Rv)
  (hsys : ∀ q m, G.modeAt q = some m → m.sys = rightBlock (fR q) (Term.const 1))
  (hdomM : ∀ q m, G.modeAt q = some m → m.dom = domR)
  (hweight : ∀ q m, G.modeAt q = some m → m.weight = 1)
  -- the time model: the common segment span `δ`, the right interval `ε_R`, the stretches
  (epsR δ : ℝ) (hδ : 0 < δ) (lam : ℕ → ℝ) (hlam : ∀ q, 0 < lam q)
  (hspan : ∀ q, lam q * δ ≤ epsR)
  -- the anchors (the pairing's row, both sides' kept atoms, the envelope)
  (A : ℕ → Formula (Var n)) (hAfv : ∀ q, (A q).fv ⊆ range Lv ∪ range Rv)
  (hAdom : ∀ q y, Formula.sat (A q) y → Formula.sat domR y)
  -- Theorem 1 at each pairing (the joint flow at the pairing's stretch keeps the anchor)
  (hbox : ∀ q m, G.modeAt q = some m → ch.jointOK q = true → ∀ σ ω, Formula.sat (A q) σ →
    Program.sem (Program.ode (jointSys fL (fR q) (Term.const (lam q))) (Formula.and domL domR))
      σ ω → Formula.sat (A q) ω)
  -- entry: the anchor of `q` and the guard of the entered mode give its anchor
  (hhand : ∀ q, ∀ e ∈ G.edgesFrom q, ∀ y, Formula.sat (A q) y → SwitchLegal e y →
    Formula.sat (A e.tgt) y)
  -- Assumption 1 (the right model is well formed)
  (hwf : WellFormedR G guard epsR)
  -- Theorem 2: pruned edges are never enabled after the segment (joint and right-only kinds)
  (hprune : ∀ q m, G.modeAt q = some m → ∀ e ∈ G.edgesFrom q, e.pruned = true →
    ∀ σ ω, Formula.sat (A q) σ →
    Program.sem (Program.ode (jointSys fL (fR q) (Term.const (lam q))) (Formula.and domL domR))
      σ ω → ¬ Formula.sat e.guard ω)
  -- reposition progress (`RepoProgress`): a reposition node's right-only cycles reach an exit
  (hrepoProg : ∀ q m, G.modeAt q = some m → ∀ pre : Bool,
    (if pre then ch.repoPre q else ch.repoPost q) = true →
    RepoProgress G A gL (guard q) q pre)
  -- the coverage certificates, as regions implied by the anchor and sets they cover
  (RJ : ℕ → Formula (Var n)) (hRJ : ∀ q y, Formula.sat (A q) y → Formula.sat (RJ q) y)
  (hcovJ : ∀ q S, S ∈ ch.jointS q → ∀ y, Formula.sat (RJ q) y → ∃ q' ∈ S, Formula.sat (guard q') y)
  (RR : ℕ → SrcSetting → Formula (Var n))
  (hRR : ∀ q σ y, Formula.sat (A q) y → (σ = SrcSetting.preJ → Formula.sat gL y) →
    Formula.sat (RR q σ) y)
  (hcovR : ∀ q σ S, S ∈ ch.repoS q σ → ∀ y, Formula.sat (RR q σ) y →
    ∃ q' ∈ S, Formula.sat (guard q') y)
  (RS : ℕ → SrcSetting → Formula (Var n))
  (hRS : ∀ q σ y, Formula.sat (A q) y → Formula.sat (guard q) y →
    (σ = SrcSetting.preJ → Formula.sat gL y) → Formula.sat (RS q σ) y)
  (hcovS : ∀ q σ S, S ∈ ch.hopS q σ → ∀ y, Formula.sat (RS q σ) y →
    ∃ q' ∈ S, Formula.sat (guard q') y)

include hgR hguards hfL hdomL hdomR hfR hsys hdomM hlam hspan hAdom hbox hhand hwf in
/-- **The closing joint segment.** From a joint node whose segment covers the rest of the piece
(`r − a ≤ δ`), the right runs to the piece's end and switches into an enabled successor. -/
theorem coverX_finish {x : State (Var n)} {r : ℝ} {ΦL : ℝ → State (Var n)}
    (hL : ODESol (clk tg (leftBlock fL)) domL x r ΦL) (ω₀ : State (Var n))
    {q : ℕ} {m : RMode (Var n)} (hm : G.modeAt q = some m) (hj : ch.jointOK q = true)
    {a : ℝ} (ha : 0 ≤ a) (har : a ≤ r) (hfit : r - a ≤ δ) {ρ : State (Var n)}
    (hPre : Formula.sat (guard q) ρ) (hA : Formula.sat (A q) (mergeLR ω₀ (ΦL a) ρ)) :
    RRespP G q (fun q' μ => Formula.sat (guard q') μ ∧
      Formula.sat (A q') (mergeLR ω₀ (ΦL r) μ) ∧ ∀ i, μ (Lv i) = ρ (Lv i)) ρ := by
  have hlq := hlam q
  have hρdom : Formula.sat domR ρ := (sat_merge_R hdomR ω₀ (ΦL a) ρ).mp (hAdom q _ hA)
  have hmdom : Formula.sat m.dom ρ := by rw [hdomM q m hm]; exact hρdom
  obtain ⟨⟨Φ, hΦ⟩, hcomp⟩ := hwf q (modeAt_lt hm) m hm ρ hPre hmdom trivial
  set T := lam q * (r - a) with hT
  have hT0 : 0 ≤ T := mul_nonneg hlq.le (by linarith)
  have hTε : T ≤ epsR := le_trans (mul_le_mul_of_nonneg_left hfit hlq.le) (hspan q)
  have hΦT : ODESol m.sys m.dom ρ T Φ := ODESol_restrict hΦ hT0 hTε
  have hΦ' : ODESol (rightBlock (fR q) (Term.const 1)) domR ρ T Φ := by
    rw [← hsys q m hm, ← hdomM q m hm]; exact hΦT
  have hAend := joint_stretch tg (lam q) hlq hfL (hfR q (modeAt_lt hm)) hdomL hdomR hL ω₀ (A q)
    (hbox q m hm hj) ha har le_rfl hΦ' hA
  obtain ⟨e, he, hge⟩ := hcomp T Φ hTε hΦT
  have hleg : SwitchLegal e (Φ T) := by unfold SwitchLegal; rw [hguards q e he]; exact hge
  refine rrespP_step hm he (DLCalTiming.sem_ode_restrict hΦT hT0 le_rfl) hleg
    (rrespP_stop ⟨hge, ?_, fun i => right_sol_left hΦ' i⟩)
  exact hhand q e he _ hAend ((switchLegal_merge hgR he ω₀ (ΦL r)).mpr hleg)

include hgR hguards hguardR hfL hdomL hdomR hgL hfR hsys hdomM hAfv hAdom hhand hrepoProg in
/-- **The right-only step.** From a reposition node, the right cycles in `q` until a non-self
retained exit is enabled (`RepoProgress`), switches into it (the entered anchor by entry), and
continues from the exit's covered configuration. -/
theorem repoStep {x : State (Var n)} {r : ℝ} {ΦL : ℝ → State (Var n)}
    (hL : ODESol (clk tg (leftBlock fL)) domL x r ΦL) (ω₀ : State (Var n))
    (hx : Formula.sat gL (ΦL 0))
    {q : ℕ} {m : RMode (Var n)} (hm : G.modeAt q = some m) (pre : Bool)
    (hflag : (if pre then ch.repoPre q else ch.repoPost q) = true)
    {a : ℝ} (ha : 0 ≤ a) (har : a ≤ r) (hpre : pre = true → a = 0)
    {ρ : State (Var n)} (hPre : Formula.sat (guard q) ρ)
    (hA : Formula.sat (A q) (mergeLR ω₀ (ΦL a) ρ))
    (hrest : ∀ q' ∈ G.exitSucc q, ∀ ρ', Formula.sat (guard q') ρ' →
      Formula.sat (A q') (mergeLR ω₀ (ΦL a) ρ') →
      RRespP G q' (fun q'' μ => Formula.sat (guard q'') μ ∧
        Formula.sat (A q'') (mergeLR ω₀ (ΦL r) μ) ∧ ∀ i, μ (Lv i) = ρ' (Lv i)) ρ') :
    RRespP G q (fun q' μ => Formula.sat (guard q') μ ∧
      Formula.sat (A q') (mergeLR ω₀ (ΦL r) μ) ∧ ∀ i, μ (Lv i) = ρ (Lv i)) ρ := by
  set y := mergeLR ω₀ (ΦL a) ρ with hy
  have hgLy : pre = true → Formula.sat gL y := by
    intro hp
    rw [hy, hpre hp]
    exact (sat_merge_L hgL ω₀ _ ρ).mpr hx
  have hchain := hrepoProg q m hm pre hflag ρ y (fun i => by rw [hy, mergeLR_R]) hA hPre hgLy
  refine rrespP_bind' hchain ?_
  rintro q' μ ⟨rfl, hAμ, hμL, e, he, hleg, hneq, hnp⟩
  have hAm : Formula.sat (A q') (mergeLR ω₀ (ΦL a) μ) := by
    refine (sat_of_agree (hAfv q') (y := mergeLR y y μ) (fun i => ?_) (fun i => ?_)).mpr hAμ
    · rw [mergeLR_L, mergeLR_L, hy, mergeLR_L]
    · rw [mergeLR_R, mergeLR_R]
  have hlegm : SwitchLegal e (mergeLR ω₀ (ΦL a) μ) :=
    (switchLegal_merge hgR he ω₀ (ΦL a)).mpr hleg
  have hAe := hhand q' e he _ hAm hlegm
  have hexit : e.tgt ∈ G.exitSucc q' := mem_exitSucc_of_edge he hnp hneq
  have hμdom : Formula.sat m.dom μ := by
    rw [hdomM q' m hm]
    exact (sat_merge_R hdomR ω₀ (ΦL a) μ).mp (hAdom q' _ hAm)
  have hge : Formula.sat (guard e.tgt) μ := by
    unfold SwitchLegal at hleg; rwa [hguards q' e he] at hleg
  refine rrespP_step hm he (sem_ode_zero m.sys m.dom hμdom) hleg
    (rrespP_mono ?_ (hrest e.tgt hexit μ hge hAe))
  rintro q'' μ' ⟨h1, h2, hμ'L⟩
  exact ⟨h1, h2, fun i => (hμ'L i).trans (hμL i)⟩

include hgR hguards hguardR hfL hdomL hdomR hgL hfR hsys hdomM hweight hδ hlam hspan hAfv hAdom
  hbox hhand hwf hprune hrepoProg hRJ hcovJ hRR hcovR hRS hcovS in
/-- **The induction of Theorem 3's proof.** A covered configuration answers one clocked left
piece from left time `a`, if the rest of the piece fits the budget. -/
theorem coverX_piece {x : State (Var n)} {r : ℝ} {ΦL : ℝ → State (Var n)}
    (hL : ODESol (clk tg (leftBlock fL)) domL x r ΦL) (ω₀ : State (Var n))
    (hx : Formula.sat gL (ΦL 0)) :
    ∀ cfg, CoveredX G ch cfg → ∀ a, 0 ≤ a → a ≤ r → r - a ≤ (cfg.B : ℝ) * δ →
      (cfg.σ = SrcSetting.preJ → a = 0) →
      ∀ ρ, Formula.sat (guard cfg.q) ρ → Formula.sat (A cfg.q) (mergeLR ω₀ (ΦL a) ρ) →
      RRespP G cfg.q (fun q' μ => Formula.sat (guard q') μ ∧
        Formula.sat (A q') (mergeLR ω₀ (ΦL r) μ) ∧ ∀ i, μ (Lv i) = ρ (Lv i)) ρ := by
  intro cfg hcov
  induction hcov with
  | @base q B σ m hm hj hle =>
      intro a ha har hbud _ ρ hPre hA
      have hw := hweight q m hm
      have hfit : r - a ≤ δ := by
        rw [hw] at hle
        have : (B : ℝ) ≤ 1 := by exact_mod_cast hle
        calc r - a ≤ (B : ℝ) * δ := hbud
          _ ≤ 1 * δ := mul_le_mul_of_nonneg_right this hδ.le
          _ = δ := one_mul δ
      exact coverX_finish G ch fR domR fL domL tg guard hgR hguards hfL hdomL hdomR hfR
        hsys hdomM epsR δ lam hlam hspan A hAdom hbox hhand hwf hL ω₀ hm hj ha har hfit hPre hA
  | @step q B σ m hm hj hlt _ ih =>
      intro a ha har hbud _ ρ hPre hA
      have hw := hweight q m hm
      rw [hw] at hlt ih
      by_cases hfit : r - a ≤ δ
      · exact coverX_finish G ch fR domR fL domL tg guard hgR hguards hfL hdomL hdomR hfR
          hsys hdomM epsR δ lam hlam hspan A hAdom hbox hhand hwf hL ω₀ hm hj ha har hfit hPre hA
      · push Not at hfit
        -- run the segment's span `δ`
        have hlq := hlam q
        set b := a + δ with hbdef
        have hab : a ≤ b := by linarith
        have hbr : b ≤ r := by linarith
        have hρdom : Formula.sat domR ρ := (sat_merge_R hdomR ω₀ (ΦL a) ρ).mp (hAdom q _ hA)
        have hmdom : Formula.sat m.dom ρ := by rw [hdomM q m hm]; exact hρdom
        obtain ⟨⟨Φ, hΦ⟩, hcomp⟩ := hwf q (modeAt_lt hm) m hm ρ hPre hmdom trivial
        set T := lam q * (b - a) with hT
        have hTδ : T = lam q * δ := by rw [hT, hbdef]; ring
        have hT0 : 0 ≤ T := by rw [hTδ]; exact mul_nonneg hlq.le hδ.le
        have hTε : T ≤ epsR := by rw [hTδ]; exact hspan q
        have hΦT : ODESol m.sys m.dom ρ T Φ := ODESol_restrict hΦ hT0 hTε
        have hΦ' : ODESol (rightBlock (fR q) (Term.const 1)) domR ρ T Φ := by
          rw [← hsys q m hm, ← hdomM q m hm]; exact hΦT
        -- the joint run and the anchor at the segment's end
        have hLs := odeSol_shift hL ha hab hbr
        have hj' := joint_of_sols_lam tg (lam q) hlq hfL (hfR q (modeAt_lt hm)) hdomL hdomR hLs hΦ' ω₀
        simp only [add_zero, add_sub_cancel, hΦ'.hΦ0] at hj'
        have hAb : Formula.sat (A q) (mergeLR ω₀ (ΦL b) (Φ T)) := hbox q m hm hj _ _ hA hj'
        -- an enabled declared successor, not pruned
        obtain ⟨e, he, hge⟩ := hcomp T Φ hTε hΦT
        have hleg : SwitchLegal e (Φ T) := by unfold SwitchLegal; rw [hguards q e he]; exact hge
        have hlegm : SwitchLegal e (mergeLR ω₀ (ΦL b) (Φ T)) :=
          (switchLegal_merge hgR he ω₀ (ΦL b)).mpr hleg
        have hnp : e.pruned = false := by
          by_contra hc
          have hp : e.pruned = true := by simpa using hc
          exact hprune q m hm e he hp _ _ hA hj' hlegm
        have hret : e.tgt ∈ G.retainedSucc q := mem_retainedSucc_of_edge he hnp
        have hAe := hhand q e he _ hAb hlegm
        have hbud' : r - b ≤ ((B - 1 : ℕ) : ℝ) * δ := by
          have h1 : (1 : ℕ) ≤ B := hlt.le
          rw [Nat.cast_sub h1, Nat.cast_one, sub_mul, one_mul, hbdef]
          linarith
        have hrest := ih e.tgt hret b (by linarith) hbr hbud' (by intro h; cases h) (Φ T)
          (by rw [← hguards q e he]; exact hleg) hAe
        refine rrespP_step hm he (DLCalTiming.sem_ode_restrict hΦT hT0 le_rfl) hleg
          (rrespP_mono ?_ hrest)
        rintro q' μ ⟨h1, h2, hμL⟩
        exact ⟨h1, h2, fun i => (hμL i).trans (right_sol_left hΦ' i)⟩
  | @stepRepoPre q B m hm hrepo hB hne _ ih =>
      intro a ha har hbud hpre ρ hPre hA
      have ha0 : a = 0 := hpre rfl
      subst ha0
      exact repoStep G ch fR domR fL domL gL tg guard hgR hguards hguardR hfL hdomL hdomR hgL hfR
        hsys hdomM A hAfv hAdom hhand hrepoProg hL ω₀ hx hm true (by simpa using hrepo) le_rfl
        hL.hr (fun _ => rfl) hPre hA (fun q' hq' ρ' hg' hA' => ih q' hq' 0 le_rfl hL.hr hbud
          (fun _ => rfl) ρ' hg' hA')
  | @stepRepoPost q B m hm hrepo hB hne _ ih =>
      intro a ha har hbud _ ρ hPre hA
      exact repoStep G ch fR domR fL domL gL tg guard hgR hguards hguardR hfL hdomL hdomR hgL hfR
        hsys hdomM A hAfv hAdom hhand hrepoProg hL ω₀ hx hm false (by simpa using hrepo) ha har
        (fun h => by cases h) hPre hA (fun q' hq' ρ' hg' hA' => ih q' hq' a ha har hbud
          (by intro h; cases h) ρ' hg' hA')
  | @stepChosen q B σ m hm hj hlt S hS hneS hsub _ ih =>
      intro a ha har hbud _ ρ hPre hA
      have hw := hweight q m hm
      rw [hw] at hlt ih
      by_cases hfit : r - a ≤ δ
      · exact coverX_finish G ch fR domR fL domL tg guard hgR hguards hfL hdomL hdomR hfR
          hsys hdomM epsR δ lam hlam hspan A hAdom hbox hhand hwf hL ω₀ hm hj ha har hfit hPre hA
      · push Not at hfit
        have hlq := hlam q
        set b := a + δ with hbdef
        have hab : a ≤ b := by linarith
        have hbr : b ≤ r := by linarith
        have hρdom : Formula.sat domR ρ := (sat_merge_R hdomR ω₀ (ΦL a) ρ).mp (hAdom q _ hA)
        have hmdom : Formula.sat m.dom ρ := by rw [hdomM q m hm]; exact hρdom
        obtain ⟨⟨Φ, hΦ⟩, -⟩ := hwf q (modeAt_lt hm) m hm ρ hPre hmdom trivial
        set T := lam q * (b - a) with hT
        have hTδ : T = lam q * δ := by rw [hT, hbdef]; ring
        have hT0 : 0 ≤ T := by rw [hTδ]; exact mul_nonneg hlq.le hδ.le
        have hTε : T ≤ epsR := by rw [hTδ]; exact hspan q
        have hΦT : ODESol m.sys m.dom ρ T Φ := ODESol_restrict hΦ hT0 hTε
        have hΦ' : ODESol (rightBlock (fR q) (Term.const 1)) domR ρ T Φ := by
          rw [← hsys q m hm, ← hdomM q m hm]; exact hΦT
        have hLs := odeSol_shift hL ha hab hbr
        have hj' := joint_of_sols_lam tg (lam q) hlq hfL (hfR q (modeAt_lt hm)) hdomL hdomR hLs hΦ' ω₀
        simp only [add_zero, add_sub_cancel, hΦ'.hΦ0] at hj'
        have hAb : Formula.sat (A q) (mergeLR ω₀ (ΦL b) (Φ T)) := hbox q m hm hj _ _ hA hj'
        -- the chosen successor from the coverage certificate
        obtain ⟨q', hq'S, hgq'⟩ := hcovJ q S hS _ (hRJ q _ hAb)
        obtain ⟨e, he, rfl, -⟩ := declSucc_edge (hsub q' hq'S)
        have hlegm : SwitchLegal e (mergeLR ω₀ (ΦL b) (Φ T)) := by
          unfold SwitchLegal; rw [hguards q e he]; exact hgq'
        have hleg : SwitchLegal e (Φ T) := (switchLegal_merge hgR he ω₀ (ΦL b)).mp hlegm
        have hAe := hhand q e he _ hAb hlegm
        have hbud' : r - b ≤ ((B - 1 : ℕ) : ℝ) * δ := by
          have h1 : (1 : ℕ) ≤ B := hlt.le
          rw [Nat.cast_sub h1, Nat.cast_one, sub_mul, one_mul, hbdef]
          linarith
        have hrest := ih e.tgt hq'S b (by linarith) hbr hbud' (by intro h; cases h) (Φ T)
          (by rw [← hguards q e he]; exact hleg) hAe
        refine rrespP_step hm he (DLCalTiming.sem_ode_restrict hΦT hT0 le_rfl) hleg
          (rrespP_mono ?_ hrest)
        rintro q' μ ⟨h1, h2, hμL⟩
        exact ⟨h1, h2, fun i => (hμL i).trans (right_sol_left hΦ' i)⟩
  | @repoChosen q B σ m hm hB S hS hneS hsub _ ih =>
      intro a ha har hbud hpre ρ hPre hA
      have hρdom : Formula.sat domR ρ := (sat_merge_R hdomR ω₀ (ΦL a) ρ).mp (hAdom q _ hA)
      have hgLm : σ = SrcSetting.preJ → Formula.sat gL (mergeLR ω₀ (ΦL a) ρ) := by
        intro hσ; rw [hpre hσ]; exact (sat_merge_L hgL ω₀ _ ρ).mpr hx
      obtain ⟨q', hq'S, hgq'⟩ := hcovR q σ S hS _ (hRR q σ _ hA hgLm)
      obtain ⟨e, he, rfl, -⟩ := exitSucc_edge (hsub q' hq'S)
      have hlegm : SwitchLegal e (mergeLR ω₀ (ΦL a) ρ) := by
        unfold SwitchLegal; rw [hguards q e he]; exact hgq'
      have hleg : SwitchLegal e ρ := (switchLegal_merge hgR he ω₀ (ΦL a)).mp hlegm
      have hAe := hhand q e he _ hA hlegm
      have hmdom : Formula.sat m.dom ρ := by rw [hdomM q m hm]; exact hρdom
      have hrest := ih e.tgt hq'S a ha har hbud hpre ρ
        (by rw [← hguards q e he]; exact hleg) hAe
      exact rrespP_step hm he (sem_ode_zero m.sys m.dom hmdom) hleg hrest
  | @hop q B σ m hm S hS hneS hsub _ ih =>
      intro a ha har hbud hpre ρ hPre hA
      have hρdom : Formula.sat domR ρ := (sat_merge_R hdomR ω₀ (ΦL a) ρ).mp (hAdom q _ hA)
      have hgLm : σ = SrcSetting.preJ → Formula.sat gL (mergeLR ω₀ (ΦL a) ρ) := by
        intro hσ; rw [hpre hσ]; exact (sat_merge_L hgL ω₀ _ ρ).mpr hx
      have hPrem : Formula.sat (guard q) (mergeLR ω₀ (ΦL a) ρ) :=
        (sat_merge_R (hguardR q) ω₀ _ ρ).mpr hPre
      obtain ⟨q', hq'S, hgq'⟩ := hcovS q σ S hS _ (hRS q σ _ hA hPrem hgLm)
      obtain ⟨e, he, rfl, -⟩ := exitSucc_edge (hsub q' hq'S)
      have hlegm : SwitchLegal e (mergeLR ω₀ (ΦL a) ρ) := by
        unfold SwitchLegal; rw [hguards q e he]; exact hgq'
      have hleg : SwitchLegal e ρ := (switchLegal_merge hgR he ω₀ (ΦL a)).mp hlegm
      have hAe := hhand q e he _ hA hlegm
      have hmdom : Formula.sat m.dom ρ := by rw [hdomM q m hm]; exact hρdom
      have hrest := ih e.tgt hq'S a ha har hbud hpre ρ
        (by rw [← hguards q e he]; exact hleg) hAe
      exact rrespP_step hm he (sem_ode_zero m.sys m.dom hmdom) hleg hrest

end Piece

end RelCertifier

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-- **The gated one-piece window, answered from a cover.** The window's own guard test puts
the left in its guard at the start; the start configuration `(q, B, preJ)` is covered and the
window's duration fits the budget (`dt ≤ B · δ`); the instance turns the end facts (the entered
guard and the entered mode's anchor at the merged end state) into the loop postcondition. -/
theorem coverX_gresp (G : SearchGraph (Var n)) (ch : ChoiceData)
    (fR : ℕ → Fin n → Term (Var n)) (domR : Formula (Var n)) (fL : Fin n → Term (Var n))
    (domL gL : Formula (Var n)) (b : Fin n) (guard : ℕ → Formula (Var n))
    (hgR : GuardsRight G) (hguards : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = guard e.tgt)
    (hguardR : ∀ q, (guard q).fv ⊆ range Rv)
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv) (hdomR : domR.fv ⊆ range Rv)
    (hgL : gL.fv ⊆ range Lv) (hfR : ∀ q, q < G.modes.length → ∀ i, (fR q i).fv ⊆ range Rv)
    (hsys : ∀ q m, G.modeAt q = some m → m.sys = rightBlock (fR q) (Term.const 1))
    (hdomM : ∀ q m, G.modeAt q = some m → m.dom = domR)
    (hweight : ∀ q m, G.modeAt q = some m → m.weight = 1)
    (epsR δ : ℝ) (hδ : 0 < δ) (lam : ℕ → ℝ) (hlam : ∀ q, 0 < lam q)
    (hspan : ∀ q, lam q * δ ≤ epsR)
    (A : ℕ → Formula (Var n)) (hAfv : ∀ q, (A q).fv ⊆ range Lv ∪ range Rv)
    (hAdom : ∀ q y, Formula.sat (A q) y → Formula.sat domR y)
    (hbox : ∀ q m, G.modeAt q = some m → ch.jointOK q = true → ∀ σ ω, Formula.sat (A q) σ →
      Program.sem (Program.ode (jointSys fL (fR q) (Term.const (lam q))) (Formula.and domL domR))
        σ ω → Formula.sat (A q) ω)
    (hhand : ∀ q, ∀ e ∈ G.edgesFrom q, ∀ y, Formula.sat (A q) y → SwitchLegal e y →
      Formula.sat (A e.tgt) y)
    (hwf : WellFormedR G guard epsR)
    (hprune : ∀ q m, G.modeAt q = some m → ∀ e ∈ G.edgesFrom q, e.pruned = true →
      ∀ σ ω, Formula.sat (A q) σ →
      Program.sem (Program.ode (jointSys fL (fR q) (Term.const (lam q))) (Formula.and domL domR))
        σ ω → ¬ Formula.sat e.guard ω)
    (hrepoProg : ∀ q m, G.modeAt q = some m → ∀ pre : Bool,
      (if pre then ch.repoPre q else ch.repoPost q) = true →
      RepoProgress G A gL (guard q) q pre)
    (RJ : ℕ → Formula (Var n)) (hRJ : ∀ q y, Formula.sat (A q) y → Formula.sat (RJ q) y)
    (hcovJ : ∀ q S, S ∈ ch.jointS q → ∀ y, Formula.sat (RJ q) y →
      ∃ q' ∈ S, Formula.sat (guard q') y)
    (RR : ℕ → SrcSetting → Formula (Var n))
    (hRR : ∀ q σ y, Formula.sat (A q) y → (σ = SrcSetting.preJ → Formula.sat gL y) →
      Formula.sat (RR q σ) y)
    (hcovR : ∀ q σ S, S ∈ ch.repoS q σ → ∀ y, Formula.sat (RR q σ) y →
      ∃ q' ∈ S, Formula.sat (guard q') y)
    (RS : ℕ → SrcSetting → Formula (Var n))
    (hRS : ∀ q σ y, Formula.sat (A q) y → Formula.sat (guard q) y →
      (σ = SrcSetting.preJ → Formula.sat gL y) → Formula.sat (RS q σ) y)
    (hcovS : ∀ q σ S, S ∈ ch.hopS q σ → ∀ y, Formula.sat (RS q σ) y →
      ∃ q' ∈ S, Formula.sat (guard q') y)
    (dt : ℝ) (B : ℕ) (hdt : dt ≤ (B : ℝ) * δ) (q : ℕ)
    (σ : State (Var n)) (hgq : Formula.sat (guard q) σ)
    (hcov : Formula.sat gL σ → CoveredX G ch ⟨q, B, SrcSetting.preJ⟩)
    (hAσ : Formula.sat gL σ → Formula.sat (A q) σ)
    (post : ℕ → Formula (Var n))
    (hpost : ∀ ν, Program.sem (windowSeg (leftBlock fL) domL ((Side.Aux, b) : Var n) dt 1) σ ν →
      ∀ q' μ, (∀ i, μ (Lv i) = ν (Lv i)) → Formula.sat (guard q') μ →
        Formula.sat (A q') (mergeLR σ ν μ) → Formula.sat (post q') μ) :
    GResp G q (gwindowSeg gL (leftBlock fL) domL ((Side.Aux, b) : Var n) dt 1) post σ := by
  refine gresp_gate (fun hg => gresp_of_rresp (fun ν hwin => ?_))
  set tg : Var n := ((Side.Aux, b) : Var n) with htg
  have hP := vars_windowSegL_sub fL domL b dt 1 hfL hdomL
  have hR : ∀ i, ν (Rv i) = σ (Rv i) := by
    intro i
    refine (Program.bound_effect _ hwin (Rv i) ?_).symm
    intro hb
    rcases hP (Or.inr hb) with h' | ⟨j, hj⟩
    · exact absurd (Set.mem_singleton_iff.mp h') (by simp [Rv, Prod.ext_iff])
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
  -- the left run of the one clocked piece
  have hw : Program.sem (windowSeg (leftBlock fL) domL tg dt 1) σ ν := hwin
  simp only [windowSeg, List.replicate_one, bigSeq] at hw
  obtain ⟨mid, hseg, hrest⟩ := hw
  rw [sem_test] at hrest
  obtain ⟨hmid, -⟩ := hrest
  rw [hmid] at hseg
  obtain ⟨r, ΦL, hL, hΦr, hrdt⟩ := clockedSeg_sol hseg
  have htgL : ∀ i, tg ≠ Lv i := fun i h => by simp [htg, Lv, Prod.ext_iff] at h
  have htgnot : tg ∉ gL.fv := fun h => by
    obtain ⟨i, hi⟩ := hgL h
    exact htgL i hi.symm
  have hx : Formula.sat gL (ΦL 0) := by
    rw [hL.hΦ0]
    exact (Formula.coincidence gL (fun v hv =>
      Function.update_of_ne (fun hc => htgnot (by rw [← hc]; exact hv)) _ _)).mpr hg
  have hA0 : Formula.sat (A q) (mergeLR σ (ΦL 0) ν) := by
    refine (sat_of_agree (hAfv q) (y := σ) (fun i => ?_) (fun i => ?_)).mpr (hAσ hg)
    · rw [mergeLR_L, hL.hΦ0, Function.update_of_ne (htgL i).symm]
    · rw [mergeLR_R, hR i]
  have hgν : Formula.sat (guard q) ν :=
    (sat_merge_R (hguardR q) σ (ΦL 0) ν).mp ((sat_merge_R (hguardR q) σ (ΦL 0) σ).mpr hgq
      |> fun h => by
        refine (Formula.coincidence (guard q) (fun v hv => ?_)).mp h
        obtain ⟨j, rfl⟩ := hguardR q hv
        rw [mergeLR_R, mergeLR_R, hR j])
  have hbud : r - 0 ≤ ((B : ℕ) : ℝ) * δ := by linarith
  have hpiece := coverX_piece G ch fR domR fL domL gL tg guard hgR hguards hguardR hfL hdomL
    hdomR hgL hfR hsys hdomM hweight epsR δ hδ lam hlam hspan A hAfv hAdom hbox
    hhand hwf hprune hrepoProg RJ hRJ hcovJ RR hRR hcovR RS hRS hcovS hL σ hx
    ⟨q, B, SrcSetting.preJ⟩ (hcov hg) 0 le_rfl hL.hr hbud (fun _ => rfl) ν hgν hA0
  rw [hΦr] at hpiece
  refine rresp_of_rrespP (rrespP_mono ?_ hpiece)
  rintro q' μ ⟨hgq', hAq', hμL⟩
  exact hpost ν hwin q' μ hμL hgq' hAq'

end RelCertifier
