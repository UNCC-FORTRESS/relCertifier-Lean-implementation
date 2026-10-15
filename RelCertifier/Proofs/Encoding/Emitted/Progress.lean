/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge, part 5: reposition progress from the emitted certificates

For every reposition node `(l, q, pre)` of a cover the tool emits a progress certificate
(`ProgressE`: one stage in either direction, or two upward stages, and the exits the landing
covers). Its verdict (`ProgressVerd`, the queries the progress runner rebuilds) is read as
facts over the node's region by `progressVerd_one` / `progressVerd_one_down` /
`progressVerd_two`; `repoProgress_one` / `repoProgress_one_down` / `repoProgress_two` turn
them into the general theorem's `RepoProgress` premise, with Assumption 1 for the cycles, the
anchor kept along the frozen flow (`AG_boxD`) and the pruned exits excluded (`AG_pruneD`).
The certificate's shape facts (`progOK`: positive rates, variables right, a two-stage
certificate upward in both stages, exits declared non-self non-pruned successors, mode
indices by name) are decided in the kernel.
-/
import RelCertifier.Proofs.Encoding.Emitted.Anchor
import RelCertifier.Proofs.Encoding.Progress
import RelCertifier.VerdictsV2.ProgressPin
import RelCertifier.Proofs.Encoding.Emitted.Region

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL DLCalTiming Parse Run Set Oracle Progress

variable {n : ℕ}

section Defs

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
  (prog : ProgressEmitE)

/-- Every emitted certificate's verdict. -/
def ProgAll : Prop := ∀ c ∈ prog.certs, ProgressVerd p cX n c

/-- The certificate of reposition node `(l, q, pre)`. -/
def certFor (l q : ℕ) (pre : Bool) : Option ProgressE :=
  prog.certs.find? (fun c => c.mL == (mLof p l).name && c.mR == (mRof p q).name && c.pre == pre)

/-- A stage is positive-rate, on a right variable that resolves (either direction). -/
def stageOK (st : ProgressStageE) : Bool :=
  (0 < st.rate) && (resolveVar (vars p) n Side.R st.var).isSome &&
    !st.var.startsWith "L_"

/-- The certificate's stages pass `stageOK`: one stage in either direction, or two stages
both upward (the only two-stage form the lemmas cover); its exits are declared non-self
non-pruned successors of `q`. -/
def certOK (q : ℕ) (c : ProgressE) : Bool :=
  (c.stages.length == 1 || (c.stages.length == 2 && c.stages.all (·.up))) &&
  c.stages.all (stageOK p n) &&
  c.exits.all (fun nm => (mRof p q).next.contains nm && nm != (mRof p q).name &&
    !(prunedOf cov (mRof p q).name nm))

/-- Every reposition node of every window has a well-shaped certificate; mode indices by name
are the indices. -/
def progOK : Bool :=
  (List.range (nL p)).all (fun l => modeIdx p.L.modes (mLof p l).name == l &&
    (List.range (nR p)).all (fun q => modeIdx p.R.modes (mRof p q).name == q &&
      [true, false].all (fun pre =>
        !(if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) ||
        (match certFor p prog l q pre with
         | some c => certOK p n cov q c
         | none => false))))

/-- The region of a reposition node as a formula (`RegionSat`). -/
noncomputable def regionF (l q : ℕ) (pre : Bool) : Formula (Var n) :=
  Formula.and (Formula.and (Formula.and (Formula.and (hostEvolve (vars p) n Side.L (mLof p l))
    (cutF (cL p n cX l))) (FRow p n l)) (if pre then guardL p n l else Formula.tt))
    (Formula.and (hostEvolve (vars p) n Side.R (mRof p q)) (cutF (cR p n cX q)))

end Defs

section Proofs

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}
  (hs : structOK p n cov cX = true)

include hs

theorem regionSat_of_regionF {l q : ℕ} (hl : l < nL p) (pre : Bool) (y : State (Var n))
    (h : Formula.sat (regionF p n cX l q pre) y) :
    RegionSat (vars p) n cX (mLof p l) (mRof p q) (rowOf p l) pre y := by
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := h
  refine ⟨h1, (sat_cutF _ _).mp h2, ?_, ?_, h5, (sat_cutF _ _).mp h6⟩
  · have := (sat_FM_iff _ _ y).mp h3
    rwa [cons_g_gs p n l (rowsOK_at (hrows hs) hl)] at this
  · intro hp; rw [hp] at h4; exact h4

theorem AG_regionF {l q : ℕ} (hl : l < nL p) (hq : q < nR p) (pre : Bool) (y : State (Var n))
    (hA : Formula.sat (AG p n cX cov l q) y) (hgL : pre = true → Formula.sat (guardL p n l) y) :
    Formula.sat (regionF p n cX l q pre) y := by
  obtain ⟨hFA, -⟩ := (sat_FM_append _ _ _ y).mp hA.1
  obtain ⟨hF, hat⟩ := (sat_FM_append _ _ _ y).mp hFA
  obtain ⟨hLc, hRc⟩ := (atomTerms_iff (hiffL hs hl) (hiffR hs hq) y).mp hat
  refine ⟨⟨⟨⟨?_, (sat_cutF _ _).mpr hLc⟩, hF⟩, ?_⟩, ?_, (sat_cutF _ _).mpr hRc⟩
  · rw [hostEvolve_L (hu hs) hl]; exact hA.2.1
  · cases pre with
    | true => exact hgL rfl
    | false => trivial
  · rw [hostEvolve_R (hu hs) hq]; exact hA.2.2

omit hs in
theorem progOK_at (hpo : progOK p n cov prog = true) {l q : ℕ} (hl : l < nL p) (hq : q < nR p) :
    modeIdx p.L.modes (mLof p l).name = l ∧ modeIdx p.R.modes (mRof p q).name = q ∧
    ∀ pre : Bool, (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true →
      ∃ c, certFor p prog l q pre = some c ∧ certOK p n cov q c = true := by
  simp only [progOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hpo
  obtain ⟨hL, hall⟩ := hpo l hl
  obtain ⟨hR, hpre⟩ := hall q hq
  refine ⟨hL, hR, fun pre hflag => ?_⟩
  have hp := hpre pre (by cases pre <;> simp)
  rcases hp with h | h
  · rw [hflag] at h; exact absurd h (by decide)
  · rcases hc : certFor p prog l q pre with _ | c
    · simp only [hc] at h; exact absurd h (by decide)
    · simp only [hc] at h; exact ⟨c, rfl, h⟩

omit hs in
theorem certFor_mem {l q : ℕ} {pre : Bool} {c : ProgressE} (h : certFor p prog l q pre = some c) :
    c ∈ prog.certs ∧ c.mL = (mLof p l).name ∧ c.mR = (mRof p q).name ∧ c.pre = pre := by
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hmem, hp.1.1, hp.1.2, hp.2⟩

omit hs in
theorem certOK_exit {q : ℕ} {c : ProgressE} (h : certOK p n cov q c = true) {nm : String}
    (hnm : nm ∈ c.exits) :
    nm ∈ (mRof p q).next ∧ nm ≠ (mRof p q).name ∧ prunedOf cov (mRof p q).name nm = false := by
  simp only [certOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, bne_iff_ne,
    ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.2 nm hnm
  exact ⟨h1, h2, h3⟩

omit hs in
theorem certOK_stage {q : ℕ} {c : ProgressE} (h : certOK p n cov q c = true) {st : ProgressStageE}
    (hst : st ∈ c.stages) :
    0 < (st.rate : ℝ) ∧ (resolveVar (vars p) n Side.R st.var).isSome = true ∧
    st.var.startsWith "L_" = false := by
  simp only [certOK, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.2 st hst
  simp only [stageOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true] at this
  exact ⟨by exact_mod_cast this.1.1, this.1.2, this.2⟩

omit hs in
/-- The shape: one stage (either direction), or two stages both upward. -/
theorem certOK_shape {q : ℕ} {c : ProgressE} (h : certOK p n cov q c = true) :
    (∃ st, c.stages = [st]) ∨ ∃ sth st, c.stages = [sth, st] ∧ sth.up = true ∧ st.up = true := by
  simp only [certOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h
  rcases h.1.1 with h1 | ⟨h2, hup⟩
  · obtain ⟨st, hst⟩ := List.length_eq_one_iff.mp h1
    exact Or.inl ⟨st, hst⟩
  · rcases hc : c.stages with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> rw [hc] at h2 hup <;> simp at h2
    exact Or.inr ⟨a, b, rfl, hup a (by simp), hup b (by simp)⟩

omit hs in
/-- A resolved right variable is `Rv` of its index. -/
theorem resolve_Rv {v : Var n} {name : String} (hfree : name.startsWith "L_" = false)
    (h : resolveVar (vars p) n Side.R name = some v) : v = Rv v.2 := by
  have := Run.resolveVar_side_R hfree h
  exact Prod.ext this rfl

/-- An exit named by the certificate, enabled at `y`, is a declared non-self non-pruned edge
whose target's guard holds. -/
theorem exit_edge {q : ℕ} (hq : q < nR p) {c : ProgressE} (hc : certOK p n cov q c = true)
    (y : State (Var n))
    (h : ∃ nm ∈ c.exits, ∃ md ∈ p.R.modes, md.name = nm ∧
      Formula.sat (hostGuard (vars p) n Side.R md) y) :
    ∃ e ∈ (grOf p n (prunedOf cov)).edgesFrom q, e.tgt ≠ q ∧ e.pruned = false ∧
      Formula.sat (guardR p n e.tgt) y := by
  obtain ⟨nm, hnm, md, hmd, hname, hg⟩ := h
  obtain ⟨hnext, hne, hnp⟩ := certOK_exit hc hnm
  have hres' := hres hs
  have hnd : (p.R.modes.map (·.name)).Nodup := by
    simp only [namesResolve, Bool.and_eq_true, decide_eq_true_eq] at hres'; exact hres'.1.1
  have htlt := tgtIdx_lt hres' hq hnext
  have hmd' : mRof p (tgtIdx p nm) = md := by
    refine List.inj_on_of_nodup_map hnd (mRof_mem htlt) hmd ?_
    rw [name_tgtIdx hres' hq hnext, hname]
  refine ⟨edgeOf p n (prunedOf cov) q nm, edge_mem_grOf hq hnext, ?_, hnp, ?_⟩
  · intro heq
    simp only [edgeOf] at heq
    apply hne
    rw [← name_tgtIdx hres' hq hnext, heq]
  · show Formula.sat (guardR p n (tgtIdx p nm)) y
    unfold guardR; rw [hmd']; exact hg

/-- **The reposition-progress premise of every reposition node of window `l`.** -/
theorem hrepoProg_of (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX)
    (hprog : ProgAll p n cX prog) (hpo : progOK p n cov prog = true)
    {reg : Formula (Var n)} (hregR : reg.fv ⊆ range Rv)
    (hinv : RegionInvariant (grOf p n (prunedOf cov)) reg)
    (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p))
    (hdyn : ∀ l < nL p, ∀ q < nR p, ∀ pre : Bool,
      (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true →
      DynVerd p n cX cov l q pre)
    {l : ℕ} (hl : l < nL p) :
    ∀ q m, (grOf p n (prunedOf cov)).modeAt q = some m → ∀ pre : Bool,
      (if pre then (chOf p cov l).repoPre q else (chOf p cov l).repoPost q) = true →
      RepoProgress (grOf p n (prunedOf cov)) (AGr p n cX cov reg l) (guardL p n l) (guardR p n q)
        q pre := by
  intro q m hm pre hflag
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm
  have hflag' : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true := by
    cases pre <;> simpa [chOf] using hflag
  obtain ⟨hidxL, hidxR, hcert⟩ := progOK_at hpo hl hq
  obtain ⟨c, hcf, hok⟩ := hcert pre hflag'
  obtain ⟨hcmem, hcL, hcR, hcpre⟩ := certFor_mem hcf
  have hv := hprog c hcmem
  -- Assumption 1 at `q`
  have hwfq := hwf q (by rw [grOf_len]; exact hq) (modeOf p n q) hm
  have hex : ∀ x, Formula.sat (guardR p n q) x → Formula.sat (domR p n) x → Formula.sat reg x →
      ∃ Φ, ODESol (rightBlock (fR p n q) (Term.const 1)) (domR p n) x (epsR p) Φ :=
    fun x hg hd hr => (hwfq x hg hd hr).1
  have hcomp : ∀ x, Formula.sat (guardR p n q) x → Formula.sat (domR p n) x → Formula.sat reg x →
      ∀ t Φ, t ≤ epsR p →
      ODESol (rightBlock (fR p n q) (Term.const 1)) (domR p n) x t Φ →
      ∃ e ∈ (grOf p n (prunedOf cov)).edgesFrom q, Formula.sat (guardR p n e.tgt) (Φ t) :=
    fun x hg hd hr t Φ ht H => (hwfq x hg hd hr).2 t Φ ht H
  -- the anchor with the region, kept along the frozen flow
  have hAfv' : (AGr p n cX cov reg l q).fv ⊆ range Lv ∪ range Rv := by
    intro v hv
    rcases hv with hv | hv
    · exact AG_fv hs hl hq hv
    · exact Or.inr (hregR hv)
  have hboxD' : ∀ σ ω, Formula.sat (AGr p n cX cov reg l q) σ →
      (pre = true → Formula.sat (guardL p n l) σ) →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR p n q) (Term.const 1))
        (Formula.and (domL p n) (domR p n))) σ ω → Formula.sat (AGr p n cX cov reg l q) ω :=
    fun σ ω hA hg hω => ⟨AG_boxD hs hnc hst hl hq pre hflag' (hdyn l hl q hq pre hflag') σ ω hA.1 hg hω,
      reg_kept_joint hinv hregR (fR_fv (hnames hs) q) (domR_fv (hnames hs)) hm rfl rfl 1 one_pos hω hA.2⟩
  have hε : 0 < epsR p := (timeOK_at (htime hs) hl).1
  -- the region
  have hR : ∀ y, Formula.sat (AGr p n cX cov reg l q) y → (pre = true → Formula.sat (guardL p n l) y) →
      Formula.sat (regionF p n cX l q pre) y := fun y hA hg => AG_regionF hs hl hq pre y hA.1 hg
  have hRsat : ∀ y, Formula.sat (regionF p n cX l q pre) y →
      RegionSat (vars p) n cX (mLof p l) (mRof p q) (rowOf p l) pre y :=
    fun y hy => regionSat_of_regionF hs hl pre y hy
  rcases certOK_shape hok with ⟨st, hstg⟩ | ⟨sth, st, hstg, huph, hup⟩
  · -- one stage, in either direction
    obtain ⟨hrpos, -, hfree⟩ := certOK_stage hok (st := st) (by rw [hstg]; simp)
    cases hup : st.up
    · -- downward
      obtain ⟨v, hv', hrate, hline, hstart⟩ := progressVerd_one_down hv st hstg hup
      rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate hline hstart
      have hvR := resolve_Rv (p := p) hfree hv'
      refine repoProgress_one_down (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
        (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
        (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
        (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGr p n cX cov reg l) hAfv'
        (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε reg hregR (fun y h => h.2) hex hcomp hboxD'
        (fun e he hp σ ω hA hω => AG_pruneD hs hnc hst hl hq e he hp σ ω hA.1 hω) (regionF p n cX l q pre) hR
        v.2 (st.theta : ℝ) ?_ (st.rate : ℝ) hrpos ?_ ?_
      · intro y hy hθ
        exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
      · intro y hy hg hθ
        exact exit_edge hs hq hok y (hstart y (hRsat y hy) hg (by rw [hvR]; exact hθ))
      · intro y hy hlt
        exact hrate y (hRsat y hy) (by rw [hvR]; exact hlt)
    · -- upward
      obtain ⟨v, hv', hrate, hline, hstart⟩ := progressVerd_one hv st hstg hup
      rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate hline hstart
      have hvR := resolve_Rv (p := p) hfree hv'
      refine repoProgress_one (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
        (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
        (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
        (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGr p n cX cov reg l) hAfv'
        (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε reg hregR (fun y h => h.2) hex hcomp hboxD'
        (fun e he hp σ ω hA hω => AG_pruneD hs hnc hst hl hq e he hp σ ω hA.1 hω) (regionF p n cX l q pre) hR
        v.2 (st.theta : ℝ) ?_ ?_ (st.rate : ℝ) hrpos ?_
      · intro y hy hθ
        exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
      · intro y hy hg hθ
        exact exit_edge hs hq hok y (hstart y (hRsat y hy) hg (by rw [hvR]; exact hθ))
      · intro y hy hlt
        exact hrate y (hRsat y hy) (by rw [hvR]; exact hlt)
  · -- two stages, both upward
    obtain ⟨hrhpos, -, hfreeh⟩ := certOK_stage hok (st := sth) (by rw [hstg]; simp)
    obtain ⟨hrpos, -, hfree⟩ := certOK_stage hok (st := st) (by rw [hstg]; simp)
    obtain ⟨w, v, hw', hv', hrate_h, hkeep_h, hrate, hline, hstart⟩ :=
      progressVerd_two hv sth st hstg huph hup
    rw [hcL, hcR, hidxL, hidxR, hcpre] at hrate_h hkeep_h hrate hline hstart
    have hvR := resolve_Rv (p := p) hfree hv'
    have hwR := resolve_Rv (p := p) hfreeh hw'
    refine repoProgress_two (grOf p n (prunedOf cov)) (fR p n q) (domL p n) (domR p n)
      (guardL p n l) (guardR p n) q (modeOf p n q) hm rfl rfl (fR_fv (hnames hs) q)
      (domL_fv (hnames hs)) (domR_fv (hnames hs)) (guardL_fv (hnames hs) l) (guardR_fv (hnames hs))
      (grOf_guardsRight (hnames hs)) (grOf_guards q) (AGr p n cX cov reg l) hAfv'
      (fun y h => ⟨h.1.2.1, h.1.2.2⟩) pre (epsR p) hε reg hregR (fun y h => h.2) hex hcomp hboxD'
      (fun e he hp σ ω hA hω => AG_pruneD hs hnc hst hl hq e he hp σ ω hA.1 hω) (regionF p n cX l q pre) hR
      v.2 (st.theta : ℝ) ?_ ?_ (st.rate : ℝ) hrpos w.2 (sth.theta : ℝ) (sth.rate : ℝ) hrhpos
      ?_ ?_ ?_
    · intro y hy hθ
      exact exit_edge hs hq hok y (hline y (hRsat y hy) (by rw [hvR]; exact hθ))
    · intro y hy hg hθ
      exact exit_edge hs hq hok y (hstart y (hRsat y hy) hg (by rw [hvR]; exact hθ))
    · intro y hy hlt
      exact hrate_h y (hRsat y hy) (by rw [hwR]; exact hlt)
    · intro y hy hle
      exact hkeep_h y (hRsat y hy) (by rw [hwR]; exact hle)
    · intro y hy hθh hlt
      exact hrate y (hRsat y hy) (by rw [hwR]; exact hθh) (by rw [hvR]; exact hlt)

end Proofs

end Emitted
end RelCertifier
