/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Guard-gated switching on the right: the per-switch obligation and the guarded chain

The right automaton `rightAutomatonBody G mv` (`JointBridge.lean`) already tests each
edge's guard after the flow: `modeStep = ?(mv = q) ; flow_q ; ⋃_e (?e.guard ; mv := e.tgt)`.
What made the earlier instance theorems statements about a relaxation of the paper's model
was the GRAPH: every constructed edge carried `guard := ⊤`, and the bridge lemmas took the
premise `htt : ∀ q e, e.guard = ⊤`. In the paper's `cpsProg` the right switches only into a
declared successor whose guard holds at the switch state (`?(m ∈ next(mv)) ; ?guard_m(x) ;
mv := m ; flow`), and staying in a mode is the same move (`m = mv`, its own guard tested).

This file is the generic layer for the GUARDED automaton: an edge carries the lowered guard
of the mode it enters (`e.guard = hostGuard … (mR e.tgt)`, built per instance exactly as the
left guards are), and no lemma here assumes anything about `e.guard`.

* `SwitchLegal e ω`: the per-switch obligation, the entered mode's guard holds at `ω`.
* `gseg s = flow_{s.q} ; ?s.edge.guard`: one segment WITH its switch test. A run of
  `bigSeq (segs.map gseg)` is exactly a sequence of flows each followed by a legal switch.
* `guarded_rights_bridge`: such a run IS a run of `star (rightAutomatonBody G mv)` with the
  mode variable threaded (`mv : q0 ↦ qfOf segs q0`); no guard premise.
* `GResp G q P post σ`: the guarded step obligation. For EVERY run of the left program `P`
  from `σ`, there is a list of declared segments starting at `q`, each switch legal, whose
  end state satisfies `post` of the final mode. The segments are chosen AFTER the left run,
  so the final switch can depend on where the response ends (the paper's demonic choice of
  successor is resolved by choosing an enabled one).
* `hstep_single_GR`/`hstep_assembled_GR` (region-carrying loop invariant `phiInvR`),
  `hstep_single_GF`/`hstep_assembled_GF` (`phiInvF`, `mvValid`), `hstepMode_GR`/`GF`
  (per left mode, for `theorem3_modeKeyed`): the loop steps over the guarded automaton.
* Building blocks for the instances: `gresp_gate` (the left window's own guard test),
  `gresp_hop` (a zero-duration flow followed by a legal switch), `gresp_final` (the
  response flow, then a switch into an enabled successor; its `NonblockingAt` premise is
  Assumption 1 at the end states the response can reach, discharged per instance from the
  explicit end state), `gresp_mono`.
* Footprint lemmas without `htt`: `vars_bodyG_sub` and the `hd`/`hddF` dischargers, whose
  only new premise is that the edge guards read right coordinates.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.CutComposition
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Encoding.WindowRF

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-! ## The per-switch obligation and the guarded segment -/

/-- **The per-switch obligation**: the guard carried by edge `e` (the entered mode's lowered
guard) holds at the switch state `ω`. -/
def SwitchLegal (e : REdge (Var n)) (ω : State (Var n)) : Prop :=
  Formula.sat e.guard ω

/-- One guarded segment: the flow of the segment's mode, then the switch test of its edge. -/
def gseg (s : ℕ × RMode (Var n) × REdge (Var n)) : Program (Var n) :=
  Program.seq (Program.ode s.2.1.sys s.2.1.dom) (Program.test s.2.2.guard)

theorem sem_gseg {s : ℕ × RMode (Var n) × REdge (Var n)} {ν μ : State (Var n)} :
    Program.sem (gseg s) ν μ ↔
      Program.sem (Program.ode s.2.1.sys s.2.1.dom) ν μ ∧ SwitchLegal s.2.2 μ := by
  constructor
  · rintro ⟨κ, hflow, hκ, hg⟩
    subst hκ
    exact ⟨hflow, hg⟩
  · rintro ⟨hflow, hg⟩
    exact ⟨μ, hflow, rfl, hg⟩

/-- The mode variable is fresh for every declared guard. -/
def GuardsFresh (G : SearchGraph (Var n)) (mv : Var n) : Prop :=
  ∀ q, ∀ e ∈ G.edgesFrom q, mv ∉ e.guard.fv

/-- The guards read right coordinates only (the footprint premise replacing `htt`). -/
def GuardsRight (G : SearchGraph (Var n)) : Prop :=
  ∀ q, ∀ e ∈ G.edgesFrom q, e.guard.fv ⊆ range Rv

theorem guardsFresh_of_right (G : SearchGraph (Var n)) (a : Fin n)
    (h : GuardsRight G) : GuardsFresh G ((Side.Aux, a) : Var n) := by
  intro q e he hx
  obtain ⟨i, hi⟩ := h q e he hx
  exact absurd hi (by simp [Rv, Prod.ext_iff])

/-! ## The bridge: legal switches make a run of the guarded automaton -/

/-- One flow at a declared mode followed by a LEGAL switch along a declared edge is one
step of the guarded automaton. -/
theorem guarded_seg_step (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (hfv : mv ∉ (Program.ode m.sys m.dom).fv)
    {e : REdge (Var n)} (hm : G.modeAt q = some m) (he : e ∈ G.edgesFrom q)
    (hgf : mv ∉ e.guard.fv)
    {ν κ : State (Var n)} (hflow : Program.sem (Program.ode m.sys m.dom) ν κ)
    (hleg : SwitchLegal e κ) :
    Program.sem (Program.star (rightAutomatonBody G mv))
      (Function.update ν mv (q : ℝ)) (Function.update κ mv (e.tgt : ℝ)) := by
  have hg : Formula.sat e.guard (Function.update κ mv (q : ℝ)) :=
    (Formula.coincidence e.guard (fun y hy =>
      (Function.update_of_ne (fun hc => hgf (by rw [← hc]; exact hy)) _ _).symm)).mp hleg
  have hstep := modeStep_sem G mv q m hfv he hflow hg
  have hbody : Program.sem (rightAutomatonBody G mv)
      (Function.update ν mv (q : ℝ)) (Function.update κ mv (e.tgt : ℝ)) := by
    refine bigChoiceP_sem_of_mem (List.mem_filterMap.mpr ⟨q, ?_, ?_⟩) hstep
    · exact List.mem_range.mpr (by
        have := hm; simp only [SearchGraph.modeAt] at this
        exact List.getElem?_eq_some_iff.mp this |>.1)
    · rw [hm]; rfl
  exact Relation.ReflTransGen.head hbody Relation.ReflTransGen.refl

/-- **The guarded bridge, final mode pinned.** A run of `bigSeq (segs.map gseg)` (declared
modes, declared chained edges, every switch legal) is a run of the guarded automaton's star,
the mode variable going from `q0` to `qfOf segs q0`. No premise on the guards. -/
theorem guarded_rights_bridge (G : SearchGraph (Var n)) (mv : Var n)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv) :
    ∀ (segs : List (ℕ × RMode (Var n) × REdge (Var n))),
      (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) →
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs →
      ∀ (q0 : ℕ), ∀ {ν μ : State (Var n)},
        (∀ s, segs.head? = some s → s.1 = q0) →
        Program.sem (bigSeq (segs.map gseg)) ν μ →
        Program.sem (Program.star (rightAutomatonBody G mv))
          (Function.update ν mv (q0 : ℝ)) (Function.update μ mv ((qfOf segs q0) : ℝ)) := by
  intro segs
  induction segs with
  | nil =>
      intro _ _ q0 _ _ _ hrun
      rw [List.map_nil, bigSeq, sem_test] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact Relation.ReflTransGen.refl
  | cons s rest ih =>
      intro halign hchain q0 ν μ hstart hrun
      have hq0 : s.1 = q0 := hstart s rfl
      subst hq0
      simp only [List.map_cons, bigSeq] at hrun
      obtain ⟨κ, hseg, hrest⟩ := hrun
      obtain ⟨hflow, hleg⟩ := sem_gseg.mp hseg
      obtain ⟨hm, he⟩ := halign s (List.mem_cons_self ..)
      have hfirst := guarded_seg_step G mv s.1 s.2.1 (hfresh s.1 s.2.1 hm) hm he
        (hgf s.1 s.2.2 he) hflow hleg
      have htailstart : ∀ t, rest.head? = some t → t.1 = s.2.2.tgt := by
        intro t ht
        rcases rest with - | ⟨r, rs⟩
        · exact absurd ht (by simp)
        · simp only [List.head?_cons, Option.some.injEq] at ht
          subst ht; exact hchain.rel.symm
      have htail := ih (fun t ht => halign t (List.mem_cons_of_mem s ht))
        hchain.of_cons s.2.2.tgt htailstart hrest
      rw [qfOf_cons]
      exact Relation.ReflTransGen.trans hfirst htail

/-! ## The guarded step obligation -/

/-- **The guarded step obligation.** For every run of the left program `P` from `σ`, the
right can respond from mode `q` with declared segments whose every switch is legal (the
`gseg` tests), ending in a state satisfying `post` of the final mode. The segment list is
chosen after the left run, so the final switch may depend on the end state. -/
def GResp (G : SearchGraph (Var n)) (q : ℕ) (P : Program (Var n))
    (post : ℕ → Formula (Var n)) (σ : State (Var n)) : Prop :=
  ∀ ν, Program.sem P σ ν → ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
    (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
    List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
    (∀ s, segs.head? = some s → s.1 = q) ∧
    ∃ μ, Program.sem (bigSeq (segs.map gseg)) ν μ ∧ Formula.sat (post (qfOf segs q)) μ

theorem gresp_mono {G : SearchGraph (Var n)} {q : ℕ} {P : Program (Var n)}
    {post post' : ℕ → Formula (Var n)} {σ : State (Var n)}
    (himp : ∀ q' μ, Formula.sat (post q') μ → Formula.sat (post' q') μ)
    (h : GResp G q P post σ) : GResp G q P post' σ := by
  intro ν hν
  obtain ⟨segs, ha, hc, hh, μ, hrun, hp⟩ := h ν hν
  exact ⟨segs, ha, hc, hh, μ, hrun, himp _ μ hp⟩

/-- The left window's own guard test: `GResp` over `?φ ; P'` from `GResp` over `P'`
wherever `φ` holds. -/
theorem gresp_gate {G : SearchGraph (Var n)} {q : ℕ} {φ : Formula (Var n)}
    {P' : Program (Var n)} {post : ℕ → Formula (Var n)} {σ : State (Var n)}
    (h : Formula.sat φ σ → GResp G q P' post σ) :
    GResp G q (Program.seq (Program.test φ) P') post σ := by
  intro ν hν
  obtain ⟨κ, ⟨rfl, hφ⟩, hrun⟩ := hν
  exact h hφ ν hrun

/-- **A zero-duration hop with a legal switch.** At the end of the left run the right
switches from `q` along the declared edge `e` without flowing (a zero-duration run of
`q`'s flow, which needs `q`'s domain), provided the entered mode's guard holds there
(`SwitchLegal`), then responds from `e.tgt`. -/
theorem gresp_hop {G : SearchGraph (Var n)} {q : ℕ} {m : RMode (Var n)} {e : REdge (Var n)}
    (hm : G.modeAt q = some m) (he : e ∈ G.edgesFrom q)
    {P : Program (Var n)} {post : ℕ → Formula (Var n)} {σ : State (Var n)}
    (hlegal : ∀ ν, Program.sem P σ ν → Formula.sat m.dom ν ∧ SwitchLegal e ν)
    (hrest : GResp G e.tgt P post σ) : GResp G q P post σ := by
  intro ν hν
  obtain ⟨hdom, hleg⟩ := hlegal ν hν
  obtain ⟨segs, ha, hc, hh, μ, hrun, hp⟩ := hrest ν hν
  refine ⟨(q, m, e) :: segs, ?_, ?_, by simp, μ, ?_, ?_⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨hm, he⟩
    · exact ha s hs
  · rcases segs with - | ⟨r, rs⟩
    · simp
    · exact hc.cons (by
        intro y hy
        rw [List.head?_cons, Option.mem_some_iff] at hy
        subst hy
        exact (hh r rfl).symm)
  · simp only [List.map_cons, bigSeq]
    exact ⟨ν, sem_gseg.mpr ⟨sem_ode_zero m.sys m.dom hdom, hleg⟩, hrun⟩
  · rw [qfOf_cons]
    exact hp

/-- **Assumption 1 at the response's end states.** From every state `Post'` describes (where
the response flow in `qs` can end), some declared successor of `qs` is enabled (its switch is
legal) and the loop postcondition holds for the entered mode. Every instance discharges
this from the explicit end-state facts; it is the nonblocking half of the paper's
Assumption 1, restricted to the states the response reaches. -/
def NonblockingAt (G : SearchGraph (Var n)) (qs : ℕ) (Post' : Formula (Var n))
    (post : ℕ → Formula (Var n)) : Prop :=
  ∀ μ, Formula.sat Post' μ →
    ∃ e ∈ G.edgesFrom qs, SwitchLegal e μ ∧ Formula.sat (post e.tgt) μ

/-- **The response flow, then a switch into an enabled successor.** From a `faModal`
response that flows in the declared mode `qs` and ends in `Post'`, and `NonblockingAt`, the
guarded step obligation: after the flow the right takes a legal switch into a successor that
is enabled at the end state (chosen after the run, from the end state). -/
theorem gresp_final {G : SearchGraph (Var n)} {qs : ℕ} {ms : RMode (Var n)}
    (hm : G.modeAt qs = some ms)
    {P : Program (Var n)} {Post' : Formula (Var n)} {post : ℕ → Formula (Var n)}
    {σ : State (Var n)}
    (hfa : Formula.sat (faModal (Equiv.refl (Var n)) P
      (bigSeq [Program.ode ms.sys ms.dom]) Post') σ)
    (hnb : NonblockingAt G qs Post' post) : GResp G qs P post σ := by
  intro ν hν
  rw [faModal_sat] at hfa
  obtain ⟨μ, hrun, hpost⟩ := hfa ν hν
  rw [Program.rename_refl] at hrun
  simp only [bigSeq] at hrun
  obtain ⟨κ, hflow, hκ, -⟩ := hrun
  subst hκ
  obtain ⟨e, he, hleg, hp⟩ := hnb κ hpost
  refine ⟨[(qs, ms, e)], ?_, by simp, by simp, κ, ?_, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    exact ⟨hm, he⟩
  · simp only [List.map_cons, List.map_nil, bigSeq]
    exact ⟨κ, sem_gseg.mpr ⟨hflow, hleg⟩, rfl, trivial⟩
  · simpa [qfOf] using hp

/-- **The idle response.** The right makes no step at all (zero iterations of the star: no
switch, nothing to check) wherever the loop postcondition already holds for the current mode
at every end state of the left run. -/
theorem gresp_idle {G : SearchGraph (Var n)} {q : ℕ} {P : Program (Var n)}
    {post : ℕ → Formula (Var n)} {σ : State (Var n)}
    (h : ∀ ν, Program.sem P σ ν → Formula.sat (post q) ν) : GResp G q P post σ := by
  intro ν hν
  refine ⟨[], by simp, by simp, by simp, ν, ?_, ?_⟩
  · show Program.sem (Program.test Formula.tt) ν ν
    exact ⟨rfl, trivial⟩
  · simpa [qfOf] using h ν hν

/-- **The response flow, then an enabled switch, or nothing.** As `gresp_final`, except that
where the response flow ended where it started (`μ = ν`, a zero-duration run) the right may
make no step at all: the postcondition then holds for the current mode. -/
theorem gresp_final_idle {G : SearchGraph (Var n)} {qs : ℕ} {ms : RMode (Var n)}
    (hm : G.modeAt qs = some ms)
    {P : Program (Var n)} {Post' : Formula (Var n)} {post : ℕ → Formula (Var n)}
    {σ : State (Var n)}
    (hfa : Formula.sat (faModal (Equiv.refl (Var n)) P
      (bigSeq [Program.ode ms.sys ms.dom]) Post') σ)
    (hnb : ∀ ν μ, Program.sem (Program.ode ms.sys ms.dom) ν μ → Formula.sat Post' μ →
      (μ = ν ∧ Formula.sat (post qs) μ) ∨
        ∃ e ∈ G.edgesFrom qs, SwitchLegal e μ ∧ Formula.sat (post e.tgt) μ) :
    GResp G qs P post σ := by
  intro ν hν
  rw [faModal_sat] at hfa
  obtain ⟨μ, hrun, hpost⟩ := hfa ν hν
  rw [Program.rename_refl] at hrun
  simp only [bigSeq] at hrun
  obtain ⟨κ, hflow, hκ, -⟩ := hrun
  subst hκ
  rcases hnb ν κ hflow hpost with ⟨hκν, hp⟩ | ⟨e, he, hleg, hp⟩
  · refine ⟨[], by simp, by simp, by simp, κ, ?_, by simpa [qfOf] using hp⟩
    rw [hκν]
    show Program.sem (Program.test Formula.tt) ν ν
    exact ⟨rfl, trivial⟩
  · refine ⟨[(qs, ms, e)], ?_, by simp, by simp, κ, ?_, ?_⟩
    · intro s hs
      rw [List.mem_singleton] at hs
      subst hs
      exact ⟨hm, he⟩
    · simp only [List.map_cons, List.map_nil, bigSeq]
      exact ⟨κ, sem_gseg.mpr ⟨hflow, hleg⟩, rfl, trivial⟩
    · simpa [qfOf] using hp

/-- **A flow cannot END on an upper face it pushes away from.** If along every state of the
domain the coordinate `x` is at most `c`, and wherever `x = c` its derivative is negative,
then a run either ends strictly below `c` or has zero duration (ends where it started). -/
theorem ode_coord_end_lt_or_eq {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {ν μ : State (Var n)} (h : Program.sem (Program.ode sys dom) ν μ)
    {x : Var n} {f : Term (Var n)} (hx : (x, f) ∈ sys) {c : ℝ}
    (hle : ∀ s, Formula.sat dom s → s x ≤ c)
    (hneg : ∀ s, Formula.sat dom s → s x = c → Term.eval f s < 0) :
    μ x < c ∨ μ = ν := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, -, hdom⟩ := h
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · right; subst hr0; rw [← hΦr, hΦ0]
  left
  have hmem : r ∈ Set.Icc (0:ℝ) r := ⟨hr, le_refl r⟩
  have hμle : μ x ≤ c := hΦr ▸ hle _ (hdom r hmem)
  rcases lt_or_eq_of_le hμle with hlt | heq
  · exact hlt
  exfalso
  have hd := hder r hmem (x, f) hx
  have hneg' : Term.eval f (Φ r) < 0 := hneg _ (hdom r hmem) (by rw [hΦr]; exact heq)
  rw [hasDerivWithinAt_iff_tendsto_slope] at hd
  have hset : Set.Icc (0:ℝ) r \ {r} = Set.Ico 0 r := by
    ext t; simp [lt_iff_le_and_ne]
  rw [hset, nhdsWithin_Ico_eq_nhdsLT hrpos] at hd
  have hge : 0 ≤ Term.eval f (Φ r) := by
    refine ge_of_tendsto hd ?_
    filter_upwards [Ioo_mem_nhdsLT hrpos] with t ht
    rw [slope_def_field]
    have h1 : Φ t x ≤ c := hle _ (hdom t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    have h2 : (fun s => Φ s x) r = c := by simp only; rw [hΦr]; exact heq
    simp only at h2 ⊢
    rw [h2]
    apply div_nonneg_of_nonpos <;> linarith [ht.2]
  linarith

/-- **The response flow after a legal prefix.** As `gresp_final`, with a prefix of guarded
segments (each flow followed by its switch test) run before the final flow in `qs`; the prefix
is declared, chained, starts at `q` and ends in `qs`. -/
theorem gresp_final_pre {G : SearchGraph (Var n)} {q qs : ℕ} {ms : RMode (Var n)}
    (hm : G.modeAt qs = some ms)
    (pre : List (ℕ × RMode (Var n) × REdge (Var n)))
    (halign : ∀ s ∈ pre, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1)
    (hchain : List.IsChain (fun a b => a.2.2.tgt = b.1) pre)
    (hhead : ∀ s, pre.head? = some s → s.1 = q) (hlast : qfOf pre q = qs)
    {P : Program (Var n)} {Post' : Formula (Var n)} {post : ℕ → Formula (Var n)}
    {σ : State (Var n)}
    (hfa : Formula.sat (faModal (Equiv.refl (Var n)) P
      (bigSeq (pre.map gseg ++ [Program.ode ms.sys ms.dom])) Post') σ)
    (hnb : NonblockingAt G qs Post' post) : GResp G q P post σ := by
  intro ν hν
  rw [faModal_sat] at hfa
  obtain ⟨μ, hrun, hpost⟩ := hfa ν hν
  rw [Program.rename_refl] at hrun
  obtain ⟨e, he, hleg, hp⟩ := hnb μ hpost
  refine ⟨pre ++ [(qs, ms, e)], ?_, ?_, ?_, μ, ?_, ?_⟩
  · intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact halign s hs
    · rw [List.mem_singleton] at hs; subst hs; exact ⟨hm, he⟩
  · refine List.IsChain.append hchain (by simp) ?_
    intro x hx y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    have : qfOf pre q = x.2.2.tgt := by
      simp [qfOf, Option.mem_def.mp hx]
    simpa [← this] using hlast
  · intro s hs
    rcases pre with - | ⟨r, rs⟩
    · simp at hs; subst hs; simp [qfOf] at hlast; exact hlast.symm
    · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hs
      subst hs; exact hhead _ rfl
  · -- split the run: the prefix, then the final flow; append its switch test
    have key : ∀ (L : List (Program (Var n))) (A B : Program (Var n)) {x y : State (Var n)},
        Program.sem (bigSeq (L ++ [A])) x y → (∀ z, Program.sem A z y →
          Program.sem B z y) → Program.sem (bigSeq (L ++ [B])) x y := by
      intro L
      induction L with
      | nil =>
          intro A B x y h hAB
          obtain ⟨z, hA, hz, -⟩ := h
          subst hz
          exact ⟨z, hAB x hA, rfl, trivial⟩
      | cons c cs ih =>
          intro A B x y h hAB
          obtain ⟨z, hc, hrest⟩ := h
          exact ⟨z, hc, ih A B hrest hAB⟩
    rw [List.map_append, List.map_singleton]
    exact key _ _ _ hrun (fun z hz => sem_gseg.mpr ⟨hz, hleg⟩)
  · have : qfOf (pre ++ [(qs, ms, e)]) q = e.tgt := by simp [qfOf]
    rw [this]; exact hp

/-- **The guarded reposition prefix.** `faModalB_repoPrefix` with the switch test after the
hop: if the hop (a frozen-left run of a right mode) ends where the right-only formula `γ`
(the entered mode's guard) holds, the response program carries the test `?γ` between the
hop and the continuation. The hop's end state, replayed after the left run, has the same
right coordinates, so the test passes there. -/
theorem faModalB_repoPrefixG {fL fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domL domR γ : Formula (Var n)} {φ : Formula (Var n)} {Q : Program (Var n)}
    {a : Fin n} {dt : ℝ} {ω₀ : State (Var n)}
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hlam : lam.fv ⊆ range Rv)
    (hdomR : domR.fv ⊆ range Rv) (hγ : γ.fv ⊆ range Rv)
    (hω₀tg : ω₀ ((Side.Aux, a) : Var n) = 0)
    (hR : ∃ ρ₁, Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fR lam)
        (Formula.and domL domR)) ω₀ ρ₁ ∧ Formula.sat φ ρ₁ ∧ Formula.sat γ ρ₁)
    (hQ : ∀ σ, Formula.sat φ σ → σ ((Side.Aux, a) : Var n) = 0 →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        Q φ ((Side.Aux, a) : Var n) dt σ) :
    faModalB (Equiv.refl (Var n))
      (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
      (Program.seq (Program.seq
        (Program.ode (jointSys (fun _ => Term.const 0) fR lam) (Formula.and domL domR))
        (Program.test γ)) Q)
      φ ((Side.Aux, a) : Var n) dt ω₀ := by
  intro ν hplant
  obtain ⟨ρ₁, hhop, hρ₁sat, hρ₁γ⟩ := hR
  have hrights : ∀ i : Fin n, ν (Rv i) = ω₀ (Rv i) := by
    intro i
    refine sem_ode_mask hplant.1 ?_
    intro hb
    rcases clk_boundSet_sub _ _ (by simpa [ODESystem.boundSet] using hb) with hx | hx
    · obtain ⟨j, hj⟩ := leftBlock_boundSet_sub fL hx
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
    · rw [Set.mem_singleton_iff] at hx
      exact absurd hx (by simp [Rv, Prod.ext_iff])
  have hνdomL : Formula.sat domL ν := by
    obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hplant.1
    rw [← hΦr]
    exact hdom r (Set.right_mem_Icc.mpr hr)
  have hreplay := sem_frozen_replay hfR hlam hdomL hdomR hhop hrights hνdomL
  have hρ₁eq : rpatch ω₀ ρ₁ = ρ₁ := by
    funext v
    obtain ⟨s, i⟩ := v
    cases s with
    | R => rfl
    | L =>
        show ω₀ (Lv i) = ρ₁ (Lv i)
        exact (frozen_left_constant hhop i).symm
    | Aux =>
        show ω₀ ((Side.Aux, i) : Var n) = ρ₁ ((Side.Aux, i) : Var n)
        exact (sem_ode_mask hhop (aux_not_jointSys_bound _ _ _ i)).symm
  have hplant' := plantT_rpatch hfL hdomL (ρ := ρ₁) hplant
  rw [hρ₁eq] at hplant'
  have hρ₁tg : ρ₁ ((Side.Aux, a) : Var n) = 0 := by
    rw [sem_ode_mask hhop (aux_not_jointSys_bound _ _ _ a)]
    exact hω₀tg
  obtain ⟨μ, hQμSem, hQμφ⟩ := hQ ρ₁ hρ₁sat hρ₁tg (rpatch ν ρ₁) hplant'
  have hγpatch : Formula.sat γ (rpatch ν ρ₁) := by
    refine (Formula.coincidence γ (fun v hv => ?_)).mpr hρ₁γ
    obtain ⟨i, rfl⟩ := hγ hv
    rfl
  refine ⟨μ, ?_, hQμφ⟩
  rw [Program.rename_refl] at hQμSem ⊢
  exact ⟨rpatch ν ρ₁, ⟨rpatch ν ρ₁, hreplay, rfl, hγpatch⟩, hQμSem⟩

/-- **The response flow, then a switch chosen at a point of the run, or nothing.** The most
general one-flow response: for every left run and every end state `μ` of the certified
response flow, either the postcondition already holds for the current mode at the left run's
end (`ν`, the right makes no step), or the right runs the same mode's flow from `ν` to some
`κ` (typically `μ` itself, or a point of the same run) and switches there into an enabled
successor. -/
theorem gresp_final_choose {G : SearchGraph (Var n)} {qs : ℕ} {ms : RMode (Var n)}
    (hm : G.modeAt qs = some ms)
    {P : Program (Var n)} {Post' : Formula (Var n)} {post : ℕ → Formula (Var n)}
    {σ : State (Var n)}
    (hfa : Formula.sat (faModal (Equiv.refl (Var n)) P
      (bigSeq [Program.ode ms.sys ms.dom]) Post') σ)
    (hpick : ∀ ν μ, Program.sem P σ ν → Program.sem (Program.ode ms.sys ms.dom) ν μ →
      Formula.sat Post' μ →
      Formula.sat (post qs) ν ∨
        ∃ e ∈ G.edgesFrom qs, ∃ κ, Program.sem (Program.ode ms.sys ms.dom) ν κ ∧
          SwitchLegal e κ ∧ Formula.sat (post e.tgt) κ) :
    GResp G qs P post σ := by
  intro ν hν
  have hfa' := (faModal_sat _ _ _ _ _).mp hfa ν hν
  obtain ⟨μ, hrun, hpost⟩ := hfa'
  rw [Program.rename_refl] at hrun
  simp only [bigSeq] at hrun
  obtain ⟨κ0, hflow, hκ, -⟩ := hrun
  subst hκ
  rcases hpick ν κ0 hν hflow hpost with hidle | ⟨e, he, κ, hκrun, hleg, hp⟩
  · refine ⟨[], by simp, by simp, by simp, ν, ?_, by simpa [qfOf] using hidle⟩
    show Program.sem (Program.test Formula.tt) ν ν
    exact ⟨rfl, trivial⟩
  · refine ⟨[(qs, ms, e)], ?_, by simp, by simp, κ, ?_, ?_⟩
    · intro s hs
      rw [List.mem_singleton] at hs
      subst hs
      exact ⟨hm, he⟩
    · simp only [List.map_cons, List.map_nil, bigSeq]
      exact ⟨κ, sem_gseg.mpr ⟨hκrun, hleg⟩, rfl, trivial⟩
    · simpa [qfOf] using hp

/-- **Stopping a run at a level.** If a coordinate goes from at most `c` to at least `c`
along a run, the run can be cut where the coordinate equals `c` (intermediate value
theorem on the continuous trajectory); the cut run is a run of the same program, ends in its
domain, and leaves every unbound variable at its start value. -/
theorem ode_run_hits {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {ν μ : State (Var n)} (h : Program.sem (Program.ode sys dom) ν μ)
    {x : Var n} {f : Term (Var n)} (hx : (x, f) ∈ sys) {c : ℝ}
    (hlo : ν x ≤ c) (hhi : c ≤ μ x) :
    ∃ κ, Program.sem (Program.ode sys dom) ν κ ∧ κ x = c ∧ Formula.sat dom κ ∧
      ∀ y, y ∉ sys.bound → κ y = ν y := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  have H : ODESol sys dom ν r Φ := ⟨hr, hΦ0, hder, hmask, hdom⟩
  have hcont : ContinuousOn (fun t => Φ t x) (Set.Icc 0 r) :=
    fun t ht => (hder t ht (x, f) hx).continuousWithinAt
  obtain ⟨t, ht, hct⟩ := intermediate_value_Icc hr hcont
    ⟨by simp only [hΦ0]; exact hlo, by simp only [hΦr]; exact hhi⟩
  exact ⟨Φ t, DLCalTiming.sem_ode_restrict H ht.1 ht.2, hct, hdom t ht, fun y hy => hmask t ht y hy⟩

/-- **The guarded reposition prefix with an arbitrary landing predicate.** A right-only hop
(the mode's own program) whose end satisfies the landing predicate `A` and the right-only
switch condition `γ`, followed by a continuation coupled from every `A`-state with the clock
at 0: the response program carries the test `?γ` after the hop. -/
theorem hopAG {fL fR : Fin n → Term (Var n)} {lam : Term (Var n)}
    {domL domR γ φ : Formula (Var n)} {Q : Program (Var n)} {a : Fin n} {dt : ℝ}
    {ω₀ : State (Var n)}
    (hfL : ∀ i, (fL i).fv ⊆ range Lv) (hdomL : domL.fv ⊆ range Lv)
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hlam : lam.fv ⊆ range Rv)
    (hdomR : domR.fv ⊆ range Rv) (hγ : γ.fv ⊆ range Rv)
    (hω₀tg : ω₀ ((Side.Aux, a) : Var n) = 0) (hdomLω : Formula.sat domL ω₀)
    (A : State (Var n) → Prop)
    (hR : ∃ ρ₁, Program.sem (Program.ode (rightBlock fR lam) domR) ω₀ ρ₁ ∧ A ρ₁ ∧
      Formula.sat γ ρ₁)
    (hQ : ∀ σ, A σ → σ ((Side.Aux, a) : Var n) = 0 →
      faModalB (Equiv.refl (Var n))
        (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
        Q φ ((Side.Aux, a) : Var n) dt σ) :
    faModalB (Equiv.refl (Var n))
      (Program.ode (DLCalTiming.clk ((Side.Aux, a) : Var n) (leftBlock fL)) domL)
      (Program.seq (Program.seq (Program.ode (rightBlock fR lam) domR) (Program.test γ)) Q)
      φ ((Side.Aux, a) : Var n) dt ω₀ := by
  intro ν hplant
  obtain ⟨ρ₁, hrun0, hρ₁A, hρ₁γ⟩ := hR
  have hhop := hop_run_toJoint hfR hlam hdomL hdomLω hrun0
  have hrights : ∀ i : Fin n, ν (Rv i) = ω₀ (Rv i) := by
    intro i
    refine sem_ode_mask hplant.1 ?_
    intro hb
    rcases clk_boundSet_sub _ _ (by simpa [ODESystem.boundSet] using hb) with hx | hx
    · obtain ⟨j, hj⟩ := leftBlock_boundSet_sub fL hx
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
    · rw [Set.mem_singleton_iff] at hx
      exact absurd hx (by simp [Rv, Prod.ext_iff])
  have hνdomL : Formula.sat domL ν := by
    obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hplant.1
    rw [← hΦr]
    exact hdom r (Set.right_mem_Icc.mpr hr)
  have hreplay := sem_frozen_replay hfR hlam hdomL hdomR hhop hrights hνdomL
  have hρ₁eq : rpatch ω₀ ρ₁ = ρ₁ := by
    funext v
    obtain ⟨s, i⟩ := v
    cases s with
    | R => rfl
    | L =>
        show ω₀ (Lv i) = ρ₁ (Lv i)
        exact (frozen_left_constant hhop i).symm
    | Aux =>
        show ω₀ ((Side.Aux, i) : Var n) = ρ₁ ((Side.Aux, i) : Var n)
        exact (sem_ode_mask hhop (aux_not_jointSys_bound _ _ _ i)).symm
  have hplant' := plantT_rpatch hfL hdomL (ρ := ρ₁) hplant
  rw [hρ₁eq] at hplant'
  have hρ₁tg : ρ₁ ((Side.Aux, a) : Var n) = 0 := by
    rw [sem_ode_mask hhop (aux_not_jointSys_bound _ _ _ a)]
    exact hω₀tg
  obtain ⟨μ, hQμSem, hQμφ⟩ := hQ ρ₁ hρ₁A hρ₁tg (rpatch ν ρ₁) hplant'
  have hγpatch : Formula.sat γ (rpatch ν ρ₁) := by
    refine (Formula.coincidence γ (fun v hv => ?_)).mpr hρ₁γ
    obtain ⟨i, rfl⟩ := hγ hv
    rfl
  refine ⟨μ, ?_, hQμφ⟩
  rw [Program.rename_refl] at hQμSem ⊢
  exact ⟨rpatch ν ρ₁, ⟨rpatch ν ρ₁, joint_run_toR hfR hlam hreplay, rfl, hγpatch⟩, hQμSem⟩

/-- **A linear coordinate, explicitly.** If along a run the coordinate `x` has field
`k (c − x)` on the domain, the run ends at `c + (x₀ − c) e^{−k r}` for its duration `r ≥ 0`
(`(c − x) e^{k t}` is constant along the run). -/
theorem ode_linear_coord {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {ν μ : State (Var n)} (h : Program.sem (Program.ode sys dom) ν μ)
    {x : Var n} {f : Term (Var n)} (hx : (x, f) ∈ sys) (k c : ℝ)
    (hf : ∀ s, Formula.sat dom s → Term.eval f s = k * (c - s x)) :
    ∃ r, 0 ≤ r ∧ μ x = c + (ν x - c) * Real.exp (-(k * r)) := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, -, hdom⟩ := h
  refine ⟨r, hr, ?_⟩
  set H : ℝ → ℝ := fun t => (c - Φ t x) * Real.exp (k * t) with hH
  have hHder : ∀ t ∈ Set.Icc (0:ℝ) r, HasDerivWithinAt H 0 (Set.Icc 0 r) t := by
    intro t ht
    have h1 := hder t ht (x, f) hx
    rw [hf _ (hdom t ht)] at h1
    have h2 : HasDerivWithinAt (fun u => Real.exp (k * u)) (Real.exp (k * t) * (k * 1))
        (Set.Icc 0 r) t :=
      (((hasDerivAt_id t).const_mul k).exp).hasDerivWithinAt
    exact ((h1.const_sub c).mul h2).congr_deriv (by ring)
  have hcont : ContinuousOn H (Set.Icc 0 r) := fun t ht => (hHder t ht).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht =>
    (hHder t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    r ⟨hr, le_refl r⟩
  simp only [hH, hΦ0, hΦr, mul_zero, Real.exp_zero, mul_one] at hconst
  have hexp : Real.exp (k * r) * Real.exp (-(k * r)) = 1 := by
    rw [← Real.exp_add]; simp
  have : c - μ x = (c - ν x) * Real.exp (-(k * r)) := by
    calc c - μ x = (c - μ x) * (Real.exp (k * r) * Real.exp (-(k * r))) := by rw [hexp, mul_one]
      _ = ((c - μ x) * Real.exp (k * r)) * Real.exp (-(k * r)) := by ring
      _ = (c - ν x) * Real.exp (-(k * r)) := by rw [hconst]
  linarith

/-- A predicate preserved by every clocked piece is preserved by a `k`-piece window. -/
theorem windowSeg_preserve (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (tg : Var n) (dt : ℝ) (P : State (Var n) → Prop)
    (hpiece : ∀ σ ν, P σ → Program.sem (clockedSeg leftSys domL tg dt) σ ν → P ν) :
    ∀ (k : ℕ) (σ ν : State (Var n)), P σ →
      Program.sem (windowSeg leftSys domL tg dt k) σ ν → P ν := by
  intro k
  induction k with
  | zero =>
      intro σ ν hP h
      simp only [windowSeg, List.replicate_zero, bigSeq, sem_test] at h
      obtain ⟨rfl, -⟩ := h
      exact hP
  | succ k ih =>
      intro σ ν hP h
      simp only [windowSeg, List.replicate_succ, bigSeq] at h
      obtain ⟨mid, hseg, hrest⟩ := h
      exact ih mid ν (hpiece σ mid hP hseg) hrest

/-- Right-only facts survive a left program that binds no right coordinate. -/
theorem sat_framed {P : Program (Var n)} {φ : Formula (Var n)}
    (hdis : ∀ x ∈ φ.fv, x ∉ P.bv) {σ ν : State (Var n)} (hrun : Program.sem P σ ν) :
    Formula.sat φ σ ↔ Formula.sat φ ν :=
  Formula.coincidence φ (fun x hx => Program.bound_effect P hrun x (hdis x hx))

/-- The bound variables of a left program inside `{tg} ∪ range Lv` miss every right
coordinate. -/
theorem notMem_bv_of_vars {P : Program (Var n)} {b : Fin n}
    (hP : Program.vars P ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv)
    {φ : Formula (Var n)} (hφ : φ.fv ⊆ range Rv) : ∀ x ∈ φ.fv, x ∉ P.bv := by
  intro x hx hb
  obtain ⟨i, rfl⟩ := hφ hx
  rcases hP (Or.inr hb) with h | ⟨j, hj⟩
  · exact absurd (Set.mem_singleton_iff.mp h) (by simp [Rv, Prod.ext_iff])
  · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-! ## The loop steps over the guarded automaton -/

/-- **The guarded step, region-carrying chain.** The provider's guarded obligation lifts to
one loop step against `star (rightAutomatonBody G mv)`, whatever the guards are. -/
theorem hstep_single_GR (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ)
    (F env : Formula (Var n)) (regions : ℕ → Formula (Var n)) (P : Program (Var n))
    (hF : mv ∉ F.fv) (henv : mv ∉ env.fv) (hregf : ∀ q', mv ∉ (regions q').fv)
    (hframe : FramesMv P mv) (hqlt : q < G.modes.length)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ))
    (hresp : GResp G q P (fun qf => Formula.and (Formula.and F env) (regions qf)) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) P
      (Program.star (rightAutomatonBody G mv))
      (phiInvR F env mv regions G.modes.length)) σ := by
  rw [faModal_sat]
  intro ν hleft
  obtain ⟨segs, halign, hchain, hhead, μ, hrun, hpostμ⟩ := hresp ν hleft
  have hνmv : ν mv = (q : ℝ) := (hframe σ ν hleft).trans hmvq
  have hstar := guarded_rights_bridge G mv hfresh hgf segs halign hchain q hhead hrun
  have hupdν : Function.update ν mv (q : ℝ) = ν := by
    funext x
    by_cases hx : x = mv
    · subst hx; rw [Function.update_self, hνmv]
    · rw [Function.update_of_ne hx]
  rw [hupdν] at hstar
  refine ⟨Function.update μ mv ((qfOf segs q) : ℝ),
    by rw [Program.rename_refl]; exact hstar, ?_⟩
  obtain ⟨⟨hFμ, henvμ⟩, hregμ⟩ := hpostμ
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rwa [(Formula.coincidence F (fun y hy =>
      Function.update_of_ne (fun hc => hF (by rw [← hc]; exact hy)) _ _) :
        Formula.sat F _ ↔ Formula.sat F μ)]
  · rwa [(Formula.coincidence env (fun y hy =>
      Function.update_of_ne (fun hc => henv (by rw [← hc]; exact hy)) _ _) :
        Formula.sat env _ ↔ Formula.sat env μ)]
  · rw [sat_mvRegion]
    refine ⟨qfOf segs q, qfOf_lt G hlt segs halign q hqlt,
      Function.update_self mv _ μ, ?_⟩
    rwa [(Formula.coincidence (regions (qfOf segs q)) (fun y hy =>
      Function.update_of_ne (fun hc => hregf _ (by rw [← hc]; exact hy)) _ _) :
        Formula.sat (regions (qfOf segs q)) _ ↔ _)]

/-- **The assembled guarded step, region-carrying chain** (the guarded counterpart of
`hstep_assembled_multiR`): the provider receives the start mode's region and owes, per left
window, the guarded obligation. -/
theorem hstep_assembled_GR (G : SearchGraph (Var n)) (mv : Var n)
    (F env : Formula (Var n)) (regions : ℕ → Formula (Var n))
    (leftProgs : List (Program (Var n))) (hF : mv ∉ F.fv) (henv : mv ∉ env.fv)
    (hregf : ∀ q', mv ∉ (regions q').fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframes : ∀ P ∈ leftProgs, FramesMv P mv)
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ → Formula.sat (regions q) σ →
      GResp G q P (fun qf => Formula.and (Formula.and F env) (regions qf)) σ) :
    ∀ σ, Formula.sat (phiInvR F env mv regions G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv))
        (phiInvR F env mv regions G.modes.length)) σ := by
  intro σ hφ'
  obtain ⟨q, hqlt, hmvq, hregq⟩ := sat_mvRegion.mp hφ'.2
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (Program.star (rightAutomatonBody G mv))
    (phiInvR F env mv regions G.modes.length) σ leftProgs ?_
  intro P hP
  exact hstep_single_GR G mv q F env regions P hF henv hregf (hframes P hP) hqlt
    hfresh hgf hlt hmvq (Hmulti P hP q hqlt σ hmvq hφ'.1 hregq)

/-- **The guarded step, `mvValid` chain.** -/
theorem hstep_single_GF (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ)
    (F env : Formula (Var n)) (P : Program (Var n))
    (hF : mv ∉ F.fv) (henv : mv ∉ env.fv)
    (hframe : FramesMv P mv) (hqlt : q < G.modes.length)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ))
    (hresp : GResp G q P (fun _ => Formula.and F env) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) P
      (Program.star (rightAutomatonBody G mv)) (phiInvF F env mv G.modes.length)) σ := by
  rw [faModal_sat]
  intro ν hleft
  obtain ⟨segs, halign, hchain, hhead, μ, hrun, hpostμ⟩ := hresp ν hleft
  have hνmv : ν mv = (q : ℝ) := (hframe σ ν hleft).trans hmvq
  have hstar := guarded_rights_bridge G mv hfresh hgf segs halign hchain q hhead hrun
  have hupdν : Function.update ν mv (q : ℝ) = ν := by
    funext x
    by_cases hx : x = mv
    · subst hx; rw [Function.update_self, hνmv]
    · rw [Function.update_of_ne hx]
  rw [hupdν] at hstar
  refine ⟨Function.update μ mv ((qfOf segs q) : ℝ),
    by rw [Program.rename_refl]; exact hstar, ?_⟩
  obtain ⟨hFμ, henvμ⟩ := hpostμ
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rwa [(Formula.coincidence F (fun y hy =>
      Function.update_of_ne (fun hc => hF (by rw [← hc]; exact hy)) _ _) :
        Formula.sat F _ ↔ Formula.sat F μ)]
  · rwa [(Formula.coincidence env (fun y hy =>
      Function.update_of_ne (fun hc => henv (by rw [← hc]; exact hy)) _ _) :
        Formula.sat env _ ↔ Formula.sat env μ)]
  · rw [sat_mvValid]
    exact ⟨qfOf segs q, qfOf_lt G hlt segs halign q hqlt, Function.update_self mv _ μ⟩

/-- **The assembled guarded step, `mvValid` chain.** -/
theorem hstep_assembled_GF (G : SearchGraph (Var n)) (mv : Var n)
    (F env : Formula (Var n))
    (leftProgs : List (Program (Var n))) (hF : mv ∉ F.fv) (henv : mv ∉ env.fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframes : ∀ P ∈ leftProgs, FramesMv P mv)
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ →
      GResp G q P (fun _ => Formula.and F env) σ) :
    ∀ σ, Formula.sat (phiInvF F env mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv)) (phiInvF F env mv G.modes.length)) σ := by
  intro σ hφ'
  obtain ⟨q, hqlt, hmvq⟩ := sat_mvValid.mp hφ'.2
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (Program.star (rightAutomatonBody G mv))
    (phiInvF F env mv G.modes.length) σ leftProgs ?_
  intro P hP
  exact hstep_single_GF G mv q F env P hF henv (hframes P hP) hqlt hfresh hgf hlt hmvq
    (Hmulti P hP q hqlt σ hmvq hφ'.1)

/-- The per-left-mode guarded step for `theorem3_modeKeyed`, region-carrying chain. -/
theorem hstepMode_GR (G : SearchGraph (Var n)) (mv : Var n)
    (F env : Formula (Var n)) (regions : ℕ → Formula (Var n)) (P : Program (Var n))
    (hF : mv ∉ F.fv) (henv : mv ∉ env.fv) (hregf : ∀ q', mv ∉ (regions q').fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframe : FramesMv P mv)
    (H : ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and F env) (regions q)) σ →
      GResp G q P (fun qf => Formula.and (Formula.and F env) (regions qf)) σ) :
    ∀ σ, Formula.sat (Formula.and (Formula.and F env) (mvRegion mv regions G.modes.length)) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) P (Program.star (rightAutomatonBody G mv))
        (Formula.and (Formula.and F env) (mvRegion mv regions G.modes.length))) σ := by
  intro σ hσ
  obtain ⟨q, hq, hmvq, hreg⟩ := sat_mvRegion.mp hσ.2
  exact hstep_single_GR G mv q F env regions P hF henv hregf hframe hq hfresh hgf hlt hmvq
    (H q hq σ hmvq ⟨hσ.1, hreg⟩)

/-- The per-left-mode guarded step for `theorem3_modeKeyed`, `mvValid` chain. -/
theorem hstepMode_GF (G : SearchGraph (Var n)) (mv : Var n)
    (F env : Formula (Var n)) (P : Program (Var n))
    (hF : mv ∉ F.fv) (henv : mv ∉ env.fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (hgf : GuardsFresh G mv)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframe : FramesMv P mv)
    (H : ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ → GResp G q P (fun _ => Formula.and F env) σ) :
    ∀ σ, Formula.sat (Formula.and (Formula.and F env) (mvValid mv G.modes.length)) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) P (Program.star (rightAutomatonBody G mv))
        (Formula.and (Formula.and F env) (mvValid mv G.modes.length))) σ := by
  intro σ hσ
  obtain ⟨q, hq, hmvq⟩ := sat_mvValid.mp hσ.2
  exact hstep_single_GF G mv q F env P hF henv hframe hq hfresh hgf hlt hmvq
    (H q hq σ hmvq hσ.1)

/-! ## Footprints of the guarded automaton -/

/-- A mode step touches `mv`, the mode's own footprint and the outgoing guards'. -/
theorem vars_modeStepG_sub (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ)
    (m : RMode (Var n)) (S : Set (Var n))
    (hg : ∀ e ∈ G.edgesFrom q, e.guard.fv ⊆ S) :
    Program.vars (modeStep G mv q m)
      ⊆ {mv} ∪ (m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv) ∪ S := by
  intro x hx
  rcases vars_seq_sub _ _ hx with hx | hx
  · rw [vars_test_eq] at hx
    simp only [modeIs, Formula.fv, Term.fv] at hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact absurd hx (by simp)
  · rcases vars_seq_sub _ _ hx with hx | hx
    · exact Or.inl (Or.inr (vars_ode_sub _ _ hx))
    · refine vars_bigChoiceP_sub _ _ ?_ hx
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨e, hef, rfl⟩ := hp
      intro y hy
      rcases vars_seq_sub _ _ hy with hy | hy
      · rw [vars_test_eq] at hy
        exact Or.inr (hg e hef hy)
      · rcases vars_assign_sub mv _ hy with hy | hy
        · exact Or.inl (Or.inl hy)
        · exact absurd hy (by simp [Term.fv])

/-- **The guarded right automaton touches only `mv` and right coordinates**, given that the
modes' footprints and the declared guards are right-side (no `htt`). -/
theorem vars_bodyG_sub (G : SearchGraph (Var n)) (mv : Var n)
    (hgR : GuardsRight G)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    Program.vars (rightAutomatonBody G mv) ⊆ {mv} ∪ range Rv := by
  refine vars_bigChoiceP_sub _ _ ?_
  intro p hp
  simp only [List.mem_filterMap, List.mem_range] at hp
  obtain ⟨q, -, hq⟩ := hp
  rcases hm : G.modeAt q with _ | m
  · rw [hm] at hq; simp at hq
  · rw [hm] at hq
    simp only [Option.map_some, Option.some.injEq] at hq
    subst hq
    intro x hx
    rcases vars_modeStepG_sub G mv q m (range Rv) (hgR q) hx with (hx | hx) | hx
    · exact Or.inl hx
    · exact Or.inr (hRv q m hm hx)
    · exact Or.inr hx

/-- The guarded counterpart of `hddF_multiR`. -/
theorem hddF_multiR_G (Gr : SearchGraph (Var n)) (a b : Fin n) (dt : ℝ)
    (leftData : List (Formula (Var n) × (Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (regions : ℕ → Formula (Var n))
    (ϕinv : RFormula (Var n)) (domL domR : Formula (Var n)) (hab : a ≠ b)
    (hgR : GuardsRight Gr)
    (hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hL : ∀ d ∈ leftData, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
      d.2.2.1.fv ⊆ range Lv)
    (hreg : ∀ q < Gr.modes.length, (regions q).fv ⊆ range Rv)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv)
    (hdomLv : domL.fv ⊆ range Lv) (hdomRv : domR.fv ⊆ range Rv) :
    Disjoint (faShape (Program.star (bigChoice (leftData.map (fun d =>
          gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 ((Side.Aux, b) : Var n) dt d.2.2.2))))
        (Program.star (rightAutomatonBody Gr ((Side.Aux, a) : Var n)))
        (RFormula.and (RFormula.and ϕinv (envLR domL domR))
          (mvRegionR ((Side.Aux, a) : Var n) regions Gr.modes.length))).varsL
      (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (leftData.map (fun d =>
          gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 ((Side.Aux, b) : Var n) dt d.2.2.2))))
        (Program.star (rightAutomatonBody Gr ((Side.Aux, a) : Var n)))
        (RFormula.and (RFormula.and ϕinv (envLR domL domR))
          (mvRegionR ((Side.Aux, a) : Var n) regions Gr.modes.length))).varsR) := by
  rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by intro S; simp]
  refine sides_disjoint a b a hab.symm hab.symm ?_ ?_
  · rw [faShape_varsL', pvars_star']
    refine Set.union_subset ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 b dt d.2.2.2 (hL d hd).1
        (hL d hd).2.1 (hL d hd).2.2
    · intro v hv
      rcases ψmultiR_varsL_sub _ regions Gr.modes.length ϕinv domL domR hv with hv | hv
      · exact Or.inr (hinvL hv)
      · exact Or.inr (hdomLv hv)
  · rw [faShape_varsR', pvars_star']
    refine Set.union_subset ?_ ?_
    · intro v hv
      rcases vars_bodyG_sub Gr _ hgR hRv hv with hv | hv
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
      · exact Or.inr hv
    · intro v hv
      rcases ψmultiR_varsR_sub _ regions Gr.modes.length ϕinv domL domR hreg hv
        with (hv | hv) | (hv | hv)
      · exact Or.inr (hinvR hv)
      · exact Or.inr (hdomRv hv)
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
      · exact Or.inr hv

/-- The guarded counterpart of `hdis_multi` (plain clock-capped windows). -/
theorem hdis_multi_G (Gr : SearchGraph (Var n)) (a b : Fin n) (dt : ℝ)
    (leftData : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (hab : a ≠ b) (hgR : GuardsRight Gr)
    (hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hL : ∀ d ∈ leftData, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv) :
    Disjoint (Program.vars (bigChoice (leftData.map (fun d =>
        windowSeg (leftBlock d.1) d.2.1 ((Side.Aux, b) : Var n) dt d.2.2))))
      (Program.vars ((rightAutomatonBody Gr ((Side.Aux, a) : Var n)).rename
        (Equiv.refl (Var n)))) := by
  refine sides_disjoint a b a hab.symm hab.symm ?_ ?_
  · refine vars_bigChoice_sub _ _ ?_
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    exact vars_windowSegL_sub d.1 d.2.1 b dt d.2.2 (hL d hd).1 (hL d hd).2
  · intro x hx
    rw [Program.rename_refl] at hx
    rcases vars_bodyG_sub Gr _ hgR hRv hx with hx | hx
    · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
    · exact Or.inr hx

/-- The guarded counterpart of `hddF_multiR_plain`. -/
theorem hddF_multiR_plain_G (Gr : SearchGraph (Var n)) (a b : Fin n) (dt : ℝ)
    (leftData : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (regions : ℕ → Formula (Var n))
    (ϕinv : RFormula (Var n)) (domL domR : Formula (Var n)) (hab : a ≠ b)
    (hgR : GuardsRight Gr)
    (hRv : ∀ q m, Gr.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hL : ∀ d ∈ leftData, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv)
    (hreg : ∀ q < Gr.modes.length, (regions q).fv ⊆ range Rv)
    (hinvL : ϕinv.varsL ⊆ range Lv) (hinvR : ϕinv.varsR ⊆ range Rv)
    (hdomLv : domL.fv ⊆ range Lv) (hdomRv : domR.fv ⊆ range Rv) :
    Disjoint (faShape (Program.star (bigChoice (leftData.map (fun d =>
          windowSeg (leftBlock d.1) d.2.1 ((Side.Aux, b) : Var n) dt d.2.2))))
        (Program.star (rightAutomatonBody Gr ((Side.Aux, a) : Var n)))
        (RFormula.and (RFormula.and ϕinv (envLR domL domR))
          (mvRegionR ((Side.Aux, a) : Var n) regions Gr.modes.length))).varsL
      (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice (leftData.map (fun d =>
          windowSeg (leftBlock d.1) d.2.1 ((Side.Aux, b) : Var n) dt d.2.2))))
        (Program.star (rightAutomatonBody Gr ((Side.Aux, a) : Var n)))
        (RFormula.and (RFormula.and ϕinv (envLR domL domR))
          (mvRegionR ((Side.Aux, a) : Var n) regions Gr.modes.length))).varsR) := by
  rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by intro S; simp]
  refine sides_disjoint a b a hab.symm hab.symm ?_ ?_
  · rw [faShape_varsL', pvars_star']
    refine Set.union_subset ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_windowSegL_sub d.1 d.2.1 b dt d.2.2 (hL d hd).1 (hL d hd).2
    · intro v hv
      rcases ψmultiR_varsL_sub _ regions Gr.modes.length ϕinv domL domR hv with hv | hv
      · exact Or.inr (hinvL hv)
      · exact Or.inr (hdomLv hv)
  · rw [faShape_varsR', pvars_star']
    refine Set.union_subset ?_ ?_
    · intro v hv
      rcases vars_bodyG_sub Gr _ hgR hRv hv with hv | hv
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
      · exact Or.inr hv
    · intro v hv
      rcases ψmultiR_varsR_sub _ regions Gr.modes.length ϕinv domL domR hreg hv
        with (hv | hv) | (hv | hv)
      · exact Or.inr (hinvR hv)
      · exact Or.inr (hdomRv hv)
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hv)))
      · exact Or.inr hv

/-- The guarded counterpart of `hd_modeKeyed`. -/
theorem hd_modeKeyed_G (A : LeftAut n) (G : SearchGraph (Var n)) (a b c : Fin n)
    (hba : b ≠ a) (hca : c ≠ a)
    (hwin : ∀ t < A.numModes, Program.vars (A.window t)
      ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv)
    (hgrd : ∀ t < A.numModes, (A.guard t).fv ⊆ range Lv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hgR : GuardsRight G)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    Disjoint (Program.vars (leftAutomatonBody A ((Side.Aux, c) : Var n)))
      (Program.vars ((rightAutomatonBody G ((Side.Aux, a) : Var n)).rename
        (Equiv.refl (Var n)))) := by
  refine sides_disjoint3 a b c hba hca ?_ ?_
  · refine vars_leftAutomatonBody_sub A _ _ ?_ ?_ ?_ hnext
    · exact Or.inl (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))
    · intro t ht x hx
      rcases hwin t ht hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
    · intro t ht x hx
      exact Or.inr (hgrd t ht hx)
  · intro x hx
    rw [Program.rename_refl] at hx
    rcases vars_bodyG_sub G _ hgR hRv hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx

/-- The guarded counterpart of `hddF_modeKeyed`. -/
theorem hddF_modeKeyed_G (A : LeftAut n) (G : SearchGraph (Var n)) (a b c : Fin n)
    (hba : b ≠ a) (hca : c ≠ a)
    (ϕ : ℕ → RFormula (Var n)) (domL domR : Formula (Var n)) (BkR : RFormula (Var n))
    (hwin : ∀ t < A.numModes, Program.vars (A.window t)
      ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv)
    (hgrd : ∀ t < A.numModes, (A.guard t).fv ⊆ range Lv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hgR : GuardsRight G)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hϕL : ∀ m < A.numModes, (ϕ m).varsL ⊆ range Lv)
    (hϕR : ∀ m < A.numModes, (ϕ m).varsR ⊆ range Rv)
    (hdomLv : domL.fv ⊆ range Lv) (hdomRv : domR.fv ⊆ range Rv)
    (hBkL : BkR.varsL = ∅)
    (hBkR : BkR.varsR ⊆ {((Side.Aux, a) : Var n)} ∪ range Rv) :
    Disjoint (faShape (Program.star (leftAutomatonBody A ((Side.Aux, c) : Var n)))
        (Program.star (rightAutomatonBody G ((Side.Aux, a) : Var n)))
        (psiK ((Side.Aux, c) : Var n) ϕ A.numModes domL domR BkR)).varsL
      (Equiv.refl (Var n) '' (faShape (Program.star (leftAutomatonBody A ((Side.Aux, c) : Var n)))
        (Program.star (rightAutomatonBody G ((Side.Aux, a) : Var n)))
        (psiK ((Side.Aux, c) : Var n) ϕ A.numModes domL domR BkR)).varsR) := by
  rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by intro S; simp]
  refine sides_disjoint3 a b c hba hca ?_ ?_
  · rw [faShape_varsL', pvars_star']
    refine Set.union_subset ?_ ?_
    · refine vars_leftAutomatonBody_sub A _ _ ?_ ?_ ?_ hnext
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))
      · intro t ht x hx
        rcases hwin t ht hx with hx | hx
        · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
        · exact Or.inr hx
      · intro t ht x hx
        exact Or.inr (hgrd t ht hx)
    · refine psiK_varsL_sub _ ϕ _ domL domR BkR _ ?_ ?_ ?_ ?_
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))
      · intro m hm x hx; exact Or.inr (hϕL m hm hx)
      · intro x hx; exact Or.inr (hdomLv hx)
      · rw [hBkL]; exact Set.empty_subset _
  · rw [faShape_varsR', pvars_star']
    refine Set.union_subset ?_ ?_
    · intro v hv
      rcases vars_bodyG_sub G _ hgR hRv hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr hv
    · refine psiK_varsR_sub _ ϕ _ domL domR BkR _ ?_ ?_ hBkR
      · intro m hm x hx; exact Or.inr (hϕR m hm hx)
      · intro x hx; exact Or.inr (hdomRv hx)

/-- The guarded counterpart of `notMem_bv_rightAutomatonBody`. -/
theorem notMem_bv_rightAutomatonBody_G (G : SearchGraph (Var n)) (mv : Var n) (x : Var n)
    (hx : x ≠ mv) (hxR : x ∉ range Rv) (hgR : GuardsRight G)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    x ∉ (rightAutomatonBody G mv).bv := by
  intro h
  have hv : x ∈ Program.vars (rightAutomatonBody G mv) := Or.inr h
  rcases vars_bodyG_sub G mv hgR hRv hv with hx' | hx'
  · exact hx (Set.mem_singleton_iff.mp hx')
  · exact hxR hx'

/-- A right mode's lowered guard reads only right coordinates. -/
theorem hostGuard_fv_R (vars : List String) (m : Parse.PMode)
    (hfree : Parse.PForm.namesFree "L_" m.guard = true) :
    (hostGuard vars n Side.R m).fv ⊆ range Rv := by
  intro x hx
  unfold hostGuard at hx
  rcases hlow : Run.lowerF vars n Side.R m.guard with _ | ff
  · rw [hlow] at hx; exact absurd hx (by simp [Formula.fv])
  · rw [hlow, Option.map_some, Option.getD_some] at hx
    exact side_eq_R_mem (Run.lowerF_fv_side (resolvesTo_R vars) hfree hlow x hx)

end RelCertifier
