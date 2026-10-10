/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S2 — the guard-threaded cut lift for the cover chain

13 of the 46 benchmarks certify only with the checked-cut channel: their cover queries
(joint segments and dynamic repositions) are NARROWED by guard-derived cut
atoms, so the emitted UNSATs establish preservation over `dom ∧ cut`, not `dom` — outside
`CoverCertM`'s fields. This file lifts them: the CUT BATON.

## The baton

Cut atoms are ONE-SIDED guard conjuncts (`checkedCut`): left atoms (over `Lv`, from the
left window mode's guard) and right atoms (over `Rv`, from each right mode's guard). Their
O2 verdicts are one-sided Lie checks (own field, other side frozen), so each atom stays
`≤ 0` along BOTH the joint flows (its own side moves the same way) and the frozen-left
dynamic-reposition flows (left atoms are constant, right atoms move under the SAME field
the O2 probe checked). Entry:

* left atoms enter ONCE, at the window start (initial conditioning: admissible starts
  satisfy the window's left guard) and persist through every step;
* right atoms enter at each RIGHT MODE SWITCH — under GUARD-TRIGGERED SWITCHING (the
  target mode's guard holds when its residence begins), the physical automaton semantics
  the tool's O1 already assumes, and the same assumption family as successor-completeness.

The mechanized reach relation `RightReach` does not record switch guards (emitted cover
edges carry `⊤`), so the lifted theorem is stated over the SUBRELATION `RightReachG` —
`RightReach` plus the target-guard fact at each switch. `RightReachG ⊆ RightReach`
(`rightReachG_forget`), so the cut-free battery's theorems subsume their `G`-versions;
the 13 get theirs over `RightReachG`, with guard-triggered switching the documented
model assumption. No change to `Checker/` (no battery invalidation).

## The certificate

`CoverCertMC`: the narrowed preservation fields (exactly the queries the tool sent for
the 13) + per-atom `hiff`/staying facts (from the O2 probes via `CutLift`'s per-route
constructors) + the O1 entry fact (mode guard ⟹ its atoms — `cutAtoms_sat`, kernel).
`pres_multi_cut` threads everything; `check_sound_multi_cut` is the
runner↔theorem connection, mirroring `check_sound_multi`.
-/
import RelCertifier.Proofs.Encoding.CoverMulti
import RelCertifier.Proofs.Soundness.CutLift

namespace RelCertifier
open DL Set

variable {n : ℕ}

/-! ## Cut atom lists (form + safe-side term), the fold, and satisfaction -/

/-- A cut atom: its lowered formula and its `≤ 0`-normal-form term. -/
abbrev CutAtomP (n : ℕ) := Formula (Var n) × Term (Var n)

/-- The conjoined cut formula (the tool's fold shape, `tt`-seeded). -/
def cutF (atoms : List (CutAtomP n)) : Formula (Var n) :=
  atoms.foldl (fun d a => Formula.and d a.1) Formula.tt

/-- All atoms hold. -/
def CutSat (atoms : List (CutAtomP n)) (ν : State (Var n)) : Prop :=
  ∀ a ∈ atoms, Formula.sat a.1 ν

theorem sat_cutF (atoms : List (CutAtomP n)) (ν : State (Var n)) :
    Formula.sat (cutF atoms) ν ↔ CutSat atoms ν := by
  suffices hgen : ∀ (acc : Formula (Var n)),
      Formula.sat (atoms.foldl (fun d a => Formula.and d a.1) acc) ν
        ↔ (Formula.sat acc ν ∧ CutSat atoms ν) by
    unfold cutF
    rw [hgen]
    simp [Formula.sat, CutSat]
  induction atoms with
  | nil => intro acc; simp [CutSat]
  | cons a atoms ih =>
      intro acc
      simp only [List.foldl_cons, ih, Formula.sat, CutSat]
      constructor
      · rintro ⟨⟨hacc, ha⟩, hrest⟩
        exact ⟨hacc, fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hrest x hx⟩
      · rintro ⟨hacc, hall⟩
        exact ⟨⟨hacc, hall a List.mem_cons_self⟩,
          fun x hx => hall x (List.mem_cons_of_mem _ hx)⟩

/-! ## The narrowing lift: a bare-domain run with staying atoms is a narrowed run -/

/-- Per-atom staying along a system/domain pair. -/
def AtomsStay (atoms : List (CutAtomP n)) (sys : ODESystem (Var n))
    (dom : Formula (Var n)) : Prop :=
  ∀ a ∈ atoms, ∀ ν, Term.eval a.2 ν ≤ 0 →
    BoxLe (Program.ode sys dom) (fun ω => Term.eval a.2 ω) ν

/-- Atom forms and terms agree (`≤ 0`-normal form). -/
def AtomsIff (atoms : List (CutAtomP n)) : Prop :=
  ∀ a ∈ atoms, ∀ ν, Formula.sat a.1 ν ↔ Term.eval a.2 ν ≤ 0

/-- A bare-domain run from a cut-satisfying base is a run of the cut-narrowed ode. -/
theorem sem_ode_narrow {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    (atoms : List (CutAtomP n)) (hiff : AtomsIff atoms)
    (hstay : AtomsStay atoms sys dom) {ν μ : State (Var n)}
    (hsem : Program.sem (Program.ode sys dom) ν μ) (hν : CutSat atoms ν) :
    Program.sem (Program.ode sys (Formula.and dom (cutF atoms))) ν μ := by
  refine sem_ode_and_of_stays sys dom (cutF atoms) hsem ?_
  intro r Φ hr hΦ0 hΦr hder hmask hdom t ht
  rw [sat_cutF]
  intro a ha
  have hb := (hiff a ha ν).mp (hν a ha)
  have := boxLe_trace (hstay a ha ν hb) hr hΦ0 hder hmask hdom t ht
  exact (hiff a ha (Φ t)).mpr this

/-- Endpoint persistence: staying atoms hold at the endpoint of a bare-domain run. -/
theorem cutSat_endpoint {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    (atoms : List (CutAtomP n)) (hiff : AtomsIff atoms)
    (hstay : AtomsStay atoms sys dom) {ν μ : State (Var n)}
    (hsem : Program.sem (Program.ode sys dom) ν μ) (hν : CutSat atoms ν) :
    CutSat atoms μ := by
  intro a ha
  have hb := (hiff a ha ν).mp (hν a ha)
  exact (hiff a ha μ).mpr (hstay a ha ν hb μ hsem)

/-! ## The guard-triggered reach relation -/

/-- **`RightReach` under guard-triggered switching.** Identical to `RightReach`, with
the TARGET mode's guard (`Gd e.tgt`) recorded at the state where the target's residence
begins — the physical semantics of guard-triggered mode switching, which the tool's O1
already assumes for every entry. `rightReachG_forget` embeds it into `RightReach`. -/
inductive RightReachG (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n)) :
    Config → State (Var n) → State (Var n) → Prop
  | refl {q B σ ν} : RightReachG G Gd ⟨q, B, σ⟩ ν ν
  | evolve {q B σ ν μ ω} (m : RMode (Var n)) (hm : G.modeAt q = some m)
      (hj : m.jointOK = true) :
      Program.sem (Program.ode m.sys m.dom) ν μ →
      RightReachG G Gd ⟨q, B, SrcSetting.postJ⟩ μ ω → RightReachG G Gd ⟨q, B, σ⟩ ν ω
  | jump {q B σ ν μ ω} (m : RMode (Var n)) (hm : G.modeAt q = some m)
      (hj : m.jointOK = true) (e : REdge (Var n)) (he : e ∈ G.edges) (hsrc : e.src = q)
      (hlt : m.weight < B) :
      Program.sem (Program.ode m.sys m.dom) ν μ →
      Formula.sat e.guard μ →
      Formula.sat (Gd e.tgt) μ →
      RightReachG G Gd ⟨e.tgt, B - m.weight, SrcSetting.postJ⟩ μ ω →
      RightReachG G Gd ⟨q, B, σ⟩ ν ω
  | repositionDynPre {q B ν μ ω} (m : RMode (Var n)) (hm : G.modeAt q = some m)
      (hrepo : m.repoDynPreOK = true) (e : REdge (Var n)) (he : e ∈ G.edges)
      (hsrc : e.src = q) (hB : 0 < B) :
      Program.sem (Program.ode m.dynSys m.dynDomPre) ν μ →
      Formula.sat (Gd e.tgt) μ →
      RightReachG G Gd ⟨e.tgt, B, SrcSetting.preJ⟩ μ ω →
      RightReachG G Gd ⟨q, B, SrcSetting.preJ⟩ ν ω
  | repositionDynPost {q B ν μ ω} (m : RMode (Var n)) (hm : G.modeAt q = some m)
      (hrepo : m.repoDynPostOK = true) (e : REdge (Var n)) (he : e ∈ G.edges)
      (hsrc : e.src = q) (hB : 0 < B) :
      Program.sem (Program.ode m.dynSys m.dynDomPost) ν μ →
      Formula.sat (Gd e.tgt) μ →
      RightReachG G Gd ⟨e.tgt, B, SrcSetting.postJ⟩ μ ω →
      RightReachG G Gd ⟨q, B, SrcSetting.postJ⟩ ν ω

/-- Forgetting the switch guards embeds `RightReachG` into `RightReach`. -/
theorem rightReachG_forget {G : SearchGraph (Var n)} {Gd : ℕ → Formula (Var n)}
    {cfg : Config} {ν ω : State (Var n)}
    (h : RightReachG G Gd cfg ν ω) : RightReach G cfg ν ω := by
  induction h with
  | refl => exact RightReach.refl
  | evolve m hm hj hsem _ ih => exact RightReach.evolve m hm hj hsem ih
  | jump m hm hj e he hsrc hlt hsem hguard _ _ ih =>
      exact RightReach.jump m hm hj e he hsrc hlt hsem hguard ih
  | repositionDynPre m hm hrepo e he hsrc hB hsem _ _ ih =>
      exact RightReach.repositionDynPre m hm hrepo e he hsrc hB hsem ih
  | repositionDynPost m hm hrepo e he hsrc hB hsem _ _ ih =>
      exact RightReach.repositionDynPost m hm hrepo e he hsrc hB hsem ih

/-! ## The cut-carrying certificate -/

/-- **The cut-narrowed multi-component certificate.** `cutL` — the window's left atoms
(entered once, at the window start); `cutR q` — right mode `q`'s atoms (entered at each
switch via `Gd q`). Preservation fields carry the NARROWED domains — exactly the queries
the tool sent for the 13 cut-reliant benchmarks. Staying fields per system kind: the
joint flow and the frozen-left dynamic flows (one-sided O2 covers both; left atoms are
frozen along the dynamic flows). -/
structure CoverCertMC (G : SearchGraph (Var n)) (gs : List (Term (Var n)))
    (Gd : ℕ → Formula (Var n)) (cutL : List (CutAtomP n))
    (cutR : ℕ → List (CutAtomP n)) : Prop where
  hiffL : AtomsIff cutL
  hiffR : ∀ q, AtomsIff (cutR q)
  -- staying along the joint segments (per jointOK mode)
  stayJL : ∀ q m, G.modeAt q = some m → m.jointOK = true → AtomsStay cutL m.sys m.dom
  stayJR : ∀ q m, G.modeAt q = some m → m.jointOK = true → AtomsStay (cutR q) m.sys m.dom
  -- staying along the frozen-left dynamic flows (per dyn-repo mode)
  stayDPreL : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    AtomsStay cutL m.dynSys m.dynDomPre
  stayDPreR : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    AtomsStay (cutR q) m.dynSys m.dynDomPre
  stayDPostL : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    AtomsStay cutL m.dynSys m.dynDomPost
  stayDPostR : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    AtomsStay (cutR q) m.dynSys m.dynDomPost
  -- O1: a right mode's guard implies its atoms (each atom is a guard conjunct)
  entryR : ∀ q ν, Formula.sat (Gd q) ν → CutSat (cutR q) ν
  -- the NARROWED preservation verdicts (the tool's actual queries)
  segPresC : ∀ q m, G.modeAt q = some m → m.jointOK = true →
    SegPreservesAllOn gs m.sys
      (Formula.and m.dom (Formula.and (cutF cutL) (cutF (cutR q))))
  repoDynPresPreC : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
    SegPreservesAllOn gs m.dynSys
      (Formula.and m.dynDomPre (Formula.and (cutF cutL) (cutF (cutR q))))
  repoDynPresPostC : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
    SegPreservesAllOn gs m.dynSys
      (Formula.and m.dynDomPost (Formula.and (cutF cutL) (cutF (cutR q))))
  weightPos : ∀ m ∈ G.modes, 0 < m.weight

/-! ## The threaded preservation -/

/-- Combine the two atom families' narrowing at a run. -/
private theorem sem_ode_narrow2 {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {cutL : List (CutAtomP n)} {cutRq : List (CutAtomP n)}
    (hiffL : AtomsIff cutL) (hiffR : AtomsIff cutRq)
    (hstayL : AtomsStay cutL sys dom) (hstayR : AtomsStay cutRq sys dom)
    {ν μ : State (Var n)} (hsem : Program.sem (Program.ode sys dom) ν μ)
    (hL : CutSat cutL ν) (hR : CutSat cutRq ν) :
    Program.sem (Program.ode sys
      (Formula.and dom (Formula.and (cutF cutL) (cutF cutRq)))) ν μ := by
  have h1 := sem_ode_narrow cutL hiffL hstayL hsem hL
  have hstayR' : AtomsStay cutRq sys (Formula.and dom (cutF cutL)) := by
    intro a ha ν' hb ω hω
    exact hstayR a ha ν' hb ω (sem_ode_dom_and_left hω)
  have h2 := sem_ode_narrow cutRq hiffR hstayR' h1 hR
  refine sem_ode_congr ?_ h2
  intro x
  constructor
  · rintro ⟨⟨hd, hl⟩, hr⟩
    exact ⟨hd, hl, hr⟩
  · rintro ⟨hd, hl, hr⟩
    exact ⟨⟨hd, hl⟩, hr⟩
where
  /-- Weaken an ode's conjoined domain to the left conjunct. -/
  sem_ode_dom_and_left {sys : ODESystem (Var n)} {A B : Formula (Var n)}
      {ν μ : State (Var n)}
      (h : Program.sem (Program.ode sys (Formula.and A B)) ν μ) :
      Program.sem (Program.ode sys A) ν μ := by
    obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
    exact ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, fun t ht => (hdom t ht).1⟩

/-- **The cut-threaded preservation.** Along every guard-triggered right reach from a
jointly-invariant, cut-satisfying entry, every component holds throughout. The baton:
left atoms persist by their staying facts through every flow; right atoms persist
within a mode the same way and RE-ENTER at each switch from the recorded target guard
(O1). -/
theorem pres_multi_cut (G : SearchGraph (Var n)) (gs : List (Term (Var n)))
    (Gd : ℕ → Formula (Var n)) (cutL : List (CutAtomP n))
    (cutR : ℕ → List (CutAtomP n)) (cert : CoverCertMC G gs Gd cutL cutR) :
    ∀ cfg ν ω, RightReachG G Gd cfg ν ω →
      InvAllHolds gs ν → CutSat cutL ν → CutSat (cutR cfg.q) ν →
      InvAllHolds gs ω := by
  intro cfg ν ω hreach
  induction hreach with
  | refl => exact fun h _ _ => h
  | evolve m hm hj hsem _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2 cert.hiffL (cert.hiffR _)
        (cert.stayJL _ m hm hj) (cert.stayJR _ m hm hj) hsem hL hR
      exact ih (cert.segPresC _ m hm hj _ hν _ hrun)
        (cutSat_endpoint cutL cert.hiffL (cert.stayJL _ m hm hj) hsem hL)
        (cutSat_endpoint _ (cert.hiffR _) (cert.stayJR _ m hm hj) hsem hR)
  | jump m hm hj e he hsrc hlt hsem hguard hGd _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2 cert.hiffL (cert.hiffR _)
        (cert.stayJL _ m hm hj) (cert.stayJR _ m hm hj) hsem hL hR
      exact ih (cert.segPresC _ m hm hj _ hν _ hrun)
        (cutSat_endpoint cutL cert.hiffL (cert.stayJL _ m hm hj) hsem hL)
        (cert.entryR _ _ hGd)
  | repositionDynPre m hm hrepo e he hsrc hB hsem hGd _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2 cert.hiffL (cert.hiffR _)
        (cert.stayDPreL _ m hm hrepo) (cert.stayDPreR _ m hm hrepo) hsem hL hR
      exact ih (cert.repoDynPresPreC _ m hm hrepo _ hν _ hrun)
        (cutSat_endpoint cutL cert.hiffL (cert.stayDPreL _ m hm hrepo) hsem hL)
        (cert.entryR _ _ hGd)
  | repositionDynPost m hm hrepo e he hsrc hB hsem hGd _ ih =>
      intro hν hL hR
      have hrun := sem_ode_narrow2 cert.hiffL (cert.hiffR _)
        (cert.stayDPostL _ m hm hrepo) (cert.stayDPostR _ m hm hrepo) hsem hL hR
      exact ih (cert.repoDynPresPostC _ m hm hrepo _ hν _ hrun)
        (cutSat_endpoint cutL cert.hiffL (cert.stayDPostL _ m hm hrepo) hsem hL)
        (cert.entryR _ _ hGd)

/-- The ∀∃-throughout invariant over guard-triggered reaches. -/
def CoexecInvAllThroughoutG (G : SearchGraph (Var n)) (Gd : ℕ → Formula (Var n))
    (gs : List (Term (Var n))) (cfg : Config) (ν : State (Var n)) : Prop :=
  ∀ ω, RightReachG G Gd cfg ν ω → InvAllHolds gs ω

/-- **The runner↔theorem connection, cut-lifted.** The kernel-replayed `decideCovered`
+ the cut-narrowed certificate bundle + the initial conditioning (entry state jointly
invariant, window-left atoms and start-mode atoms satisfied — the admissible-start
guards give both) give the throughout invariant of every component along every
guard-triggered coexecution. -/
theorem check_sound_multi_cut (G : SearchGraph (Var n)) (gs : List (Term (Var n)))
    (Gd : ℕ → Formula (Var n)) (cutL : List (CutAtomP n))
    (cutR : ℕ → List (CutAtomP n)) (cert : CoverCertMC G gs Gd cutL cutR)
    (fuel : ℕ) (cfg : Config) (hchk : decideCovered G fuel cfg = true)
    (ν : State (Var n)) (hinit : InvAllHolds gs ν)
    (hinitL : CutSat cutL ν) (hinitR : CutSat (cutR cfg.q) ν) :
    Covered G cfg ∧ CoexecInvAllThroughoutG G Gd gs cfg ν :=
  ⟨decideCovered_sound G fuel cfg hchk,
   fun ω hreach => pres_multi_cut G gs Gd cutL cutR cert cfg ν ω hreach
     hinit hinitL hinitR⟩

end RelCertifier
