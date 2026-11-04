/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The cover relation (Definition 8) and invariant preservation along a cover

The search graph over right modes, the configurations `(q, B, σ)` of Section 5, and the cover
relation `Covered`: Definition 8 with the retained successors as landing sets (the
committed-subset variants are `CoveredX`, `Checker/CoverX.lean`). A configuration is covered
when one joint segment of `q` finishes the remaining budget (finish case), or a certified
segment of `q` continues into every retained successor (continue case): a joint segment
consumes its weight, a right-only segment consumes nothing. Every joint step strictly
consumes budget (`0 < weight`), and `Covered` is inductive, so every derivation is finite.

`cover_sound` composes the flow certificates (Definition 5, `flow_cert_sound`) and the
non-connection certificates (Definition 6, `nonconn_sound`) along every right response a
cover assembles: from an entry state satisfying the invariant, the invariant holds
throughout. This is the invariant-preservation part of Theorem 1 over a cover (Lemma 5).
`RightReach` follows declared edges only (`jump`), the transition-faithful right response;
`JointBridge.rightReach_is_R_real_run` identifies it with runs of the right automaton, and
`BridgeFinish.theorem3_faithful` states the ∀∃ claim over it. The theorem the paper's
Theorem 3 maps to is `theorem3_of_coverX` (`Proofs/Encoding/Theorem3General.lean`).

Trust boundary: the Z3 `unsat` answers to the local certificate queries are the only leaf;
the cover composition is verified logic.
-/
import RelCertifier.Core.FlowCert
import RelCertifier.Checker.NonConn

namespace RelCertifier

open DL

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## (1) Search-graph / configuration structures (parser-ready) -/

/-- A right mode of the search graph, with the two segment kinds of Definition 3:
* **joint** — `sys` (the joint product field at stretch λ, `jointSys`, Eq. (14)), evolution
  domain `dom`, and the budget `weight` one joint segment consumes; available iff `jointOK`.
* **right-only** — the right flows under the frozen-left field `dynSys` (the right-only
  product, Eq. (15)) while the left is held, consuming **zero** budget; the invariant is kept
  by the right-only flow certificate on the domain of the source setting.

These are the only two kinds: there is no zero-duration right switch (one at a single instant
with no check that the successor's guard holds); every right mode change follows a joint
segment or a right-only flow. The right automaton's edges carry `⊤` guards; that abstraction
is justified for exactly these two step kinds under Assumption 1 (`docs/PAPER-MAPPING.md`,
"The right automaton's ⊤ edge guards"). -/
structure RMode (V : Type*) where
  sys       : ODESystem V
  dom       : Formula V
  weight    : ℕ
  jointOK   : Bool := true
  -- **right-only segment** (Definition 3), kept by the right-only flow certificate
  -- (Definition 5): the right EVOLVES under the frozen-left field `dynSys` (`ṡ_L = 0`), and
  -- `g ≤ 0` is kept along the flow (`DI_nonstrict_domain`, whole-domain `ġ ≤ 0`, Eq. (18)).
  -- `dynDomPre`/`dynDomPost` are the flow domains of the two source settings
  -- (`guardL ∧ evolveL ∧ evolveR` / `evolveL ∧ evolveR`). Zero budget.
  dynSys     : ODESystem V := []
  dynDomPre  : Formula V := .tt
  dynDomPost : Formula V := .tt
  repoDynPreOK  : Bool := false
  repoDynPostOK : Bool := false

/-- A declared right mode change `src → tgt`, enabled by `guard`, flagged `pruned` when a
non-connection certificate (Definition 6) removed it. -/
structure REdge (V : Type*) where
  src    : ℕ
  tgt    : ℕ
  guard  : Formula V
  pruned : Bool

/-- The right transition graph: modes indexed by list position, declared edges. -/
structure SearchGraph (V : Type*) where
  modes : List (RMode V)
  edges : List (REdge V)

/-- **Source setting** σ (Section 3, entry states): has a joint segment occurred yet?
`preJ` (pre-joint) = the left has NOT evolved, so its guard `guardL` still holds; `postJ`
(post-joint) = the left may have evolved, and only `evolveL` constrains it. Monotone: a joint
segment flips `preJ → postJ`, a right-only segment keeps σ, nothing flips back. σ selects
which right-only certificate applies. -/
inductive SrcSetting where
  | preJ
  | postJ
deriving Repr, DecidableEq

/-- A configuration (Section 5): current right mode `q`, remaining budget `B` (a number of
equal joint segments), and source setting `σ` (pre-joint or post-joint). -/
structure Config where
  q : ℕ
  B : ℕ
  σ : SrcSetting
deriving Repr, DecidableEq

/-- Mode lookup by index. -/
def SearchGraph.modeAt (G : SearchGraph V) (q : ℕ) : Option (RMode V) := G.modes[q]?

/-- Retained successors of `q` for a joint segment (Section 4.2): the self-loop `q` plus every
declared edge target not pruned by a non-connection certificate. The self-loop is listed
whether or not it is declared, which only adds obligations. -/
def SearchGraph.retainedSucc (G : SearchGraph V) (q : ℕ) : List ℕ :=
  q :: ((G.edges.filter (fun e => decide (e.src = q) && !e.pruned)).map REdge.tgt)

/-- Retained successors of `q` for a right-only segment (Section 4.2): the declared edge
targets other than `q` that are not pruned, drawn from the candidates `next(q) \ {q}`. A
right-only segment consumes zero budget, so it must leave `q`: staying is covered by the
segment's own flow certificate (the right may linger in `q` with the invariant held), and
requiring the self-loop to be covered would be a budget-neutral cycle. The `∀` over
`exitSucc` (every non-self declared successor, by the completeness clause of Assumption 1) is
Definition 8's continue case for the right-only kind. -/
def SearchGraph.exitSucc (G : SearchGraph V) (q : ℕ) : List ℕ :=
  (G.edges.filter (fun e => decide (e.src = q) && !e.pruned && decide (e.tgt ≠ q))).map REdge.tgt

/-! ## (2) The relational invariant and the certificate interface -/

/-- The relational invariant as one sublevel component `g ≤ 0` over the joint state (Eq. (8)). -/
def InvHolds (g : Term V) (ω : State V) : Prop := Term.eval g ω ≤ 0

/-- A flow segment over `(sys, dom)` preserves the invariant: the `BoxLe` conclusion of
`flow_cert_sound` (Lemma 2; any of its routes, incl. `DI_nonstrict_domain`). -/
def SegPreservesOn (g : Term V) (sys : ODESystem V) (dom : Formula V) : Prop :=
  ∀ ν, InvHolds g ν → BoxLe (Program.ode sys dom) (fun ω => Term.eval g ω) ν

/-- A mode's **joint** segment preserves the invariant (`BoxLe` on the joint product
program): the joint flow certificate of Definition 5. -/
def SegPreserves (g : Term V) (m : RMode V) : Prop := SegPreservesOn g m.sys m.dom

/-- The certificate bundle the cover consumes. Every field is discharged by a certificate
theorem at instantiation:
* `segPres` — each joint-supported (`jointOK`) mode's joint flow certificate (Definition 5,
  `flow_cert_sound`);
* `repoDynPresPre` / `repoDynPresPost` — each right-only mode's right-only flow certificate
  on the domain of its source setting;
* `pruneSound` — each pruned edge's non-connection certificate (Definition 6,
  `nonconn_sound`);
* `weightPos` — every joint segment strictly consumes budget (finiteness).

**Assumption, not proven here:** Assumption 1 — every execution of `mR` ends in the guard of
one of its declared successors (complete). Since only *some* declared successor is known to be
enabled, a right-only step must cover **all** non-self declared successors
(`Covered.stepRepositionDyn*`'s `∀ q' ∈ exitSucc q`). -/
structure CoverCert (G : SearchGraph V) (g : Term V) : Prop where
  segPres      : ∀ q m, G.modeAt q = some m → m.jointOK = true → SegPreserves g m
  -- **the right-only flow certificate** (Definition 5), whole-domain: `SegPreservesOn` over
  -- the frozen-left field `dynSys` (`ṡ_L = 0`), discharged by `flow_cert_sound`'s
  -- `DI_nonstrict_domain` route (`UNSAT(ġ > 0 ∧ dom)`, Eq. (18); not the boundary form of
  -- Eq. (17), which a tangential `t²` touch defeats for a non-strict component). Domains by
  -- source setting: `dynDomPre` (with guardL) / `dynDomPost`.
  repoDynPresPre  : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
      SegPreservesOn g m.dynSys m.dynDomPre
  repoDynPresPost : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
      SegPreservesOn g m.dynSys m.dynDomPost
  pruneSound   : ∀ e ∈ G.edges, e.pruned = true → ∀ q m, G.modeAt q = some m → e.src = q →
      ∀ ν μ, InvHolds g ν → Program.sem (Program.ode m.sys m.dom) ν μ →
        ¬ Formula.sat e.guard μ
  weightPos    : ∀ m ∈ G.modes, 0 < m.weight

/-! ## (3) The cover relation (Covered) and right-response reachability -/

/-- **The cover relation** `Covered`: Definition 8 with the retained successors as landing
sets (the committed-subset variants are `CoveredX`). Its cases:

* **`base`** (finish): the current mode has a joint certificate (`hj`) and one joint segment
  covers the remaining budget (`B ≤ m.weight`). The derivation **ends here** without
  successors: a prefix of this one segment finishes the left cycle.
* **`step`** (continue, joint): strictly more budget than one segment (`m.weight < B`), and
  **every retained successor** is covered at the decremented budget, post-joint.
* **`stepRepositionDynPre/Post`** (continue, right-only): the right-only certificate of the
  matching source setting, `0 < B`, `exitSucc q ≠ []`, and every non-self retained successor
  covered at the same budget and setting. -/
inductive Covered (G : SearchGraph V) : Config → Prop
  -- base/step are the JOINT segments. A joint segment evolves the left, so its successor config
  -- is `postJ` (regardless of the current `σ`). `σ` is monotone: joint flips `preJ→postJ`,
  -- right-only keeps it; nothing resets `postJ→preJ`.
  | base {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hj : m.jointOK = true)
      (hle : B ≤ m.weight) : Covered G ⟨q, B, σ⟩
  | step {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hj : m.jointOK = true)
      (hlt : m.weight < B) :
      (∀ q' ∈ G.retainedSucc q, Covered G ⟨q', B - m.weight, SrcSetting.postJ⟩) →
      Covered G ⟨q, B, σ⟩
  -- **right-only segment**, by source setting: zero budget, `0<B`, `exitSucc≠[]`, every
  -- non-self retained successor covered at the SAME σ (the left is held, so σ is kept);
  -- availability is the whole-domain right-only flow certificate
  -- (`repoDynPreOK`/`repoDynPostOK`). Each constructor concludes only its own σ, so the
  -- pre-joint certificate can never be applied at a `postJ` config.
  | stepRepositionDynPre {q B} (m : RMode V) (hm : G.modeAt q = some m)
      (hrepo : m.repoDynPreOK = true) (hB : 0 < B) (hne : G.exitSucc q ≠ []) :
      (∀ q' ∈ G.exitSucc q, Covered G ⟨q', B, SrcSetting.preJ⟩) →
      Covered G ⟨q, B, SrcSetting.preJ⟩
  | stepRepositionDynPost {q B} (m : RMode V) (hm : G.modeAt q = some m)
      (hrepo : m.repoDynPostOK = true) (hB : 0 < B) (hne : G.exitSucc q ≠ []) :
      (∀ q' ∈ G.exitSucc q, Covered G ⟨q', B, SrcSetting.postJ⟩) →
      Covered G ⟨q, B, SrcSetting.postJ⟩

/-- **Right-response reachability**, projected to the right: from mode `q` with budget `B`,
the assembled right response stays put (`refl`), evolves within the current mode on a joint
segment (`evolve`, of any duration, as the flow certificate is a forward invariant), jumps
along a declared successor whose guard the evolved state satisfies (`jump`), or runs a
right-only segment and continues at a successor (`repositionDynPre/Post`).

The `jump` gate is `m.weight < B` (Definition 8's **continue** case), **not** `0 < B`: a jump
fires only when budget remains *after* this segment (`B - m.weight ≥ 1`). When `B ≤ m.weight`
(the `base`, finish case) no jump is possible: the right response is a *prefix of the one
certified segment* and ends there, never evolving into a successor mode. -/
inductive RightReach (G : SearchGraph V) : Config → State V → State V → Prop
  | refl {q B σ ν} : RightReach G ⟨q, B, σ⟩ ν ν
  -- joint evolve/jump evolve the left ⟹ the continuation config is `postJ`.
  | evolve {q B σ ν μ ω} (m : RMode V) (hm : G.modeAt q = some m) (hj : m.jointOK = true) :
      Program.sem (Program.ode m.sys m.dom) ν μ →
      RightReach G ⟨q, B, SrcSetting.postJ⟩ μ ω → RightReach G ⟨q, B, σ⟩ ν ω
  | jump {q B σ ν μ ω} (m : RMode V) (hm : G.modeAt q = some m) (hj : m.jointOK = true)
      (e : REdge V) (he : e ∈ G.edges) (hsrc : e.src = q) (hlt : m.weight < B) :
      Program.sem (Program.ode m.sys m.dom) ν μ →
      Formula.sat e.guard μ →
      RightReach G ⟨e.tgt, B - m.weight, SrcSetting.postJ⟩ μ ω →
      RightReach G ⟨q, B, σ⟩ ν ω
  -- **right-only response**, by source setting. The right EVOLVES under the frozen-left field
  -- `dynSys` (`Program.sem`, a flow segment), and `InvHolds μ` is kept along it by the
  -- right-only flow certificate (`repoDynPresPre/Post`, `DI_nonstrict_domain`, whole-domain).
  -- It then continues at a successor with the same budget and σ (left frozen, zero budget).
  -- The successor's guard is not checked here: this relation is for preservation, and that
  -- the right-only run exists is the reposition certificate's job (Definition 7).
  | repositionDynPre {q B ν μ ω} (m : RMode V) (hm : G.modeAt q = some m)
      (hrepo : m.repoDynPreOK = true) (e : REdge V) (he : e ∈ G.edges) (hsrc : e.src = q) (hB : 0 < B) :
      Program.sem (Program.ode m.dynSys m.dynDomPre) ν μ →
      RightReach G ⟨e.tgt, B, SrcSetting.preJ⟩ μ ω →
      RightReach G ⟨q, B, SrcSetting.preJ⟩ ν ω
  | repositionDynPost {q B ν μ ω} (m : RMode V) (hm : G.modeAt q = some m)
      (hrepo : m.repoDynPostOK = true) (e : REdge V) (he : e ∈ G.edges) (hsrc : e.src = q) (hB : 0 < B) :
      Program.sem (Program.ode m.dynSys m.dynDomPost) ν μ →
      RightReach G ⟨e.tgt, B, SrcSetting.postJ⟩ μ ω →
      RightReach G ⟨q, B, SrcSetting.postJ⟩ ν ω

/-! ## Finiteness (the load-bearing soundness piece) -/

/-- **Budget strictly decreases per joint covering step.** Every retained successor a joint
`step` recurses into has strictly smaller budget. Together with `Covered` being inductive
(every derivation finite), this is Definition 8's exclusion of branches that never finish. -/
theorem cover_budget_decreases (G : SearchGraph V) {q B : ℕ} {σ σ' : SrcSetting} {m : RMode V}
    (hpos : 0 < B) (hw : 0 < m.weight) {q' : ℕ} (hq' : q' ∈ G.retainedSucc q) :
    (⟨q', B - m.weight, σ'⟩ : Config).B < (⟨q, B, σ⟩ : Config).B :=
  Nat.sub_lt hpos hw

/-! ## (4) Invariant preservation along a cover (Theorem 1 over a cover, Lemma 5) -/

/-- **Preservation is per segment (`Covered`-free).** Along **every** assembled right response
(joint or right-only), from an invariant-satisfying entry the invariant holds throughout.
Preservation depends only on each segment's certificate, `segPres` (joint flow certificate)
for joint `evolve`/`jump` and `repoDynPres*` (whole-domain right-only flow certificate) for
the right-only step, and NOT on the cover derivation. So the induction follows the response
with no case analysis on `Covered`, which governs existence and finiteness (checked by
`decideCovered`). -/
theorem pres (G : SearchGraph V) (g : Term V) (cert : CoverCert G g) :
    ∀ cfg ν ω, RightReach G cfg ν ω → InvHolds g ν → InvHolds g ω := by
  intro cfg ν ω hreach
  induction hreach with
  | refl => exact id
  | evolve m hm hj hsem _ ih => intro hν; exact ih (cert.segPres _ m hm hj _ hν _ hsem)
  | jump m hm hj e he hsrc hlt hsem hguard _ ih =>
      intro hν; exact ih (cert.segPres _ m hm hj _ hν _ hsem)
  -- right-only segment: `InvHolds μ` is kept along the frozen-left FLOW by the right-only flow
  -- certificate (`repoDynPresPre/Post`, `DI_nonstrict_domain`), the same shape as the joint
  -- `evolve` case, consuming `InvHolds ν` and the `sem` run. Whole-domain, so no `t²` touch.
  | repositionDynPre m hm hrepo e he hsrc hB hsem _ ih =>
      intro hν; exact ih (cert.repoDynPresPre _ m hm hrepo _ hν _ hsem)
  | repositionDynPost m hm hrepo e he hsrc hB hsem _ ih =>
      intro hν; exact ih (cert.repoDynPresPost _ m hm hrepo _ hν _ hsem)

/-- **`cover_sound`** (invariant preservation along a cover). If the config is covered and the
certificate bundle holds, then along **every** assembled right response from an
invariant-satisfying entry, the invariant is preserved throughout. The proof factors through
`pres`: preservation is per segment, so `Covered`, kept as a hypothesis, is needed only for
existence. -/
theorem cover_sound (G : SearchGraph V) (g : Term V) (cert : CoverCert G g) :
    ∀ cfg ν ω, Covered G cfg → RightReach G cfg ν ω → InvHolds g ν → InvHolds g ω :=
  fun cfg ν ω _ hreach hν => pres G g cert cfg ν ω hreach hν

/-! ## Connectors: the certificate fields are the certificate theorems' conclusions -/

/-- `SegPreserves` (the joint flow-certificate field of `CoverCert`) is discharged by
`flow_cert_sound` (Lemma 2): a mode whose dynamics are the stretched joint field of a flow
obligation (Eq. (14)), with unsat flow query, preserves the invariant. -/
theorem segPreserves_of_flow {n : ℕ} (o : FlowObligation n) (m : RMode (Var n))
    (hsys : m.sys = jointSys o.fL o.fR o.lam) (hdom : m.dom = o.domain)
    (hunsat : ∀ σ, ¬ Formula.sat (flowQuery o) σ) :
    SegPreserves o.g m := by
  intro ν hν
  rw [hsys, hdom]
  exact flow_cert_sound o hunsat hν

/-- **Right-only connector.** The right-only obligation `SegPreservesOn g dynSys dynDom` is
discharged by the **same** `flow_cert_sound` (Lemma 2), its `DI_nonstrict_domain` route
(`flowQuery = domain ∧ ġ > 0`, whole-domain unsat, Eq. (18)), instantiated by the caller with
the **left field frozen** (`o.fL = 0`), the right-only product of Eq. (15). No new soundness
argument: whole-domain (route A), so no `t²` boundary exposure. -/
theorem dynRepo_of_flow {n : ℕ} (o : FlowObligation n)
    (sys : ODESystem (Var n)) (dom : Formula (Var n))
    (hsys : sys = jointSys o.fL o.fR o.lam) (hdom : dom = o.domain)
    (hunsat : ∀ σ, ¬ Formula.sat (flowQuery o) σ) :
    SegPreservesOn o.g sys dom := by
  -- the caller instantiates `o.fL = 0` (left frozen) so `jointSys o.fL o.fR o.lam` is the
  -- right-only field; the proof holds for any `o.fL`: it is `flow_cert_sound` (route A).
  intro ν hν
  rw [hsys, hdom]
  exact flow_cert_sound o hunsat hν

/-- The `pruneSound` per-edge obligation is discharged by `nonconn_sound` (Definition 6): a
pruned edge whose right dynamics and domain are the non-connection obligation's, with both
checks unsat, has an unreachable guard along the flow. -/
theorem prune_of_nonconn (o : NonConnObligation V) (m : RMode V)
    (hsys : m.sys = o.sysR) (hdom : m.dom = o.domain)
    (hwf : o.sysR.WellFormed) (hlink : ∀ ω, Formula.sat o.guard ω ↔ 0 < Term.eval o.g ω)
    {ν : State V} (hν : Formula.sat o.source ν)
    (hsrc : ∀ σ, ¬ Formula.sat (sourceCheck o) σ)
    (hbar : ∀ σ, ¬ Formula.sat (barrierCheck o) σ) :
    ∀ μ, Program.sem (Program.ode m.sys m.dom) ν μ → ¬ Formula.sat o.guard μ := by
  rw [hsys, hdom]
  exact nonconn_sound o hwf hlink hν hsrc hbar

/-! ## (5) The global ∀∃ encoding bridge

The invariant-preservation conclusion of `cover_sound` is the right-projected content
of the ∀∃ claim `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv` (Definition 1, Eq. (10)). dL-rel `RFormula.encoding_correct`
bridges the bi-state relational formula to its dL host encoding, connecting the cover's
verdict to the dL semantics (and to a solver-checkable global formula). Stated in
`Cover/Encoding.lean` to keep the dL-rel dependency localized. -/

end RelCertifier
