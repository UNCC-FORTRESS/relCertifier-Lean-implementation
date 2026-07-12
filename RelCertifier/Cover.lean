/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

Stage 3 — the verified cover (composition) + Theorem 3 + the global ∀∃ encoding.

Composes the Stage-1 flow certificates (`flow_cert_sound`, per-segment invariant
preservation) and Stage-2 non-connection certificates (`nonconn_sound`, pruned edges
never taken) into the paper's **Theorem 3**: `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv` — for every
left execution an assembled right response preserves the relational invariant
throughout. The global ∀∃ claim is bridged into dL by dL-rel `encoding_correct`.

Here `[|(L*, R*)⟩⟩` is written with the flat choice-star `R*`. The **transition-faithful**
right side — jumping only along declared edges (`R_real = star(rightAutomatonBody)`) — is
`BridgeFinish.theorem3_faithful`; `cover_sound`/`RightReach` below already model that faithful
response (the `jump` case follows a declared successor), and the witness
`JointBridge.rightReach_is_R_real_run` shows the two coincide.

The cover search (§IV budget walk + §V.A cover). A configuration `(qR, B)` is covered when a joint segment closes the
remaining budget, or every retained (non-pruned) successor covers the decremented
budget (all-successors). Budget-neutral cycles are rejected — each covering step
strictly consumes budget (`0 < weight`) — which is the load-bearing finiteness piece.

Trust boundary: Z3 UNSAT (the local certificates) remains the single leaf. The cover
composition is pure verified logic — no new trusted leaf.
-/
import RelCertifier.FlowCert
import RelCertifier.NonConn

namespace RelCertifier

open DL

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## (1) Search-graph / configuration structures (parser-ready) -/

/-- A right mode. Two participation kinds:
* **joint** — `sys` (λ-stretched `jointSys` shape), evolution domain `dom`, budget `weight` a
  joint residence consumes; available iff `jointOK`.
* **reposition** (REPOSITION CERTIFICATE) — a **discrete, static** mechanism (replaces the
  abandoned right-only *flow* certificate; NO derivative, NO `t²`/boundary-barrier exposure).
  The right repositions out of this mode into a declared successor, consuming **zero** budget
  (left frozen). Availability `repoOK` is gated by the STATIC region-invariant **R1**:
  `region ⟹ rel_inv` (`region = G_mR ∧ G_mL`), i.e. the invariant holds *everywhere* the right
  is in `mR` and the left in `mL` — an over-approximation of the drain-traversed region by the
  whole mode region, checked by Z3 with no dynamics. `CoverCert.repoPres` is exactly this R1. -/
structure RMode (V : Type*) where
  sys       : ODESystem V
  dom       : Formula V
  weight    : ℕ
  jointOK   : Bool := true
  -- **pre-j** reposition (σ=preJ, left still in guard): region `guardL ∧ guardR ∧ evolveL ∧ evolveR`.
  region    : Formula V := .tt
  repoPreOK : Bool := false
  -- **post-j** reposition (σ=postJ, left evolved past guard): region `guardR ∧ evolveL ∧ evolveR`
  -- (NO guardL — false post-joint; the left is carried by `evolveL`, its reachable set). STRICTLY
  -- STRONGER obligation (larger antecedent), so it is the safe default.
  regionPost : Formula V := .tt
  repoPostOK : Bool := false
  -- **dynamic (right-only flow) reposition** (certificate 3): the right EVOLVES under the
  -- frozen-left field `dynSys` (`ṡ_L = 0`), and `g ≤ 0` is preserved by MOTION (flow-cert
  -- `DI_nonstrict_domain`, whole-domain `ġ ≤ 0`), NOT statically. `dynDomPre`/`dynDomPost` are the
  -- σ-matched flow domains (`guardL ∧ evolveL ∧ evolveR` / `evolveL ∧ evolveR`). Zero budget.
  dynSys     : ODESystem V := []
  dynDomPre  : Formula V := .tt
  dynDomPost : Formula V := .tt
  repoDynPreOK  : Bool := false
  repoDynPostOK : Bool := false

/-- A declared right transition `src → tgt`, enabled by `guard`, flagged `pruned` when
a Stage-2 non-connection certificate removed it. -/
structure REdge (V : Type*) where
  src    : ℕ
  tgt    : ℕ
  guard  : Formula V
  pruned : Bool

/-- The right transition graph: modes indexed by list position, declared edges. -/
structure SearchGraph (V : Type*) where
  modes : List (RMode V)
  edges : List (REdge V)

/-- **Source setting** (paper's σ): has a joint segment occurred yet? `preJ` = the left has
NOT evolved (still in its guard `guardL`); `postJ` = the left HAS evolved (guard no longer
holds, only `evolveL` constrains it). Monotone: a joint segment flips `preJ → postJ`, never
back (the left, having evolved, cannot un-evolve). Selects which reposition obligation is used. -/
inductive SrcSetting where
  | preJ
  | postJ
deriving Repr, DecidableEq

/-- A configuration in the budget walk: current right mode `q`, remaining left-residence
budget `B`, and source setting `σ` (pre or post joint). -/
structure Config where
  q : ℕ
  B : ℕ
  σ : SrcSetting
deriving Repr, DecidableEq

/-- Mode lookup by index. -/
def SearchGraph.modeAt (G : SearchGraph V) (q : ℕ) : Option (RMode V) := G.modes[q]?

/-- Retained successors of `q`: the self-loop `q` (always an admissible response) plus
every declared non-pruned edge target. Pruned edges are dropped. -/
def SearchGraph.retainedSucc (G : SearchGraph V) (q : ℕ) : List ℕ :=
  q :: ((G.edges.filter (fun e => decide (e.src = q) && !e.pruned)).map REdge.tgt)

/-- **Exit successors** of `q` (REPOSITION): the non-pruned declared edge targets that are NOT
`q` itself. A reposition consumes zero budget, so the *self-loop* (staying in `q`) must be
excluded from its ∀-over-successors — staying is covered by the region-invariant R1 directly
(the right may linger in `q`, invariant held), and requiring the self-loop to *cover* would be a
budget-neutral cycle that never grounds. The `∀` over `exitSucc` (all non-self declared exits,
per the successor-completeness assumption) is Definition-4's all-successors condition for the
reposition kind. -/
def SearchGraph.exitSucc (G : SearchGraph V) (q : ℕ) : List ℕ :=
  (G.edges.filter (fun e => decide (e.src = q) && !e.pruned && decide (e.tgt ≠ q))).map REdge.tgt

/-! ## (2) The relational invariant and the certificate interface -/

/-- The relational invariant, as the Stage-1 joint sublevel `g ≤ 0`. -/
def InvHolds (g : Term V) (ω : State V) : Prop := Term.eval g ω ≤ 0

/-- A flow segment over `(sys, dom)` preserves the invariant — the `BoxLe` conclusion of
`flow_cert_sound` (any of its three routes, incl. `DI_nonstrict_domain`). -/
def SegPreservesOn (g : Term V) (sys : ODESystem V) (dom : Formula V) : Prop :=
  ∀ ν, InvHolds g ν → BoxLe (Program.ode sys dom) (fun ω => Term.eval g ω) ν

/-- A mode's **joint** segment preserves the invariant (`BoxLe` on the joint ODE program). -/
def SegPreserves (g : Term V) (m : RMode V) : Prop := SegPreservesOn g m.sys m.dom

/-- **REPOSITION R1 (static region-invariance).** A `repoOK` mode preserves the invariant
"for free" while the right resides in it: the invariant holds at **every** state of the mode
region `m.region` (`= G_mR ∧ G_mL`). This is a STATIC region-containment property — no ODE, no
derivative, no boundary barrier — discharged by a single Z3 UNSAT of `¬rel_inv ∧ G_mR ∧ G_mL`.
It over-approximates the drain-traversed region by the whole mode region (sound). -/
def RegionInvOn (g : Term V) (region : Formula V) : Prop :=
  ∀ ω, Formula.sat region ω → InvHolds g ω

/-- The composed certificate bundle the cover consumes. Every field is discharged by a
Stage-1/2/reposition theorem at instantiation:
* `segPres` — each **joint-supported** (`jointOK`) mode's flow certificate (`flow_cert_sound`);
* `repoPresPre` — each **pre-j-supported** (`repoPreOK`) mode's region-invariant on `m.region`
  (`= guardL ∧ guardR ∧ evolveL ∧ evolveR`), Z3 UNSAT of `¬rel_inv ∧ region` (no `t²`);
* `repoPresPost` — each **post-j-supported** (`repoPostOK`) mode's region-invariant on
  `m.regionPost` (`= guardR ∧ evolveL ∧ evolveR`, **no guardL**) — the strictly stronger
  obligation used once a joint segment has evolved the left past its guard;
* `pruneSound` — each pruned edge's non-connection certificate (`nonconn_sound`);
* `weightPos` — every mode's joint residence strictly consumes budget (finiteness).

**Documented assumption (TCB, not proven here):** the model is *faithful* — every execution of
`mR` exits via one of its declared successors (non-blocking / successor-completeness). Because we
assume exit-to-*some* declared successor, soundness requires covering **all** non-self declared
successors (`Covered.stepReposition*`'s `∀ q' ∈ exitSucc q`). -/
structure CoverCert (G : SearchGraph V) (g : Term V) : Prop where
  segPres      : ∀ q m, G.modeAt q = some m → m.jointOK = true → SegPreserves g m
  repoPresPre  : ∀ q m, G.modeAt q = some m → m.repoPreOK = true → RegionInvOn g m.region
  repoPresPost : ∀ q m, G.modeAt q = some m → m.repoPostOK = true → RegionInvOn g m.regionPost
  -- **certificate 3 (dynamic reposition)** — the right-only FLOW segment restored in its SOUND
  -- whole-domain form: `SegPreservesOn` over the frozen-left field `dynSys` (`ṡ_L = 0`), discharged
  -- by `flow_cert_sound`'s `DI_nonstrict_domain` route (`UNSAT(ġ > 0 ∧ dom)` — whole-domain, NOT the
  -- `t²`-vulnerable boundary form). σ-matched domains: `dynDomPre` (with guardL) / `dynDomPost`.
  repoDynPresPre  : ∀ q m, G.modeAt q = some m → m.repoDynPreOK = true →
      SegPreservesOn g m.dynSys m.dynDomPre
  repoDynPresPost : ∀ q m, G.modeAt q = some m → m.repoDynPostOK = true →
      SegPreservesOn g m.dynSys m.dynDomPost
  pruneSound   : ∀ e ∈ G.edges, e.pruned = true → ∀ q m, G.modeAt q = some m → e.src = q →
      ∀ ν μ, InvHolds g ν → Program.sem (Program.ode m.sys m.dom) ν μ →
        ¬ Formula.sat e.guard μ
  weightPos    : ∀ m ∈ G.modes, 0 < m.weight

/-! ## (3) The cover relation (Covered) and right-response reachability -/

/-- **The cover relation** (`Covered`) — a direct structural transcription of the paper's
**Definition 4**, its two cases explicit:

* **`base`** (budget closed): the current mode is certified (`hm`) and its single residence
  already covers the remaining budget (`B ≤ m.weight`). The cover **terminates here** — it
  does *not* recurse into successors, because the whole left residence is discharged by this
  one segment. (This is the case the old mechanization lacked: it only closed at `B = 0`,
  so a single-segment cover was forced to fabricate a spurious successor obligation.)
* **`step`** (budget remains): strictly more budget than one residence (`m.weight < B`, hence
  `0 < m.weight`), and **every retained successor** covers the decremented budget.

`base`'s `B ≤ m.weight` (not `B = 0`) is Definition 4's base condition; it is exactly the
termination that keeps the co-execution from over-reaching into a closed-leaf successor. -/
inductive Covered (G : SearchGraph V) : Config → Prop
  -- base/step are the JOINT segments. A joint segment evolves the left, so its successor config
  -- is `postJ` (regardless of the current `σ`). `σ` is monotone: joint flips `preJ→postJ`,
  -- reposition preserves it; nothing resets `postJ→preJ`.
  | base {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hj : m.jointOK = true)
      (hle : B ≤ m.weight) : Covered G ⟨q, B, σ⟩
  | step {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hj : m.jointOK = true)
      (hlt : m.weight < B) :
      (∀ q' ∈ G.retainedSucc q, Covered G ⟨q', B - m.weight, SrcSetting.postJ⟩) →
      Covered G ⟨q, B, σ⟩
  -- **pre-j reposition** (σ=preJ): obligation (1), region WITH `guardL` (`repoPreOK`). Concludes
  -- only a `preJ` config, so this cert can NEVER be applied at a `postJ` config (the false-certify
  -- direction is structurally impossible). Successors stay `preJ` (reposition doesn't evolve left).
  | stepRepositionPre {q B} (m : RMode V) (hm : G.modeAt q = some m) (hrepo : m.repoPreOK = true)
      (hB : 0 < B) (hne : G.exitSucc q ≠ []) :
      (∀ q' ∈ G.exitSucc q, Covered G ⟨q', B, SrcSetting.preJ⟩) →
      Covered G ⟨q, B, SrcSetting.preJ⟩
  -- **post-j reposition** (σ=postJ): obligation (2), region WITHOUT `guardL` (`repoPostOK`), the
  -- strictly stronger obligation. Concludes only a `postJ` config. Successors stay `postJ`.
  | stepRepositionPost {q B} (m : RMode V) (hm : G.modeAt q = some m) (hrepo : m.repoPostOK = true)
      (hB : 0 < B) (hne : G.exitSucc q ≠ []) :
      (∀ q' ∈ G.exitSucc q, Covered G ⟨q', B, SrcSetting.postJ⟩) →
      Covered G ⟨q, B, SrcSetting.postJ⟩
  -- **dynamic reposition** (certificate 3), σ-matched. Same structural shape as (1)/(2) — zero
  -- budget, `0<B`, `exitSucc≠[]`, ∀ non-self exit covered at the SAME σ — but availability is the
  -- dynamic flow cert (`repoDynPreOK`/`repoDynPostOK`) instead of the static region-invariant.
  | stepRepositionDynPre {q B} (m : RMode V) (hm : G.modeAt q = some m)
      (hrepo : m.repoDynPreOK = true) (hB : 0 < B) (hne : G.exitSucc q ≠ []) :
      (∀ q' ∈ G.exitSucc q, Covered G ⟨q', B, SrcSetting.preJ⟩) →
      Covered G ⟨q, B, SrcSetting.preJ⟩
  | stepRepositionDynPost {q B} (m : RMode V) (hm : G.modeAt q = some m)
      (hrepo : m.repoDynPostOK = true) (hB : 0 < B) (hne : G.exitSucc q ≠ []) :
      (∀ q' ∈ G.exitSucc q, Covered G ⟨q', B, SrcSetting.postJ⟩) →
      Covered G ⟨q, B, SrcSetting.postJ⟩

/-- **Right-response reachability.** Bi-state-projected to the right: from mode `q` with
budget `B`, the assembled right response either stays put (`refl`), evolves within the
current mode (`evolve`, time-unbounded — the flow certificate is a forward invariant), or
jumps along a declared successor whose guard the evolved state enables (`jump`).

The `jump` gate is `m.weight < B` (Definition 4's **step** condition), **not** `0 < B`: a
jump may fire only when budget genuinely remains *after* this residence (`B - m.weight ≥ 1`).
When the budget is closed (`B ≤ m.weight`, the `base` case) no jump is possible — the right
response is a *prefix of the single certified segment* and terminates, never evolving into a
successor mode. That is the mechanized image of Definition 4's base-case termination; its
absence (a bare `0 < B` gate) was the fidelity bug that forced closed-leaf certification. -/
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
  -- **REPOSITION response** (discrete, static — no flow, no `t²`), σ-matched. The right repositions
  -- out of `mR` into a declared successor at the SAME budget `B`, `σ` unchanged. `InvHolds μ` comes
  -- from the σ-matched region-invariant (`repoPresPre` on `region`, `repoPresPost` on `regionPost`),
  -- not from any derivative. Successor-completeness (exit via a declared successor) is the TCB.
  -- STATE-PRESERVING (the real reposition semantics): the continuous state is unchanged (`μ = ν`);
  -- only the mode advances (`q → e.tgt`, via the config). The region is checked at the current
  -- state `ν`. (Earlier this bound an arbitrary region-satisfying `μ` — a teleport, sound but
  -- conservative for preservation; tightened here so the step is a real state-preserving transition,
  -- as the `faModal_MULTI` reposition bridge requires.)
  | repositionPre {q B ν ω} (m : RMode V) (hm : G.modeAt q = some m) (hrepo : m.repoPreOK = true)
      (e : REdge V) (he : e ∈ G.edges) (hsrc : e.src = q) (hB : 0 < B) :
      Formula.sat m.region ν →
      RightReach G ⟨e.tgt, B, SrcSetting.preJ⟩ ν ω →
      RightReach G ⟨q, B, SrcSetting.preJ⟩ ν ω
  | repositionPost {q B ν ω} (m : RMode V) (hm : G.modeAt q = some m) (hrepo : m.repoPostOK = true)
      (e : REdge V) (he : e ∈ G.edges) (hsrc : e.src = q) (hB : 0 < B) :
      Formula.sat m.regionPost ν →
      RightReach G ⟨e.tgt, B, SrcSetting.postJ⟩ ν ω →
      RightReach G ⟨q, B, SrcSetting.postJ⟩ ν ω
  -- **DYNAMIC REPOSITION response** (certificate 3), σ-matched. Unlike the static ones, the right
  -- genuinely EVOLVES under the frozen-left field `dynSys` (`Program.sem`, a flow segment), and
  -- `InvHolds μ` is preserved along it by the flow cert (`repoDynPresPre/Post`, `DI_nonstrict_domain`
  -- whole-domain — NOT a static region membership, NOT a boundary-Lie). Then continues at the
  -- successor, same budget and σ. Zero budget (left frozen).
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

/-- **Budget strictly decreases per covering step** — the mechanized budget-neutral-
cycle rejection. Every retained successor a `cover` step recurses into has strictly
smaller budget, so no config can be justified through a cycle that fails to consume
budget; `Covered` is a well-founded (finite) inductive relation. -/
theorem cover_budget_decreases (G : SearchGraph V) {q B : ℕ} {σ σ' : SrcSetting} {m : RMode V}
    (hpos : 0 < B) (hw : 0 < m.weight) {q' : ℕ} (hq' : q' ∈ G.retainedSucc q) :
    (⟨q', B - m.weight, σ'⟩ : Config).B < (⟨q, B, σ⟩ : Config).B :=
  Nat.sub_lt hpos hw

/-! ## (4) The composition theorem = paper Theorem 3 -/

/-- **Preservation is per-segment (`Covered`-free).** Along **every** assembled right response
(joint or reposition), from an invariant-satisfying entry the invariant holds throughout. The
key structural fact: invariant *preservation* depends only on each segment's certificate —
`segPres` (flow cert) for joint `evolve`/`jump`, and `repoPres` (**static region-invariant R1**)
for the `reposition` step — and NOT on the cover derivation. The reposition case is where the
`t²` trap is avoided: `InvHolds μ` comes from `repoPres` applied to `m.region` (a static
region-containment fact), **not** from any boundary-Lie condition on a drain trajectory. So the
extension needs no case analysis on `Covered` here; each segment preserves and the induction
follows the response. (`Covered` governs *existence/finiteness*, discharged by `decideCovered`.) -/
theorem pres (G : SearchGraph V) (g : Term V) (cert : CoverCert G g) :
    ∀ cfg ν ω, RightReach G cfg ν ω → InvHolds g ν → InvHolds g ω := by
  intro cfg ν ω hreach
  induction hreach with
  | refl => exact id
  | evolve m hm hj hsem _ ih => intro hν; exact ih (cert.segPres _ m hm hj _ hν _ hsem)
  | jump m hm hj e he hsrc hlt hsem hguard _ ih =>
      intro hν; exact ih (cert.segPres _ m hm hj _ hν _ hsem)
  -- reposition (σ-matched): `InvHolds μ` is the STATIC region-invariant at `μ` — no derivative.
  -- pre-j uses `region` (with guardL); post-j uses `regionPost` (without guardL). Each cert is
  -- applied ONLY at its own σ config (the constructors' conclusions enforce it structurally).
  | repositionPre m hm hrepo e he hsrc hB hregion _ ih =>
      intro _; exact ih (cert.repoPresPre _ m hm hrepo _ hregion)
  | repositionPost m hm hrepo e he hsrc hB hregion _ ih =>
      intro _; exact ih (cert.repoPresPost _ m hm hrepo _ hregion)
  -- dynamic reposition (certificate 3): `InvHolds μ` is preserved along the frozen-left FLOW by the
  -- flow cert (`repoDynPresPre/Post`, `DI_nonstrict_domain`) — same shape as the joint `evolve` case,
  -- consuming `InvHolds ν` and the `sem` run. Whole-domain, no boundary-Lie ⟹ no `t²`.
  | repositionDynPre m hm hrepo e he hsrc hB hsem _ ih =>
      intro hν; exact ih (cert.repoDynPresPre _ m hm hrepo _ hν _ hsem)
  | repositionDynPost m hm hrepo e he hsrc hB hsem _ ih =>
      intro hν; exact ih (cert.repoDynPresPost _ m hm hrepo _ hν _ hsem)

/-- **`cover_sound` (Theorem 3, invariant-preservation core).** If the config is covered and the
composed certificate holds, then along **every** assembled right response from an
invariant-satisfying entry, the invariant is preserved throughout. Statement unchanged (across
the reposition extension); the proof factors through `pres` (preservation is per-segment, so
`Covered` — kept as a hypothesis — is not needed for preservation, only for existence). -/
theorem cover_sound (G : SearchGraph V) (g : Term V) (cert : CoverCert G g) :
    ∀ cfg ν ω, Covered G cfg → RightReach G cfg ν ω → InvHolds g ν → InvHolds g ω :=
  fun cfg ν ω _ hreach hν => pres G g cert cfg ν ω hreach hν

/-! ## Connectors — the certificate fields ARE the Stage-1/2 conclusions -/

/-- `SegPreserves` (the `flow certificate` field of `CoverCert`) is exactly discharged
by Stage-1 `flow_cert_sound`: a mode whose dynamics are the joint stretched field of a
flow obligation, with UNSAT flow query, preserves the invariant. -/
theorem segPreserves_of_flow {n : ℕ} (o : FlowObligation n) (m : RMode (Var n))
    (hsys : m.sys = jointSys o.fL o.fR o.lam) (hdom : m.dom = o.domain)
    (hunsat : ∀ σ, ¬ Formula.sat (flowQuery o) σ) :
    SegPreserves o.g m := by
  intro ν hν
  rw [hsys, hdom]
  exact flow_cert_sound o hunsat hν

/-- **DYNAMIC REPOSITION connector (certificate 3).** The dynamic-reposition obligation
`SegPreservesOn g dynSys dynDom` is discharged by the **same** `flow_cert_sound` — its
`DI_nonstrict_domain` route (`flowQuery = domain ∧ ġ > 0`, whole-domain UNSAT) — instantiated with
the **left field frozen** (`o.fL = 0`, made explicit by `hfrozen`), so the segment is a right-only
flow. This is NOT a new soundness argument: it is `flow_cert_sound` (already proven) with a frozen
left. Whole-domain (route A) ⟹ no `t²` boundary exposure. -/
theorem dynRepo_of_flow {n : ℕ} (o : FlowObligation n)
    (sys : ODESystem (Var n)) (dom : Formula (Var n))
    (hsys : sys = jointSys o.fL o.fR o.lam) (hdom : dom = o.domain)
    (hunsat : ∀ σ, ¬ Formula.sat (flowQuery o) σ) :
    SegPreservesOn o.g sys dom := by
  -- the caller instantiates `o.fL = 0` (left frozen) so `jointSys o.fL o.fR o.lam` is the
  -- right-only field; the proof holds for any `o.fL` — it IS `flow_cert_sound` (route A).
  intro ν hν
  rw [hsys, hdom]
  exact flow_cert_sound o hunsat hν

/-- **REPOSITION R1 connector.** `RegionInv` (the reposition field of `CoverCert`) is exactly a
Z3 UNSAT check: `region ⟹ rel_inv` holds iff `¬rel_inv ∧ region` is unsatisfiable. Purely
static (no ODE / no derivative), so it carries no `t²` boundary-barrier exposure — the invariant
on the mode region is a first-order real-arithmetic fact discharged by the solver. -/
theorem regionInv_of_unsat {n : ℕ} (region : Formula (Var n)) (g : Term (Var n))
    (hunsat : ∀ σ, ¬ Formula.sat (Formula.and (Formula.cmp .gt g (Term.const 0)) region) σ) :
    RegionInvOn g region := by
  intro ω hreg
  by_contra h
  rw [InvHolds, not_le] at h
  exact hunsat ω ⟨h, hreg⟩

/-- The `pruneSound` per-edge obligation is exactly discharged by Stage-2
`nonconn_sound`: a pruned edge whose right dynamics/domain are the non-connection
obligation's, with both checks UNSAT, has an unreachable guard along the flow. -/
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
of the paper's `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`. dL-rel `RFormula.encoding_correct`
bridges the bi-state relational formula to its dL host encoding, connecting the cover's
verdict to the dL semantics (and to a solver-checkable global formula). Stated in
`Cover/Encoding.lean` to keep the dL-rel dependency localized. -/

end RelCertifier
