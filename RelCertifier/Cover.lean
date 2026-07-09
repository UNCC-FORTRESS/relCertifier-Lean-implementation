/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

Stage 3 — the verified cover (composition) + Theorem 3 + the global ∀∃ encoding.

Composes the Stage-1 flow certificates (`flow_cert_sound`, per-segment invariant
preservation) and Stage-2 non-connection certificates (`nonconn_sound`, pruned edges
never taken) into the paper's **Theorem 3**: `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv` — for every
left execution an assembled right response preserves the relational invariant
throughout. The global ∀∃ claim is bridged into dL by dL-rel `encoding_correct`.

Functionality target: the Python cover search (`run_universal.py`, §IV budget walk +
§V.A cover). A configuration `(qR, B)` is covered when a joint segment closes the
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

/-- A right mode: its joint (λ-stretched) dynamics `sys` (Stage-1 `jointSys` shape),
its evolution domain `dom`, and the budget `weight` a residence consumes. -/
structure RMode (V : Type*) where
  sys    : ODESystem V
  dom    : Formula V
  weight : ℕ

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

/-- A configuration in the budget walk: current right mode `q`, remaining left-
residence budget `B`. -/
structure Config where
  q : ℕ
  B : ℕ
deriving Repr, DecidableEq

/-- Mode lookup by index. -/
def SearchGraph.modeAt (G : SearchGraph V) (q : ℕ) : Option (RMode V) := G.modes[q]?

/-- Retained successors of `q`: the self-loop `q` (always an admissible response) plus
every declared non-pruned edge target. Pruned edges are dropped. -/
def SearchGraph.retainedSucc (G : SearchGraph V) (q : ℕ) : List ℕ :=
  q :: ((G.edges.filter (fun e => decide (e.src = q) && !e.pruned)).map REdge.tgt)

/-! ## (2) The relational invariant and the certificate interface -/

/-- The relational invariant, as the Stage-1 joint sublevel `g ≤ 0`. -/
def InvHolds (g : Term V) (ω : State V) : Prop := Term.eval g ω ≤ 0

/-- A mode's segment preserves the invariant — the conclusion of `flow_cert_sound`
(`BoxLe` on the joint ODE program, for every invariant-satisfying entry). -/
def SegPreserves (g : Term V) (m : RMode V) : Prop :=
  ∀ ν, InvHolds g ν → BoxLe (Program.ode m.sys m.dom) (fun ω => Term.eval g ω) ν

/-- The composed certificate bundle the cover consumes. Every field is discharged by a
Stage-1/2 theorem at instantiation:
* `segPres` — each mode's flow certificate (`flow_cert_sound`);
* `pruneSound` — each pruned edge's non-connection certificate (`nonconn_sound`): its
  guard is unreachable after evolving in the source mode from an invariant state;
* `weightPos` — every mode's residence strictly consumes budget (finiteness). -/
structure CoverCert (G : SearchGraph V) (g : Term V) : Prop where
  segPres    : ∀ q m, G.modeAt q = some m → SegPreserves g m
  pruneSound : ∀ e ∈ G.edges, e.pruned = true → ∀ q m, G.modeAt q = some m → e.src = q →
      ∀ ν μ, InvHolds g ν → Program.sem (Program.ode m.sys m.dom) ν μ →
        ¬ Formula.sat e.guard μ
  weightPos  : ∀ m ∈ G.modes, 0 < m.weight

/-! ## (3) The cover relation (Covered) and right-response reachability -/

/-- **The cover relation** (`Covered`), inductively. A config is covered if the budget
is closed (`B = 0`), or the current mode has `0 < weight` (strict consumption — no
budget-neutral cycle) and **every retained successor** covers the decremented budget
(all-successors over the non-pruned graph; the self-loop is always one of them). -/
inductive Covered (G : SearchGraph V) : Config → Prop
  | closed {q} : Covered G ⟨q, 0⟩
  | cover {q B} (m : RMode V) (hm : G.modeAt q = some m) (hpos : 0 < B) (hw : 0 < m.weight) :
      (∀ q' ∈ G.retainedSucc q, Covered G ⟨q', B - m.weight⟩) →
      Covered G ⟨q, B⟩

/-- **Right-response reachability.** Bi-state-projected to the right: from mode `q` with
budget `B`, the assembled right response either stays put (`refl`), evolves within the
current mode (`evolve`, time-unbounded — the flow certificate is a forward invariant),
or jumps along a declared successor whose guard the evolved state enables (`jump`,
consuming one mode's budget). -/
inductive RightReach (G : SearchGraph V) : Config → State V → State V → Prop
  | refl {q B ν} : RightReach G ⟨q, B⟩ ν ν
  | evolve {q B ν μ ω} (m : RMode V) (hm : G.modeAt q = some m) :
      Program.sem (Program.ode m.sys m.dom) ν μ →
      RightReach G ⟨q, B⟩ μ ω → RightReach G ⟨q, B⟩ ν ω
  | jump {q B ν μ ω} (m : RMode V) (hm : G.modeAt q = some m) (e : REdge V)
      (he : e ∈ G.edges) (hsrc : e.src = q) (hpos : 0 < B) :
      Program.sem (Program.ode m.sys m.dom) ν μ →
      Formula.sat e.guard μ →
      RightReach G ⟨e.tgt, B - m.weight⟩ μ ω →
      RightReach G ⟨q, B⟩ ν ω

/-! ## Finiteness (the load-bearing soundness piece) -/

/-- **Budget strictly decreases per covering step** — the mechanized budget-neutral-
cycle rejection. Every retained successor a `cover` step recurses into has strictly
smaller budget, so no config can be justified through a cycle that fails to consume
budget; `Covered` is a well-founded (finite) inductive relation. -/
theorem cover_budget_decreases (G : SearchGraph V) {q B : ℕ} {m : RMode V}
    (hpos : 0 < B) (hw : 0 < m.weight) {q' : ℕ} (hq' : q' ∈ G.retainedSucc q) :
    (⟨q', B - m.weight⟩ : Config).B < (⟨q, B⟩ : Config).B :=
  Nat.sub_lt hpos hw

/-! ## (4) The composition theorem = paper Theorem 3 -/

/-- **`cover_sound` (Theorem 3, invariant-preservation core).** If the config is
covered and the composed certificate holds, then along **every** assembled right
response from an invariant-satisfying entry, the invariant is preserved throughout.

Proof (by induction on the `RightReach` derivation): `evolve` steps preserve the
invariant by `cert.segPres` (⟵ `flow_cert_sound`, `BoxLe`); a `jump` along an enabled
edge cannot be a pruned edge (⟵ `cert.pruneSound`, `nonconn_sound`: a pruned guard is
unreachable), so its target is a retained successor, which `Covered.cover` guarantees is
itself covered — the induction continues with strictly smaller budget. Concatenating the
certified steps yields invariant preservation on the whole right execution; since this
holds for *every* branch, whichever branch a left execution forces is covered — the
all-successors ⟹ existential the paper's ∀∃ needs. -/
theorem cover_sound (G : SearchGraph V) (g : Term V) (cert : CoverCert G g) :
    ∀ cfg ν ω, Covered G cfg → RightReach G cfg ν ω → InvHolds g ν → InvHolds g ω := by
  intro cfg ν ω hcov hreach
  induction hreach with
  | refl => exact id
  | evolve m hm hsem _ ih =>
      intro hν
      exact ih hcov (cert.segPres _ m hm _ hν _ hsem)
  | @jump q B ν μ ω m hm e he hsrc hpos hsem hguard _ ih =>
      intro hν
      have hμ : InvHolds g μ := cert.segPres _ m hm _ hν _ hsem
      -- an enabled edge cannot be pruned (else its guard is unreachable, `nonconn_sound`)
      have hnp : e.pruned = false := by
        cases hp : e.pruned with
        | false => rfl
        | true => exact absurd hguard (cert.pruneSound e he hp q m hm hsrc ν μ hν hsem)
      -- so the target is a retained successor, which `Covered.cover` guarantees is covered
      have htgt : e.tgt ∈ G.retainedSucc q := by
        refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, ?_, rfl⟩)
        exact List.mem_filter.mpr ⟨he, by simp [hsrc, hnp]⟩
      have hchild : Covered G ⟨e.tgt, B - m.weight⟩ := by
        cases hcov with
        | closed => exact absurd hpos (by simp)
        | cover m' hm' _ _ hall =>
            have hmm : m = m' := Option.some.inj (hm.symm.trans hm')
            subst hmm
            exact hall _ htgt
      exact ih hchild hμ

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
