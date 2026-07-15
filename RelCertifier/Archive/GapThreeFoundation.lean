/-
GAP 3, Task 1 — the hybrid-program representation + `graphOf`.

The foundation for tying the tooling's cover to the ACTUAL programs L, R. `HybridAut` is the mode-list
representation; `leftEncode`/`rightEncode` (`⟦·⟧`) encode it to dL programs (the modality's programs);
`graphOf` builds the semantic search graphs from the same modes.

**Two ties, both by construction:**
* UP — `⟦·⟧` and `graphOf` read the SAME `A.modes`; `leftEncode`/`rightEncode` ARE the theorem's
  programs, so `[[leftEncode L >> rightEncode R]]inv` IS the theorem's conclusion (definitional).
* DOWN — `graphOf_Gr` and `graphOf_Gj` are built per-`mR` from the same `R.modes`, so at each index the
  `Gr`-mode and `Gj`-mode share `mR` (same `fR`, `domR`) — `RightProjAlign`'s alignment holds by
  construction (matching-crux-(a), from the `graphOf` definition). Task 2 makes it a theorem.

Findings (design points): the left encode is **guard-free** (∀-over-approximation, sound: `⟦L⟧` ⊇ L's
guarded runs); edge guards are `tt` (the faithful chain's `htt`, ⊤-model), not `m.guard`.
-/
import RelCertifier.Proofs.Encoding.JointBridge
import RelCertifier.Core.Reify
import RelCertifier.Proofs.Encoding.Reification

namespace RelCertifier
open DL

variable {n : ℕ}

/-! ## The hybrid-automaton representation -/

/-- One mode of a hybrid automaton: its field `dyn`, evolution domain `dom`, transition `guard`, and
declared successor indices `next`. -/
structure HybridMode (n : ℕ) where
  dyn   : Fin n → Term (Var n)
  dom   : Formula (Var n)
  guard : Formula (Var n)
  next  : List ℕ

/-- A hybrid automaton = a list of modes (indexed by position). -/
structure HybridAut (n : ℕ) where
  modes : List (HybridMode n)

/-! ## Encoding `⟦·⟧` — the automaton as a dL program (the modality's programs) -/

/-- The left mode programs (∀-side, guard-free over-approximation — sound, stronger). -/
def HybridAut.leftProgs (L : HybridAut n) : List (Program (Var n)) :=
  L.modes.map (fun m => Program.ode (leftBlock m.dyn) m.dom)

/-- `⟦L⟧` for the left (∀-side): the star of the mode choice. Exactly the theorem's left program. -/
def leftEncode (L : HybridAut n) : Program (Var n) :=
  Program.star (bigChoice L.leftProgs)

/-! ## `graphOf` — the semantic search graphs from the automaton modes -/

/-- Declared edges from an automaton's `next` (⊤-guarded — the faithful chain's `htt`; the real guard
is dissolved by the ⊤-model, as in the runtime `cgReal`). Shared by `Gr` and `Gj`. -/
def HybridAut.edgesOf (A : HybridAut n) : List (REdge (Var n)) :=
  (List.range A.modes.length).flatMap (fun q =>
    match A.modes[q]? with
    | none   => []
    | some m => m.next.map (fun tgt => { src := q, tgt := tgt, guard := Formula.tt, pruned := false }))

/-- **`Gr(R)`** — the right search graph: each `Gr` mode is the R-projection `rightBlock m.dyn lam` of
an `R`-mode, with its evolution domain and the frozen-left `dynSys` for the dynamic reposition. -/
def graphOf_Gr (R : HybridAut n) (lam : Term (Var n)) : SearchGraph (Var n) :=
  { modes := R.modes.map (fun m =>
      { sys := rightBlock m.dyn lam, dom := m.dom, weight := 1,
        dynSys := jointSys (fun _ => Term.const 0) m.dyn lam,
        dynDomPre := m.dom, dynDomPost := m.dom })
    edges := R.edgesOf }

/-- **`Gj(L,R,mL)`** — the joint search graph for a fixed left mode `mL`: each mode is the joint
`jointSys mL.dyn m.dyn lam` of `mL` with an `R`-mode `m`, evolution domain `mL.dom ∧ m.dom`. Same
edges as `Gr` — so the per-index `Gr`/`Gj` alignment (`RightProjAlign`) holds by construction. -/
def graphOf_Gj (L R : HybridAut n) (lam : Term (Var n)) (mL : HybridMode n) : SearchGraph (Var n) :=
  { modes := R.modes.map (fun m =>
      { sys := jointSys mL.dyn m.dyn lam, dom := Formula.and mL.dom m.dom, weight := 1,
        dynSys := jointSys (fun _ => Term.const 0) m.dyn lam,
        dynDomPre := Formula.and mL.dom m.dom, dynDomPost := Formula.and mL.dom m.dom })
    edges := R.edgesOf }

/-- `⟦R⟧` for the right (∃-side): the faithful automaton `R_real (graphOf_Gr R lam) mv`. Exactly the
theorem's right program (star of `rightAutomatonBody`). -/
def rightEncode (R : HybridAut n) (lam : Term (Var n)) (mv : Var n) : Program (Var n) :=
  R_real (graphOf_Gr R lam) mv

/-! ## Scope predicates — the fragment the tool handles -/

/-- `P` is a left hybrid automaton (∀-side scope). -/
def isLeftAut (P : Program (Var n)) : Prop := ∃ L : HybridAut n, P = leftEncode L

/-- `P` is a right hybrid automaton (∃-side scope). -/
def isRightAut (P : Program (Var n)) : Prop :=
  ∃ (R : HybridAut n) (lam : Term (Var n)) (mv : Var n), P = rightEncode R lam mv

/-! ## Tie confirmations (definitional — the same `A` viewed two ways) -/

/-- UP: `leftEncode L` is literally the star of `L.leftProgs` — the theorem's left program. -/
theorem leftEncode_eq (L : HybridAut n) :
    leftEncode L = Program.star (bigChoice L.leftProgs) := rfl

/-- UP: `rightEncode R lam mv` is literally `R_real (graphOf_Gr R lam) mv` — the theorem's right. -/
theorem rightEncode_eq (R : HybridAut n) (lam : Term (Var n)) (mv : Var n) :
    rightEncode R lam mv = R_real (graphOf_Gr R lam) mv := rfl

/-- DOWN: `Gr` and `Gj` carry the SAME modes list length and SAME edges (both from `R`) — the
per-index alignment substrate for `RightProjAlign`. -/
theorem graphOf_same_edges (L R : HybridAut n) (lam : Term (Var n)) (mL : HybridMode n) :
    (graphOf_Gj L R lam mL).edges = (graphOf_Gr R lam).edges := rfl

theorem graphOf_same_length (L R : HybridAut n) (lam : Term (Var n)) (mL : HybridMode n) :
    (graphOf_Gj L R lam mL).modes.length = (graphOf_Gr R lam).modes.length := by
  simp only [graphOf_Gj, graphOf_Gr, List.length_map]

end RelCertifier
