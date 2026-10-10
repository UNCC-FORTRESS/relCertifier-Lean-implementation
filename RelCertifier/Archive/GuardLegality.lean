/-
Guard-legality of the coverage witness — retiring the ⊤-model boundary (C.2).

The ⊤-model relaxes `Gr`'s edge guards to `⊤` **only in the encoding layer** (for ∃-side proof
convenience). The **coverage layer never dropped them**: `RightReach.jump` (`Cover.lean`) carries
`Formula.sat e.guard μ` as a PREMISE at each switch — the real edge guard, satisfied at the post-flow
switch state `μ`. So a coverage witness is a legal execution of the REAL guarded automaton, not just
the ⊤-relaxed one. This is surfaced, not searched: the guard is a premise the witness's existence
already assumed (no reachability). Below: the witness stays in-domain given guard–domain coherence,
which is exactly the cross-switch entry-`domR` that the `∀ν HExistSeg` over-quantification was missing.

FINDING 1 (`WellFormedGuards`): the guard–domain coherence is an honest well-formedness hypothesis
(`source.dom ∧ e.guard ⟹ target.dom`), holding for well-specified automata (a benchmark's mode-entry
guard lands the state in that mode's domain), stated — not assumed of arbitrary graphs.
-/
import RelCertifier.Checker.Cover

namespace RelCertifier
open DL

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Guard–domain coherence (well-formedness, Finding 1).** At every declared edge, the source mode's
evolution domain together with the real edge guard implies the target mode's evolution domain — plus
the dynamic reposition analogue (`dynDom` coherence; the static reposition was removed 2026-10-09). Honest hypothesis:
true for well-specified automata (guards/regions are domain-consistent), stated not assumed. -/
structure WellFormedGuards (G : SearchGraph V) : Prop where
  /-- flow-jump: source domain + edge guard ⟹ target domain. -/
  jump : ∀ (q : ℕ) (m : RMode V), G.modeAt q = some m → ∀ e ∈ G.edges, e.src = q →
    ∀ (mt : RMode V), G.modeAt e.tgt = some mt →
      ∀ μ, Formula.sat m.dom μ → Formula.sat e.guard μ → Formula.sat mt.dom μ
  /-- dynamic reposition: source dyn-domain ⟹ target domain. -/
  dyn : ∀ (q : ℕ) (m : RMode V), G.modeAt q = some m → ∀ e ∈ G.edges, e.src = q →
    ∀ (mt : RMode V), G.modeAt e.tgt = some mt →
      ∀ μ, (Formula.sat m.dynDomPre μ ∨ Formula.sat m.dynDomPost μ) → Formula.sat mt.dom μ

/-- The entry state is admitted by the current mode's domain. -/
def EntryInDom (G : SearchGraph V) (cfg : Config) (ν : State V) : Prop :=
  ∃ m, G.modeAt cfg.q = some m ∧ Formula.sat m.dom ν

/-- Some reachable mode admits the state. -/
def SomeInDom (G : SearchGraph V) (ω : State V) : Prop :=
  ∃ (qf : ℕ) (mf : RMode V), G.modeAt qf = some mf ∧ Formula.sat mf.dom ω

/-- **The coverage witness is a guarded execution — C.2 closed.** Given guard–domain coherence
(`WellFormedGuards`) and edges targeting declared modes, a `RightReach` witness that starts in its
mode's domain **stays in-domain throughout** — the real edge guards it carries (`RightReach.jump`'s
premise) supply the cross-switch entry-`domR`. No reachability: each guard is surfaced from the
constructor premise. This retires the ⊤-model boundary for the coverage witness: the exhibited run
respects the real guards, so it is a legal execution of the guarded automaton. -/
theorem witness_is_guarded_execution (G : SearchGraph V) (hwf : WellFormedGuards G)
    (hev : ∀ e ∈ G.edges, ∃ mt, G.modeAt e.tgt = some mt) :
    ∀ {cfg : Config} {ν ω : State V}, RightReach G cfg ν ω → EntryInDom G cfg ν → SomeInDom G ω := by
  intro cfg ν ω hreach
  induction hreach with
  | @refl q B σ ν => rintro ⟨m, hm, hdom⟩; exact ⟨q, m, hm, hdom⟩
  | @evolve q B σ ν μ ω m hm hj hsem _ ih =>
      rintro ⟨m', hm', _⟩
      -- flow endpoint μ ∈ m.dom (ODE domain holds at the closed-interval endpoint)
      obtain ⟨r, Φ, hr, hΦ0, hΦr, _, _, hdomΦ⟩ := hsem
      have hμ : Formula.sat m.dom μ := by rw [← hΦr]; exact hdomΦ r ⟨hr, le_refl r⟩
      exact ih ⟨m, hm, hμ⟩
  | @jump q B σ ν μ ω m hm hj e he hsrc hlt hsem hguard _ ih =>
      rintro ⟨m', hm', _⟩
      obtain ⟨r, Φ, hr, hΦ0, hΦr, _, _, hdomΦ⟩ := hsem
      have hμ : Formula.sat m.dom μ := by rw [← hΦr]; exact hdomΦ r ⟨hr, le_refl r⟩
      obtain ⟨mt, hmt⟩ := hev e he
      have hμt : Formula.sat mt.dom μ := hwf.jump q m hm e he hsrc mt hmt μ hμ hguard
      exact ih ⟨mt, hmt, hμt⟩
  | @repositionDynPre q B ν μ ω m hm hrepo e he hsrc hB hsem _ ih =>
      rintro _
      obtain ⟨r, Φ, hr, hΦ0, hΦr, _, _, hdomΦ⟩ := hsem
      have hμ : Formula.sat m.dynDomPre μ := by rw [← hΦr]; exact hdomΦ r ⟨hr, le_refl r⟩
      obtain ⟨mt, hmt⟩ := hev e he
      exact ih ⟨mt, hmt, hwf.dyn q m hm e he hsrc mt hmt μ (Or.inl hμ)⟩
  | @repositionDynPost q B ν μ ω m hm hrepo e he hsrc hB hsem _ ih =>
      rintro _
      obtain ⟨r, Φ, hr, hΦ0, hΦr, _, _, hdomΦ⟩ := hsem
      have hμ : Formula.sat m.dynDomPost μ := by rw [← hΦr]; exact hdomΦ r ⟨hr, le_refl r⟩
      obtain ⟨mt, hmt⟩ := hev e he
      exact ih ⟨mt, hmt, hwf.dyn q m hm e he hsrc mt hmt μ (Or.inr hμ)⟩

end RelCertifier
