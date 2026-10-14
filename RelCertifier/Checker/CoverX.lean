/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The extended cover: Definition 4 with chosen successors and hops

`Covered` (`Checker/Cover.lean`) is Definition 4 with the all-successors rule: after a segment,
every retained successor must be covered. The existential mode choice adds two rules backed by
a coverage certificate `Cover(R, S)`: `R ∧ ⋀_{q' ∈ S} ¬ guard(q')` is unsat, so every state of
the region `R` lies in the guard of some mode of `S` (`docs/CHOICE-SOUNDNESS.md`):

* **chosen successors** (case 3): after a joint segment of `q` (region `JointEnd(q)`) or a
  right-only segment of `q` (region `RepoEnd(q, σ)`), every mode of a chosen nonempty subset
  `S` of the retained successors is covered;
* **hop** (case 4): at a configuration start (region `StartRegion(q, σ)`), a zero-duration
  switch into a chosen subset `S` of the declared non-self successors, every mode of which is
  covered at the same budget.

The regions are formulas over the right automaton's modes; which regions a graph certifies is
the data `ChoiceData` carries (one list of chosen sets per mode and setting). Soundness of the
certificates (the Z3 unsat answers) is a hypothesis of the semantic theorem
(`Proofs/Encoding/CoverResp.lean`); this file is the structural half: the relation, the
checker, and the checker's soundness. No hop flag is needed for the relation (every derivation
is finite by construction); the checker's fuel bounds its search.
-/
import RelCertifier.Checker.Checker
import RelCertifier.Proofs.Encoding.JointBridge

namespace RelCertifier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The coverage certificates a cover may use, as the chosen sets: `jointS q` after a joint
segment of `q`, `repoS q σ` after a right-only segment of `q` in setting `σ`, `hopS q σ` at a
configuration start in `q`. Each listed set is one certificate; the semantic theorem assumes
each certificate's unsat answer. -/
structure ChoiceData where
  jointS : ℕ → List (List ℕ)
  repoS  : ℕ → SrcSetting → List (List ℕ)
  hopS   : ℕ → SrcSetting → List (List ℕ)

/-- The empty choice data: `CoveredX` then coincides with `Covered`. -/
def ChoiceData.none : ChoiceData := ⟨fun _ => [], fun _ _ => [], fun _ _ => []⟩

/-- The declared non-pruned successors of `q` (the retained ones without the implicit
self-loop): the targets a chosen set after a joint segment may name, each with an edge. -/
def SearchGraph.declSucc (G : SearchGraph V) (q : ℕ) : List ℕ :=
  (G.edges.filter (fun e => decide (e.src = q) && !e.pruned)).map REdge.tgt

/-- **Definition 4, extended** (cases 1 to 4 of `docs/CHOICE-SOUNDNESS.md` §4). -/
inductive CoveredX (G : SearchGraph V) (ch : ChoiceData) : Config → Prop
  -- 1. base: one joint segment closes the budget
  | base {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hj : m.jointOK = true)
      (hle : B ≤ m.weight) : CoveredX G ch ⟨q, B, σ⟩
  -- 2. joint step, all retained successors
  | step {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hj : m.jointOK = true)
      (hlt : m.weight < B) :
      (∀ q' ∈ G.retainedSucc q, CoveredX G ch ⟨q', B - m.weight, SrcSetting.postJ⟩) →
      CoveredX G ch ⟨q, B, σ⟩
  -- 2. right-only step, all retained exits (σ-matched)
  | stepRepoPre {q B} (m : RMode V) (hm : G.modeAt q = some m)
      (hrepo : m.repoDynPreOK = true) (hB : 0 < B) (hne : G.exitSucc q ≠ []) :
      (∀ q' ∈ G.exitSucc q, CoveredX G ch ⟨q', B, SrcSetting.preJ⟩) →
      CoveredX G ch ⟨q, B, SrcSetting.preJ⟩
  | stepRepoPost {q B} (m : RMode V) (hm : G.modeAt q = some m)
      (hrepo : m.repoDynPostOK = true) (hB : 0 < B) (hne : G.exitSucc q ≠ []) :
      (∀ q' ∈ G.exitSucc q, CoveredX G ch ⟨q', B, SrcSetting.postJ⟩) →
      CoveredX G ch ⟨q, B, SrcSetting.postJ⟩
  -- 3. joint step, chosen successors (a certified subset of the retained ones)
  | stepChosen {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hj : m.jointOK = true)
      (hlt : m.weight < B) (S : List ℕ) (hS : S ∈ ch.jointS q) (hne : S ≠ [])
      (hsub : ∀ q' ∈ S, q' ∈ G.declSucc q) :
      (∀ q' ∈ S, CoveredX G ch ⟨q', B - m.weight, SrcSetting.postJ⟩) →
      CoveredX G ch ⟨q, B, σ⟩
  -- 3. right-only step, chosen exits (zero budget; the segment may have duration zero)
  | repoChosen {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hB : 0 < B)
      (S : List ℕ) (hS : S ∈ ch.repoS q σ) (hne : S ≠ [])
      (hsub : ∀ q' ∈ S, q' ∈ G.exitSucc q) :
      (∀ q' ∈ S, CoveredX G ch ⟨q', B, σ⟩) →
      CoveredX G ch ⟨q, B, σ⟩
  -- 4. hop: a zero-duration switch at a configuration start into a chosen subset of the
  -- declared non-self successors
  | hop {q B σ} (m : RMode V) (hm : G.modeAt q = some m)
      (S : List ℕ) (hS : S ∈ ch.hopS q σ) (hne : S ≠ [])
      (hsub : ∀ q' ∈ S, q' ∈ G.exitSucc q) :
      (∀ q' ∈ S, CoveredX G ch ⟨q', B, σ⟩) →
      CoveredX G ch ⟨q, B, σ⟩

/-- Every all-successors derivation is an extended one. -/
theorem coveredX_of_covered (G : SearchGraph V) (ch : ChoiceData) :
    ∀ cfg, Covered G cfg → CoveredX G ch cfg := by
  intro cfg h
  induction h with
  | base m hm hj hle => exact CoveredX.base m hm hj hle
  | step m hm hj hlt _ ih => exact CoveredX.step m hm hj hlt ih
  | stepRepositionDynPre m hm hrepo hB hne _ ih => exact CoveredX.stepRepoPre m hm hrepo hB hne ih
  | stepRepositionDynPost m hm hrepo hB hne _ ih =>
      exact CoveredX.stepRepoPost m hm hrepo hB hne ih

/-! ## The checker -/

/-- The chosen sets of `q` in setting `σ` usable after a right-only segment or at a start. -/
def ChoiceData.repoSAt (ch : ChoiceData) (q : ℕ) (σ : SrcSetting) : List (List ℕ) := ch.repoS q σ
def ChoiceData.hopSAt (ch : ChoiceData) (q : ℕ) (σ : SrcSetting) : List (List ℕ) := ch.hopS q σ

/-- **Definition 4 extended, executable.** `decideCovered` plus the three choice rules; each
chosen set must be nonempty and inside the rule's successor set. -/
def decideCoveredX (G : SearchGraph V) (ch : ChoiceData) : ℕ → Config → Bool
  | 0,        _      => false
  | fuel + 1, ⟨q, B, σ⟩ =>
      match G.modeAt q with
      | none   => false
      | some m =>
          (m.jointOK && decide (B ≤ m.weight))
          || (m.jointOK && decide (m.weight < B) &&
                (G.retainedSucc q).all (fun q' =>
                   decideCoveredX G ch fuel ⟨q', B - m.weight, SrcSetting.postJ⟩))
          || ((match σ with | .preJ => m.repoDynPreOK | .postJ => m.repoDynPostOK)
                && decide (0 < B) && !(G.exitSucc q).isEmpty &&
                (G.exitSucc q).all (fun q' => decideCoveredX G ch fuel ⟨q', B, σ⟩))
          || (m.jointOK && decide (m.weight < B) &&
                (ch.jointS q).any (fun S => !S.isEmpty &&
                  S.all (fun q' => decide (q' ∈ G.declSucc q) &&
                    decideCoveredX G ch fuel ⟨q', B - m.weight, SrcSetting.postJ⟩)))
          || (decide (0 < B) &&
                (ch.repoSAt q σ).any (fun S => !S.isEmpty &&
                  S.all (fun q' => decide (q' ∈ G.exitSucc q) &&
                    decideCoveredX G ch fuel ⟨q', B, σ⟩)))
          || ((ch.hopSAt q σ).any (fun S => !S.isEmpty &&
                  S.all (fun q' => decide (q' ∈ G.exitSucc q) &&
                    decideCoveredX G ch fuel ⟨q', B, σ⟩)))

theorem list_all_and {α : Type*} {p q : α → Bool} {l : List α} (h : l.all (fun x => p x && q x) = true) :
    (∀ x ∈ l, p x = true) ∧ (∀ x ∈ l, q x = true) := by
  rw [List.all_eq_true] at h
  exact ⟨fun x hx => (Bool.and_eq_true_iff.mp (h x hx)).1,
    fun x hx => (Bool.and_eq_true_iff.mp (h x hx)).2⟩

/-- **Soundness of the extended checker.** -/
theorem decideCoveredX_sound (G : SearchGraph V) (ch : ChoiceData) :
    ∀ (fuel : ℕ) (cfg : Config), decideCoveredX G ch fuel cfg = true → CoveredX G ch cfg := by
  intro fuel
  induction fuel with
  | zero => intro cfg h; simp [decideCoveredX] at h
  | succ f ih =>
      rintro ⟨q, B, σ⟩ h
      simp only [decideCoveredX] at h
      cases hm : G.modeAt q with
      | none => rw [hm] at h; simp at h
      | some m =>
          rw [hm] at h
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
            Bool.not_eq_true'] at h
          have hne_of : ∀ (S : List ℕ), S.isEmpty = false → S ≠ [] := by
            intro S hS hnil; rw [hnil] at hS; simp at hS
          rcases h with ((((⟨hj, hle⟩ | ⟨⟨hj, hlt⟩, hall⟩) | ⟨⟨⟨hrepo, hB⟩, hne'⟩, hall⟩)
            | ⟨⟨hj, hlt⟩, S, hS, hne, hall⟩) | ⟨hB, S, hS, hne, hall⟩) | ⟨S, hS, hne, hall⟩
          · exact CoveredX.base m hm hj hle
          · refine CoveredX.step m hm hj hlt ?_
            intro q' hq'; exact ih _ (List.all_eq_true.mp hall q' hq')
          · have hne : G.exitSucc q ≠ [] := by
              intro hnil; rw [hnil] at hne'; simp at hne'
            cases σ with
            | preJ =>
                refine CoveredX.stepRepoPre m hm hrepo hB hne ?_
                intro q' hq'; exact ih _ (List.all_eq_true.mp hall q' hq')
            | postJ =>
                refine CoveredX.stepRepoPost m hm hrepo hB hne ?_
                intro q' hq'; exact ih _ (List.all_eq_true.mp hall q' hq')
          · obtain ⟨hsub, hcov⟩ := list_all_and hall
            refine CoveredX.stepChosen m hm hj hlt S hS (hne_of S hne) (fun q' hq' => ?_) (fun q' hq' => ?_)
            · exact decide_eq_true_eq.mp (hsub q' hq')
            · exact ih _ (hcov q' hq')
          · obtain ⟨hsub, hcov⟩ := list_all_and hall
            refine CoveredX.repoChosen m hm hB S hS (hne_of S hne) (fun q' hq' => ?_) (fun q' hq' => ?_)
            · exact decide_eq_true_eq.mp (hsub q' hq')
            · exact ih _ (hcov q' hq')
          · obtain ⟨hsub, hcov⟩ := list_all_and hall
            refine CoveredX.hop m hm S hS (hne_of S hne) (fun q' hq' => ?_) (fun q' hq' => ?_)
            · exact decide_eq_true_eq.mp (hsub q' hq')
            · exact ih _ (hcov q' hq')

end RelCertifier
