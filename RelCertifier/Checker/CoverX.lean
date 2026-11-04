/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The extended cover: Definition 8 with committed successor subsets, and entry hops

`Covered` (`Checker/Cover.lean`) is Definition 8 with the retained successors as landing sets:
after a segment, every retained successor must be covered. `CoveredX` adds the committed
subsets of Section 4.3 and Definition 8, each backed by a coverage certificate `Cover(R, S)`:
`R ∧ ⋀_{q' ∈ S} ¬ guard(q')` is unsat, so every state of the region `R` lies in the guard of
some mode of `S` (`docs/CHOICE-SOUNDNESS.md`):

* **committed subset** (case 3): after a joint segment of `q` (region `JointEnd(q)`) or a
  right-only segment of `q` (region `RepoEnd(q, σ)`), every mode of a nonempty committed
  subset `S` of the retained successors is covered;
* **hop** (case 4): at a configuration start (region `StartRegion(q, σ)`), a zero-duration
  switch into a nonempty subset `S` of the declared non-self successors, every mode of which is
  covered at the same budget. Definition 8 has no such case; it is an extension of the tool.

The regions are formulas over the right automaton's modes; which subsets a graph certifies is
the data `ChoiceData` carries (one list of subsets per mode and setting). Soundness of the
coverage certificates (the Z3 unsat answers) is a hypothesis of the semantic theorem
(`Proofs/Encoding/CoverResp.lean`); this file is the structural half: the relation, the
checker, and the checker's soundness. The relation needs no hop flag (every derivation is
finite by construction); the checker's fuel bounds its search.
-/
import RelCertifier.Checker.Checker
import RelCertifier.Proofs.Encoding.JointBridge

namespace RelCertifier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The coverage certificates a cover may use, as committed subsets: `jointS q` after a joint
segment of `q`, `repoS q σ` after a right-only segment of `q` in source setting `σ`, `hopS q σ`
at a configuration start in `q`. Each listed set is one certificate; the semantic theorem
assumes each certificate's unsat answer. -/
structure ChoiceData where
  /-- The pairings certified for this left mode: the joint segment of `q`, the pre-joint and
  post-joint right-only segments of `q` (the tool's per-left-mode flags). -/
  jointOK  : ℕ → Bool
  repoPre  : ℕ → Bool
  repoPost : ℕ → Bool
  jointS : ℕ → List (List ℕ)
  repoS  : ℕ → SrcSetting → List (List ℕ)
  hopS   : ℕ → SrcSetting → List (List ℕ)

/-- The declared non-pruned successors of `q` (the retained ones without the implicit
self-loop): the targets a committed subset after a joint segment may name, each with an
edge. -/
def SearchGraph.declSucc (G : SearchGraph V) (q : ℕ) : List ℕ :=
  (G.edges.filter (fun e => decide (e.src = q) && !e.pruned)).map REdge.tgt

/-- **Definition 8 with committed subsets**, plus the entry hop (cases 1 to 4 of
`docs/CHOICE-SOUNDNESS.md`): 1 finish, 2 continue into every retained successor, 3 continue
into a committed subset, 4 hop. -/
inductive CoveredX (G : SearchGraph V) (ch : ChoiceData) : Config → Prop
  -- 1. finish: one joint segment closes the budget
  | base {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hj : ch.jointOK q = true)
      (hle : B ≤ m.weight) : CoveredX G ch ⟨q, B, σ⟩
  -- 2. continue, joint, every retained successor
  | step {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hj : ch.jointOK q = true)
      (hlt : m.weight < B) :
      (∀ q' ∈ G.retainedSucc q, CoveredX G ch ⟨q', B - m.weight, SrcSetting.postJ⟩) →
      CoveredX G ch ⟨q, B, σ⟩
  -- 2. continue, right-only, every non-self retained successor (by source setting)
  | stepRepoPre {q B} (m : RMode V) (hm : G.modeAt q = some m)
      (hrepo : ch.repoPre q = true) (hB : 0 < B) (hne : G.exitSucc q ≠ []) :
      (∀ q' ∈ G.exitSucc q, CoveredX G ch ⟨q', B, SrcSetting.preJ⟩) →
      CoveredX G ch ⟨q, B, SrcSetting.preJ⟩
  | stepRepoPost {q B} (m : RMode V) (hm : G.modeAt q = some m)
      (hrepo : ch.repoPost q = true) (hB : 0 < B) (hne : G.exitSucc q ≠ []) :
      (∀ q' ∈ G.exitSucc q, CoveredX G ch ⟨q', B, SrcSetting.postJ⟩) →
      CoveredX G ch ⟨q, B, SrcSetting.postJ⟩
  -- 3. continue, joint, a committed subset (a certified subset of the retained successors)
  | stepChosen {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hj : ch.jointOK q = true)
      (hlt : m.weight < B) (S : List ℕ) (hS : S ∈ ch.jointS q) (hne : S ≠ [])
      (hsub : ∀ q' ∈ S, q' ∈ G.declSucc q) :
      (∀ q' ∈ S, CoveredX G ch ⟨q', B - m.weight, SrcSetting.postJ⟩) →
      CoveredX G ch ⟨q, B, σ⟩
  -- 3. continue, right-only, a committed subset of the non-self retained successors (zero
  -- budget; the segment may have duration zero)
  | repoChosen {q B σ} (m : RMode V) (hm : G.modeAt q = some m) (hB : 0 < B)
      (S : List ℕ) (hS : S ∈ ch.repoS q σ) (hne : S ≠ [])
      (hsub : ∀ q' ∈ S, q' ∈ G.exitSucc q) :
      (∀ q' ∈ S, CoveredX G ch ⟨q', B, σ⟩) →
      CoveredX G ch ⟨q, B, σ⟩
  -- 4. hop: a zero-duration switch at a configuration start into a committed subset of the
  -- declared non-self successors (not a case of Definition 8)
  | hop {q B σ} (m : RMode V) (hm : G.modeAt q = some m)
      (S : List ℕ) (hS : S ∈ ch.hopS q σ) (hne : S ≠ [])
      (hsub : ∀ q' ∈ S, q' ∈ G.exitSucc q) :
      (∀ q' ∈ S, CoveredX G ch ⟨q', B, σ⟩) →
      CoveredX G ch ⟨q, B, σ⟩

/-! ## The checker -/

/-- The committed subsets of `q` in setting `σ` usable after a right-only segment or at a
start. -/
def ChoiceData.repoSAt (ch : ChoiceData) (q : ℕ) (σ : SrcSetting) : List (List ℕ) := ch.repoS q σ
def ChoiceData.hopSAt (ch : ChoiceData) (q : ℕ) (σ : SrcSetting) : List (List ℕ) := ch.hopS q σ

/-- **Definition 8 with committed subsets, executable.** `decideCovered` plus the three
committed-subset rules; each subset must be nonempty and inside the rule's successor set. -/
def decideCoveredX (G : SearchGraph V) (ch : ChoiceData) : ℕ → Config → Bool
  | 0,        _      => false
  | fuel + 1, ⟨q, B, σ⟩ =>
      match G.modeAt q with
      | none   => false
      | some m =>
          (ch.jointOK q && decide (B ≤ m.weight))
          || (ch.jointOK q && decide (m.weight < B) &&
                (G.retainedSucc q).all (fun q' =>
                   decideCoveredX G ch fuel ⟨q', B - m.weight, SrcSetting.postJ⟩))
          || ((match σ with | .preJ => ch.repoPre q | .postJ => ch.repoPost q)
                && decide (0 < B) && !(G.exitSucc q).isEmpty &&
                (G.exitSucc q).all (fun q' => decideCoveredX G ch fuel ⟨q', B, σ⟩))
          || (ch.jointOK q && decide (m.weight < B) &&
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

/-- **Soundness of the extended checker**: acceptance implies `CoveredX`. -/
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
