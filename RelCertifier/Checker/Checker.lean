/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The verified cover checker: from the runner's cover to the soundness theorem

The runner **proposes** a cover (untrusted search: stretch grid, mode facts, pruning, the
depth-first cover walk); a **verified, computable checker validates** it, and CERTIFIED means
*the verified checker accepted it*. A runner bug (bad search, wrong domain, guard narrowing)
can then only make the checker **reject** (a false decline), never a false CERTIFIED
(Section 6.1, Appendix B.4: the cover is outside the trusted base).

* `decideCovered` — a **computable** re-validation of the runner's cover derivation
  (Definition 8, retained successors only): budget arithmetic, `0 < weight`, the
  every-retained-successor condition. It runs.
* `decideCovered_sound` — accepting implies the proof-level `Covered` relation.
* `check_sound` — accepting (plus the flow certificates as `CoverCert`) implies the
  semantic ∀∃-throughout invariant `CoexecInvThroughout`, **by citing
  `cover_sound_throughout`**, so the checker's dependency trace contains that theorem
  (kernel-enforced).

The committed-subset extension is `decideCoveredX` (`Checker/CoverX.lean`).
-/
import RelCertifier.Checker.Cover.Coexec
import RelCertifier.Trusted.Smt

namespace RelCertifier

open DL

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The computable cover checker (re-validates the runner's untrusted search) -/

/-- **Computable** re-validation of a `Covered` derivation: the two cases of **Definition 8**
(retained successors as landing sets), executable and fuel-bounded (the fuel is the
runner-supplied derivation height; `decideCovered_sound` needs only that it suffices):

* **finish** — joint-certified and `B ≤ m.weight`: one joint segment finishes the budget →
  accept, **without** examining successors.
* **continue, joint** — joint-certified and `m.weight < B`: accept iff **every** retained
  successor validates at the decremented budget, post-joint.
* **continue, right-only** — the right-only certificate of the current source setting,
  `0 < B`, a nonempty `exitSucc`: accept iff every non-self retained successor validates at
  the same budget and setting.

No `noncomputable`, no classical choice: this function *runs* on the runner's certificate. -/
def decideCovered (G : SearchGraph V) : ℕ → Config → Bool
  | 0,        _      => false
  | fuel + 1, ⟨q, B, σ⟩ =>
      match G.modeAt q with
      | none   => false
      | some m =>
          -- finish (Definition 8): joint-supported and one joint segment closes the budget
          (m.jointOK && decide (B ≤ m.weight))
          -- continue, joint (Definition 8): budget remains, all retained successors cover at
          -- B−weight, σ flips to postJ
          || (m.jointOK && decide (m.weight < B) &&
                (G.retainedSucc q).all (fun q' =>
                   decideCovered G fuel ⟨q', B - m.weight, SrcSetting.postJ⟩))
          -- continue, right-only (Definition 8), by source setting (`repoDynPreOK`/
          -- `repoDynPostOK`): zero budget, `exitSucc` nonempty (no vacuous dead-end cover),
          -- all non-self retained successors cover at the SAME budget `B` and SAME `σ` (the
          -- left is held, so σ is kept). There is no zero-duration right-only step.
          || ((match σ with | .preJ => m.repoDynPreOK | .postJ => m.repoDynPostOK)
                && decide (0 < B) && !(G.exitSucc q).isEmpty &&
                (G.exitSucc q).all (fun q' => decideCovered G fuel ⟨q', B, σ⟩))

/-- **Soundness of the checker's structural half.** If `decideCovered` accepts, the
proof-level `Covered` relation holds — so the runner's (untrusted) search result is
re-validated into a Definition 8 derivation (finish or continue). -/
theorem decideCovered_sound (G : SearchGraph V) :
    ∀ (fuel : ℕ) (cfg : Config), decideCovered G fuel cfg = true → Covered G cfg := by
  intro fuel
  induction fuel with
  | zero => intro cfg h; simp [decideCovered] at h
  | succ f ih =>
      rintro ⟨q, B, σ⟩ h
      simp only [decideCovered] at h
      cases hm : G.modeAt q with
      | none => rw [hm] at h; simp at h
      | some m =>
          rw [hm] at h
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with (⟨hj, hle⟩ | ⟨⟨hj, hlt⟩, hall⟩) | ⟨⟨⟨hrepo, hB⟩, hne'⟩, hall⟩
          · exact Covered.base m hm hj hle                              -- finish (joint)
          · refine Covered.step m hm hj hlt ?_                          -- continue, joint (successors postJ)
            intro q' hq'; exact ih _ (List.all_eq_true.mp hall q' hq')
          · -- continue, right-only, by source setting
            have hne : G.exitSucc q ≠ [] := by intro hnil; rw [hnil] at hne'; simp at hne'
            cases σ with
            | preJ =>
                refine Covered.stepRepositionDynPre m hm hrepo hB hne ?_
                intro q' hq'; exact ih _ (List.all_eq_true.mp hall q' hq')
            | postJ =>
                refine Covered.stepRepositionDynPost m hm hrepo hB hne ?_
                intro q' hq'; exact ih _ (List.all_eq_true.mp hall q' hq')

/-! ## `check_sound` — CERTIFIED provably implies the ∀∃-throughout invariant -/

/-- **The checker's soundness (the runner↔theorem connection).** If the computable
`decideCovered` accepts the runner's cover derivation, and the flow certificates
(Definition 5) hold as a `CoverCert` (each `segPres` a `flow_cert_sound` `BoxLe` on the
mode's **evolution** domain, see the domain note below), then from any invariant-satisfying
entry the semantic ∀∃-throughout invariant `CoexecInvThroughout` holds.

It cites `cover_sound_throughout` (hence `cover_sound`, `flow_cert_sound`, the `DI` family):
a runner that proposes a bad derivation makes `decideCovered` return `false`, never reaching
this conclusion. The verified checker governs the output; the runner's search is outside the
trusted base. -/
theorem check_sound (G : SearchGraph V) (g : Term V) (cert : CoverCert G g)
    (fuel : ℕ) (cfg : Config) (hchk : decideCovered G fuel cfg = true)
    (ν : State V) (hinit : InvHolds g ν) :
    CoexecInvThroughout G g cfg ν :=
  cover_sound_throughout G g cert cfg ν (decideCovered_sound G fuel cfg hchk) hinit

/-! ## Why a guard-narrowed domain cannot certify

`check_sound`'s conclusion is `CoexecInvThroughout G g cfg ν = ∀ ω, RightReach G cfg ν ω →
InvHolds g ω`, and `RightReach`'s `evolve` step is `Program.sem (Program.ode m.sys m.dom)` —
i.e. the co-execution on the mode's domain `m.dom`. To obtain `cert : CoverCert G g` one must
provide `SegPreserves g m = ∀ ν, InvHolds g ν → BoxLe (ode m.sys m.dom) ⟦g⟧ ν`, discharged by
`flow_cert_sound` — whose conclusion is a `BoxLe` on **exactly** the flow obligation's domain.

So the SAME `m.dom` appears in the flow certificate and in the co-execution. A guard-narrowed
domain would prove `SegPreserves` on the narrow region, but then `CoexecInvThroughout` is about
the *narrow-domain* `RightReach`, not the real evolution-domain co-execution — a different,
weaker statement. The checker therefore rejects any segment whose flow-certificate domain is
not the evolution domain (`decideSegDomain` below): the evolution-domain cert is the only one
whose `CoexecInvThroughout` conclusion is the real co-execution. -/

/-- Computable domain check (over the runner's decidable `ℚ`-based IR): the segment's
flow-certificate domain must be the mode's evolution domain. A guard-narrowed domain
(`evolve ∧ guard`) is a *different* `IForm`, so this returns `false` — the guard-bug class
is a rejection, not a false certification. The host `Formula` carries `ℝ` constants and is
not decidable-eq, which is exactly why the runner (and the checker) work over the IR. -/
def decideSegDomain {n : ℕ} (segDomain evolutionDomain : IForm n) : Bool :=
  decide (segDomain = evolutionDomain)

end RelCertifier
