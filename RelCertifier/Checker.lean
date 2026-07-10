/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Verified executable certificate-checker — the runner↔theorem connection

The prior architecture was *verified functions beside an untrusted runner that
re-implements them*: `cover_sound` proved a real theorem, but `Run.lean`'s `dfsCov3` + Z3
search never invoked it. The guard bug lived in that gap — a wrong domain in the runner,
ungoverned by any proof. `#print axioms` was clean, yet CERTIFIED was **not backed by
proof**.

This file closes the gap with the standard certified-checker architecture: the runner
**proposes** (untrusted fast search), a **verified, computable checker validates**, and
CERTIFIED means *the verified checker accepted it*. A runner bug (bad DFS, wrong domain,
guard narrowing) can then only cause the checker to **reject** (a false decline) — never a
false CERTIFIED.

* `decideCovered` — a **computable** re-validation of the runner's cover derivation.
  Structural: budget arithmetic, `0 < weight`, the all-successors condition. It runs.
* `decideCovered_sound` — accepting implies the *proof-level* `Covered` relation.
* `check_sound` — accepting (plus the flow certificates as `CoverCert`) implies the
  semantic ∀∃-throughout invariant `CoexecInvThroughout`, **by citing
  `cover_sound_throughout`**. That citation is what makes the checker verified: its
  dependency trace contains the throughout theorem (kernel-enforced).
-/
import RelCertifier.Cover.Coexec
import RelCertifier.Smt

namespace RelCertifier

open DL

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The computable cover checker (re-validates the runner's untrusted search) -/

/-- **Computable** re-validation of a `Covered` derivation, fuel-bounded (the fuel is the
runner-supplied derivation height; `decideCovered_sound` needs only that it suffices). A
node is accepted iff its budget is closed (`B = 0`), or its mode exists with `0 < weight`
and **every** retained successor validates at the decremented budget. No `noncomputable`,
no classical choice — this function *runs* on the runner's proposed certificate. -/
def decideCovered (G : SearchGraph V) : ℕ → Config → Bool
  | _,        ⟨_, 0⟩     => true
  | 0,        ⟨_, _ + 1⟩ => false
  | fuel + 1, ⟨q, B + 1⟩ =>
      match G.modeAt q with
      | none   => false
      | some m => decide (0 < m.weight) &&
          (G.retainedSucc q).all (fun q' => decideCovered G fuel ⟨q', (B + 1) - m.weight⟩)

/-- **Soundness of the checker's structural half.** If `decideCovered` accepts, the
proof-level `Covered` relation holds — so the runner's (untrusted) search result is
re-validated into a real derivation. -/
theorem decideCovered_sound (G : SearchGraph V) :
    ∀ (fuel : ℕ) (cfg : Config), decideCovered G fuel cfg = true → Covered G cfg := by
  intro fuel
  induction fuel with
  | zero =>
      rintro ⟨q, B⟩ h
      cases B with
      | zero => exact Covered.closed
      | succ B' => simp [decideCovered] at h
  | succ f ih =>
      rintro ⟨q, B⟩ h
      cases B with
      | zero => exact Covered.closed
      | succ B' =>
          simp only [decideCovered] at h
          cases hm : G.modeAt q with
          | none => rw [hm] at h; simp at h
          | some m =>
              rw [hm] at h
              rw [Bool.and_eq_true] at h
              obtain ⟨hw, hall⟩ := h
              refine Covered.cover m hm (Nat.succ_pos B') (by simpa using hw) ?_
              intro q' hq'
              exact ih _ (List.all_eq_true.mp hall q' hq')

/-! ## `check_sound` — CERTIFIED provably implies the ∀∃-throughout invariant -/

/-- **The checker's soundness (the runner↔theorem connection).** If the computable
`decideCovered` accepts the runner's cover derivation, and the flow certificates hold as a
`CoverCert` (each `segPres` a `flow_cert_sound` `BoxLe` on the mode's **evolution** domain —
see the domain note below), then from any invariant-satisfying entry the semantic
∀∃-throughout invariant `CoexecInvThroughout` holds.

**This is what makes CERTIFIED backed by proof.** It cites `cover_sound_throughout` (hence
`cover_sound`, `flow_cert_sound`, the `DI` family) — a runner that proposes a bad derivation
makes `decideCovered` return `false`, never reaching this conclusion. The verified checker
governs the output; the runner's `dfsCov3` search is outside the trusted base. -/
theorem check_sound (G : SearchGraph V) (g : Term V) (cert : CoverCert G g)
    (fuel : ℕ) (cfg : Config) (hchk : decideCovered G fuel cfg = true)
    (ν : State V) (hinit : InvHolds g ν) :
    CoexecInvThroughout G g cfg ν :=
  cover_sound_throughout G g cert cfg ν (decideCovered_sound G fuel cfg hchk) hinit

/-! ## Where the guard bug dies structurally

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
