> **HISTORY (moved to `docs/history/` on 2026-10-10).** A superseded record, kept for
> provenance; `docs/history/README.md` says what replaced it. Paths, file names and counts
> below describe the repository at the time of writing, not the current artifact.

# Scope: proving the two automaton shapes equivalent on admissible starts

Status: SCOPING ONLY (2026-07-19, against main = be3765f). Nothing implemented, nothing
scheduled. Companion reading: `docs/COVER-AUDIT.md` (the guard note — a *different*
question, see §5), `docs/RESET-MAPS-SCOPE.md`.

## 1. The two shapes

**(1) — what the mechanization uses.** `modeStep` / `rightAutomatonBody`
(`Proofs/Encoding/JointBridge.lean:34,41`), flow-then-jump:

```
R₁ = ( ⋃_q  ?(mv = q) ; {x' = f_q & evolC_q} ; ⋃_{e ∈ edgesFrom q} ( ?e.guard ; mv := e.tgt ) )*
```

**(2) — what the paper displays**, jump-then-flow:

```
R₂ = ( ⋃_m  ?(m ∈ next(mv)) ; ?guard_m(x) ; mv := m ; {x' = f_m & evolC_m} )*
```

Goal: a kernel-checked lemma saying these agree on admissible starts, so the paper may
present (2) while the development proves (1).

## 2. Why this is modest: the shapes are an exact algebraic rotation

The mode-dependence looks like an obstacle — "the flow depends on which mode we are in,
so there is no fixed `A` and `B`" — but it is not, because `mv` is *state*. Define two
**fixed** programs:

```
Flow := ⋃_q ( ?(mv = q) ; {x' = f_q & evolC_q} )
Jump := ⋃_q ⋃_{e ∈ edgesFrom q} ( ?(mv = q) ; ?e.guard ; mv := e.tgt )
```

Then, using that `Flow` does not modify `mv` (exactly `MVFresh`,
`JointBridge.lean:52` — already a hypothesis in this development):

* `R₁ body = Flow ; Jump` — after `Flow`, `mv` is unchanged, so `Jump`'s `?(mv = q)`
  selects the same `q` the flow used.
* `R₂ body = Jump ; Flow` — after `Jump`, `mv = e.tgt`, so `Flow` flows in the entered
  mode, and `?(m ∈ next(mv)) ; ?guard_m` is precisely `Jump`'s edge selection with the
  target's guard.

So the whole question collapses to one standard relational identity:

```
(A ; B)* ; A   =   A ; (B ; A)*
```

Unfolded: `(Flow;Jump)ⁿ ; Flow = F₁J₁F₂J₂…FₙJₙFₙ₊₁ = Flow ; (Jump;Flow)ⁿ`. Same
trajectory, different parsing — which is the precise content of "equivalent up to a
leading/trailing segment".

## 3. Every ingredient already exists

| needed | where |
|---|---|
| `sem_test`, `sem_seq`, `sem_choice` (simp) | `dL-lean/DLLean/Metatheory.lean:33,36,39` |
| `sem (star α) = Relation.ReflTransGen (sem α)` — full Mathlib API (`head`, `tail`, `cases_head`, `head_induction_on`) | `dL-lean/DLLean/Loop.lean:26` |
| build a big-choice run | `bigChoiceP_sem_of_mem`, `JointBridge.lean:62` |
| destruct a big-choice run | `bigChoiceP_sem_forward`, `BridgeReposition.lean:287` |
| `mv` untouched by flows and guards | `MVFresh`, `JointBridge.lean:52` |
| every mode has a `⊤`-guarded self-edge (the padding mechanism) | `SelfEdges`, `JointBridge.lean:57`; R1 verified every benchmark mode declares itself in `next` |

**The decisive precedent.** `rightReach_is_R_real_run` (`JointBridge.lean:114`) already
does the structurally harder half of this job: it converts a *parsing-agnostic* reach
relation into a *parsed* form-(1) program run,

```lean
theorem rightReach_is_R_real_run (G : SearchGraph V) (mv : V)
    (hnorepo : NoRepoModes G) (hfresh : MVFresh G mv) (hself : SelfEdges G) :
    ∀ {cfg : Config} {ν ω : State V}, RightReach G cfg ν ω →
      ∃ qf : ℕ, Program.sem (R_real G mv)
        (update ν mv (cfg.q : ℝ)) (update ω mv (qf : ℝ))
```

in roughly 55–70 lines, using `SelfEdges` to pad the iteration boundary. That is the
template, and the padding trick is exactly what a rotation needs — only at the other
end.

## 4. Two routes, and the estimate

**Route A — the algebraic rotation (recommended, reusable).**

1. The relational identity `ReflTransGen (RA ∘ RB) ∘ RA = RA ∘ ReflTransGen (RB ∘ RA)`,
   by induction on the closure in both directions. **40–80 lines**, no project-specific
   content, low risk.
2. The decomposition lemmas `R₁ body = Flow ; Jump` and `R₂ body = Jump ; Flow`. This is
   the fiddliest part — regrouping nested `bigChoiceP`s and threading `mv`-preservation
   through the `?(mv = q)` tests. Both big-choice directions already exist, so it is
   bookkeeping rather than invention. **80–150 lines**.
3. Boundary/admissible-start wrapper: the leading (or trailing) segment, discharged by
   the zero-duration flow (needs `evolC_{q₀}` at the start) and the `SelfEdges` padding
   (mirroring `rightReach_is_R_real_run`). **40–80 lines**.

**Route B — mimic the precedent.** Skip the algebra and prove
`rightReach_is_R_real₂_run` directly, by the same induction as the existing lemma,
padding with a *leading* self-jump instead of a trailing one. Comparable size to the
existing proof (~70 lines) and more direct if all you want is the ∀-families — but it
yields no reusable identity and would have to be repeated for the modal statement.

**Total for Route A: ~200–300 lines, one to two focused days, low risk.**

**Rebuild cost: none.** All of it lands as a *new* file importing `JointBridge`; no
existing definition changes. This is the rare piece of work in this project that is
purely additive.

## 5. What this does NOT settle (read before relying on it)

The rotation justifies the **shape** change, not the **guard** change. Every
constructed graph sets `e.guard := Formula.tt` (`docs/COVER-AUDIT.md`), so the lemma as
scoped here relates form (1) and form (2) *over the same graph* — both with trivial edge
guards. If the paper displays (2) with a real `?guard_m(x)` test, the rotation does not
cover that step; that is the separate question the audit note handles, whose resolution
is an assumptions line (non-blocking) rather than proof work.

Also worth knowing: the direction asymmetry noted earlier in discussion is an artifact
of the guard mismatch, not of the rotation. With guards *matched* on both sides (both
`⊤`, or both real), the identity in §2 is symmetric and both directions fall out of the
same induction. The asymmetry only appears when (2) carries real guards and (1) does
not — then (2) ⊆ (1) is free (dropping tests) and (1) ⊆ (2) needs guard-legality.

## 6. Recommendation

Worth doing if you want the paper's form-(2) presentation *proven* rather than asserted:
it is cheap, additive, needs no rebuild, and the precedent lemma is a working template.
If you would rather not spend the two days, asserting the rotation in one sentence is
defensible — it is a standard and eye-checkable equivalence — but the proven version
costs little and removes a reviewer question.

The one thing to verify before starting, since it is the only unknown: that the
zero-duration flow at an admissible start is available, i.e. that admissible starts
satisfy the initial mode's evolution domain (`evolC_{q₀}`), not merely its guard and the
invariant. R2's admissible-start conditioning is `SAT guardL ∧ guardR ∧ ϕ_rel`; whether
the evolution domain is implied there should be checked rather than assumed.
