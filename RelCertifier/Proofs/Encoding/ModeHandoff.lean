/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The mode-keyed Theorem 3 — composing per-left-mode ∀∃ theorems across left switches

A benchmark may declare one relational invariant per LEFT mode. Each left mode's window
family is certified at its own row (`theorem3_faithful_multiF_LR` and friends, one
`hstep` per left mode); what those per-mode statements leave open is the SWITCH: when the
left program moves from mode `m'` to a declared successor `m`, the state is unchanged and
only the left mode variable changes, so the new mode's row must already hold. That is the
paper's Theorem 3 in its general form:

> For every left mode `m_L`, every admissible initial right mode admits an all-successors
> cover at `φ_inv(m_L)` (hypothesis (i), the per-mode `hstep`); for every declared left
> transition `m' → m`, `φ_inv(m') ∧ guard_m → φ_inv(m)` (hypothesis (ii), the HANDOFF);
> then `Φ ≡ ⋀_m (u_L = m → φ_inv(m))` is a ∀∃ invariant: `Φ → [|(L*, R*)⟩⟩ Φ`.

This leaf states and proves exactly that. The left program is the LEFT AUTOMATON
`leftAutomatonBody`, mirroring the paper's `cpsProg` body
`⋃_m ?(m ∈ next(u_L)) ; ?guard_m(x) ; u_L := m ; {x' = f_m & evolC_m}` — jump, then flow —
with the per-mode flow being the clock-capped window family the per-mode theorems already
quantify over, and `u_L` a fresh `Aux` coordinate. The loop invariant is `Φ` plus the
bookkeeping the per-mode chains carry (`env`, the right-side `mvValid`/`mvRegion`, and
`u_L ∈ modes`). A MODE-INDEPENDENT invariant is the special case `F m = F` for all `m`, where
the handoff hypothesis is trivial.

The handoff hypothesis has two discharge routes: as a Z3 verdict on EXACTLY the query the
runner prints (`Trusted/Handoff.lean`'s `ihandoffQuery`, bridged by `handoff_of_unsat` —
the verdict-pin discipline), or in-kernel when the rows are constant-offset bounds or
nested conjunctions (`linarith`/membership; this is what the seven mode-dependent
benchmarks use, so their composed theorems add no verdict beyond the per-mode packs).

Trust base unchanged: the only axiom that can enter is `z3_unsat_sound`, and only through
`handoff_of_unsat` when a handoff is discharged by Z3. New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.EnvelopeChainM
import RelCertifier.Proofs.Encoding.EnvelopeChainR
import RelCertifier.Proofs.Encoding.CoverInstance
import RelCertifier.Trusted.Handoff

namespace RelCertifier
open DL DLCalTiming DLRel Set

variable {n : ℕ}

/-! ## The left automaton -/

/-- The left automaton as data: per left mode, its window program (the clock-capped
`windowSeg` the per-mode theorem quantifies over), its lowered guard, and its declared
successor indices (the file's `next` list). -/
structure LeftAut (n : ℕ) where
  windows : List (Program (Var n))
  guards  : List (Formula (Var n))
  next    : List (List ℕ)

namespace LeftAut

/-- Mode `m`'s window; out of range is the blocked program `?⊥`. -/
def window (A : LeftAut n) (m : ℕ) : Program (Var n) :=
  A.windows.getD m (Program.test (Formula.neg Formula.tt))

/-- Mode `m`'s lowered guard. -/
def guard (A : LeftAut n) (m : ℕ) : Formula (Var n) := A.guards.getD m Formula.tt

/-- Mode `m`'s declared successors. -/
def succ (A : LeftAut n) (m : ℕ) : List ℕ := A.next.getD m []

/-- The number of left modes. -/
def numModes (A : LeftAut n) : ℕ := A.windows.length

end LeftAut

/-- One left transition out of mode `m'` into `t`: `?guard_t ; u_L := t ; window_t`. -/
def leftEdge (A : LeftAut n) (ul : Var n) (t : ℕ) : Program (Var n) :=
  Program.seq (Program.test (A.guard t))
    (Program.seq (Program.assign ul (Term.const (t : ℝ))) (A.window t))

/-- The step at left mode `m'`: `?(u_L = m') ; ⋃_{t ∈ next m'} leftEdge t` — the paper's
`?(m ∈ next(u_L)) ; ?guard_m ; u_L := m ; flow_m`, with `?(u_L = m')` selecting the current
mode exactly as `modeStep` does on the right. -/
def leftModeStep (A : LeftAut n) (ul : Var n) (m' : ℕ) : Program (Var n) :=
  Program.seq (Program.test (modeIs ul m'))
    (bigChoiceP ((A.succ m').map (leftEdge A ul)))

/-- The left automaton body: the choice over all modes' steps (its star is `L*`). -/
def leftAutomatonBody (A : LeftAut n) (ul : Var n) : Program (Var n) :=
  bigChoiceP ((List.range A.numModes).map (leftModeStep A ul))

/-! ## The mode-keyed invariant, host and relational -/

/-- `⋀ fs`, as a right fold. -/
def bigAnd : List (Formula (Var n)) → Formula (Var n)
  | []      => Formula.tt
  | f :: fs => Formula.and f (bigAnd fs)

theorem sat_bigAnd {fs : List (Formula (Var n))} {ν : State (Var n)} :
    Formula.sat (bigAnd fs) ν ↔ ∀ f ∈ fs, Formula.sat f ν := by
  induction fs with
  | nil => simp [bigAnd, Formula.sat]
  | cons a as ih =>
      simp only [bigAnd, sat_and, ih, List.mem_cons, forall_eq_or_imp]

/-- `Φ ≡ ⋀_{m < nL} (u_L = m → F m)`, the paper's mode-keyed invariant at the host level. -/
def modeKeyed (ul : Var n) (F : ℕ → Formula (Var n)) (nL : ℕ) : Formula (Var n) :=
  bigAnd ((List.range nL).map (fun m => Formula.imp (modeIs ul m) (F m)))

theorem sat_modeIs {ul : Var n} {m : ℕ} {ν : State (Var n)} :
    Formula.sat (modeIs ul m) ν ↔ ν ul = (m : ℝ) := by
  simp only [modeIs, Formula.sat, CompOp.interp, Term.eval]

theorem sat_modeKeyed {ul : Var n} {F : ℕ → Formula (Var n)} {nL : ℕ} {ν : State (Var n)} :
    Formula.sat (modeKeyed ul F nL) ν ↔ ∀ m < nL, ν ul = (m : ℝ) → Formula.sat (F m) ν := by
  unfold modeKeyed
  rw [sat_bigAnd]
  constructor
  · intro h m hm hul
    have := h (Formula.imp (modeIs ul m) (F m)) (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩)
    rw [sat_imp] at this
    exact this (sat_modeIs.mpr hul)
  · intro h f hf
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hf
    rw [sat_imp]
    intro hul
    exact h m (List.mem_range.mp hm) (sat_modeIs.mp hul)

/-- `⋀ ϕs`, relational. -/
def rbigAnd : List (RFormula (Var n)) → RFormula (Var n)
  | []      => RFormula.tt
  | f :: fs => RFormula.and f (rbigAnd fs)

/-- The relational mode-keyed invariant: `⋀_m (⌊u_L = m⌋_L → ϕ m)`. -/
def modeKeyedR (ul : Var n) (ϕ : ℕ → RFormula (Var n)) (nL : ℕ) : RFormula (Var n) :=
  rbigAnd ((List.range nL).map (fun m =>
    RFormula.imp (RFormula.proj DLRel.Side.L (modeIs ul m)) (ϕ m)))

/-- `u_L ∈ modes`, as a left projection. -/
def ulValidL (ul : Var n) (nL : ℕ) : RFormula (Var n) :=
  RFormula.proj DLRel.Side.L (mvValid ul nL)

theorem encode_rbigAnd (fs : List (RFormula (Var n))) :
    encode (Equiv.refl (Var n)) (rbigAnd fs) = bigAnd (fs.map (encode (Equiv.refl (Var n)))) := by
  induction fs with
  | nil => rfl
  | cons a as ih =>
      show encode _ (RFormula.and a (rbigAnd as)) = Formula.and (encode _ a) (bigAnd _)
      rw [← ih]
      unfold encode
      simp only [RFormula.renameR, RFormula.enc]

theorem encode_imp_projL (a : Formula (Var n)) (ϕ : RFormula (Var n)) :
    encode (Equiv.refl (Var n)) (RFormula.imp (RFormula.proj DLRel.Side.L a) ϕ)
      = Formula.imp a (encode (Equiv.refl (Var n)) ϕ) := by
  unfold encode
  simp only [RFormula.imp, RFormula.or, Formula.imp, Formula.or, RFormula.renameR, RFormula.enc]

theorem encode_modeKeyedR (ul : Var n) (ϕ : ℕ → RFormula (Var n)) (F : ℕ → Formula (Var n))
    (nL : ℕ) (hψ : ∀ m, encode (Equiv.refl (Var n)) (ϕ m) = F m) :
    encode (Equiv.refl (Var n)) (modeKeyedR ul ϕ nL) = modeKeyed ul F nL := by
  unfold modeKeyedR modeKeyed
  rw [encode_rbigAnd, List.map_map]
  congr 1
  apply List.map_congr_left
  intro m _
  simp only [Function.comp_def, encode_imp_projL, hψ]

theorem encode_ulValidL (ul : Var n) (nL : ℕ) :
    encode (Equiv.refl (Var n)) (ulValidL ul nL) = mvValid ul nL := by
  unfold encode ulValidL
  simp only [RFormula.renameR, RFormula.enc]

/-! ## The loop invariant shapes -/

/-- The host loop invariant: `Φ ∧ env ∧ Bk ∧ u_L ∈ modes`, where `Bk` is the right-side
bookkeeping the per-mode chains carry (`mvValid mv k` for the F-chain, `mvRegion …` for the
R-chain). Each per-mode conjunct `F m ∧ env ∧ Bk` is exactly `phiInvF (F m) env mv k`,
respectively `phiInvR …`. -/
def phiInvK (ul : Var n) (F : ℕ → Formula (Var n)) (nL : ℕ) (env Bk : Formula (Var n)) :
    Formula (Var n) :=
  Formula.and (Formula.and (Formula.and (modeKeyed ul F nL) env) Bk) (mvValid ul nL)

/-- Its relational form, with the LR-split envelope. -/
def psiK (ul : Var n) (ϕ : ℕ → RFormula (Var n)) (nL : ℕ) (domL domR : Formula (Var n))
    (BkR : RFormula (Var n)) : RFormula (Var n) :=
  RFormula.and (RFormula.and (RFormula.and (modeKeyedR ul ϕ nL) (envLR domL domR)) BkR)
    (ulValidL ul nL)

theorem encode_psiK (ul : Var n) (ϕ : ℕ → RFormula (Var n)) (F : ℕ → Formula (Var n))
    (nL : ℕ) (domL domR : Formula (Var n)) (BkR : RFormula (Var n)) (Bk : Formula (Var n))
    (hψ : ∀ m, encode (Equiv.refl (Var n)) (ϕ m) = F m)
    (hB : encode (Equiv.refl (Var n)) BkR = Bk) :
    encode (Equiv.refl (Var n)) (psiK ul ϕ nL domL domR BkR)
      = phiInvK ul F nL (Formula.and domL domR) Bk := by
  have hdist : encode (Equiv.refl (Var n)) (psiK ul ϕ nL domL domR BkR)
      = Formula.and (Formula.and (Formula.and
          (encode (Equiv.refl (Var n)) (modeKeyedR ul ϕ nL))
          (encode (Equiv.refl (Var n)) (envLR domL domR)))
          (encode (Equiv.refl (Var n)) BkR))
        (encode (Equiv.refl (Var n)) (ulValidL ul nL)) := by
    unfold psiK encode; simp only [RFormula.renameR, RFormula.enc]
  rw [hdist, encode_modeKeyedR ul ϕ F nL hψ, encode_envLR, hB, encode_ulValidL]; rfl

/-! ## The step: one left-automaton iteration from per-mode steps and handoffs -/

/-- **The composition step.** From (i) a per-left-mode `hstep` at each mode's own row and
(ii) the handoff implication at every declared left transition, one iteration of the left
automaton preserves the mode-keyed loop invariant against `R*`.

The run of `leftAutomatonBody` from `σ` selects the current mode `m'` (`?(u_L = m')`), a
declared successor `t` whose guard holds at `σ`, sets `u_L := t`, and runs `window t`. The
handoff turns `F m'` at `σ` into `F t` at `σ`; the per-mode step at `t` produces the right
response; `u_L` survives the window (`hframes`) and the right response (`hulR`), so the
mode-keyed conjunct at the end reads `F t`, which the response established. -/
theorem hstep_modeKeyed (A : LeftAut n) (ul : Var n) (R : Program (Var n))
    (F : ℕ → Formula (Var n)) (env Bk : Formula (Var n))
    (hulF : ∀ m, ul ∉ (F m).fv) (hulenv : ul ∉ env.fv) (hulBk : ul ∉ Bk.fv)
    (hulG : ∀ t, ul ∉ (A.guard t).fv)
    (hframes : ∀ t, FramesMv (A.window t) ul)
    (hulR : ul ∉ R.bv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hstepM : ∀ t < A.numModes, ∀ σ, Formula.sat (Formula.and (Formula.and (F t) env) Bk) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (A.window t) (Program.star R)
        (Formula.and (Formula.and (F t) env) Bk)) σ)
    (hhand : ∀ m' < A.numModes, ∀ t ∈ A.succ m', ∀ ω,
      Formula.sat (F m') ω → Formula.sat (A.guard t) ω → Formula.sat (F t) ω) :
    ∀ σ, Formula.sat (phiInvK ul F A.numModes env Bk) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (leftAutomatonBody A ul) (Program.star R)
        (phiInvK ul F A.numModes env Bk)) σ := by
  intro σ hσ
  obtain ⟨⟨⟨hMK, henv⟩, hBk⟩, hul⟩ := hσ
  obtain ⟨m', hm', hulm'⟩ := sat_mvValid.mp hul
  rw [faModal_sat]
  intro ν hleft
  -- the left run: which mode step, which edge
  obtain ⟨p, hp, hsemp⟩ := bigChoiceP_sem_forward hleft
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨m'', _, rfl⟩ := hp
  obtain ⟨σ₁, ⟨hσ₁, htest⟩, hrest⟩ := hsemp
  subst hσ₁
  have hm''eq : m'' = m' := by
    have h1 : σ ul = (m'' : ℝ) := sat_modeIs.mp htest
    exact_mod_cast h1.symm.trans hulm'
  subst hm''eq
  obtain ⟨p₂, hp₂, hsem₂⟩ := bigChoiceP_sem_forward hrest
  simp only [List.mem_map] at hp₂
  obtain ⟨t, ht, rfl⟩ := hp₂
  obtain ⟨σ₂, ⟨hσ₂, hguard⟩, σ₃, hassign, hwin⟩ := hsem₂
  subst hσ₂
  have ht' : t < A.numModes := hnext m'' hm' t ht
  -- `σ₃ = σ[u_L ↦ t]`
  have hσ₃ : σ₃ = Function.update σ ul (t : ℝ) := by
    funext x
    by_cases hx : x = ul
    · subst hx
      rw [Function.update_self]
      simpa [Term.eval] using hassign.1
    · rw [Function.update_of_ne hx]
      exact hassign.2 x hx
  -- the handoff at the switch state
  have hFm' : Formula.sat (F m'') σ := (sat_modeKeyed.mp hMK) m'' hm' hulm'
  have hFt : Formula.sat (F t) σ := hhand m'' hm' t ht σ hFm' hguard
  -- transport to the post-switch state (nothing but `u_L` changed, and none of these read it)
  have hcoin : ∀ (G : Formula (Var n)), ul ∉ G.fv →
      (Formula.sat G σ₃ ↔ Formula.sat G σ) := by
    intro G hG
    rw [hσ₃]
    exact (Formula.coincidence G (fun y hy =>
      (Function.update_of_ne (fun hc => hG (by rw [← hc]; exact hy)) _ _).symm)).symm
  have hσ₃sat : Formula.sat (Formula.and (Formula.and (F t) env) Bk) σ₃ :=
    ⟨⟨(hcoin _ (hulF t)).mpr hFt, (hcoin _ hulenv).mpr henv⟩, (hcoin _ hulBk).mpr hBk⟩
  -- the per-mode step at the entered mode
  have hfa := hstepM t ht' σ₃ hσ₃sat
  rw [faModal_sat] at hfa
  obtain ⟨μ, hRμ, ⟨hFtμ, henvμ⟩, hBkμ⟩ := hfa ν hwin
  refine ⟨μ, hRμ, ?_⟩
  -- `u_L` at the end: framed by the window, untouched by the right response
  have hulμ : μ ul = (t : ℝ) := by
    have h1 : ν ul = σ₃ ul := hframes t σ₃ ν hwin
    rw [Program.rename_refl] at hRμ
    have h2 : ν ul = μ ul :=
      Program.bound_effect (Program.star R) hRμ ul (by simpa [Program.bv] using hulR)
    rw [← h2, h1, hσ₃, Function.update_self]
  refine ⟨⟨⟨?_, henvμ⟩, hBkμ⟩, ?_⟩
  · rw [sat_modeKeyed]
    intro m _ hμm
    have hmt : m = t := by exact_mod_cast hμm.symm.trans hulμ
    subst hmt
    exact hFtμ
  · rw [sat_mvValid]
    exact ⟨t, ht', hulμ⟩

/-! ## The per-mode steps, from the chains' providers -/

/-- A per-mode step for the F-chain from a single window's `Hmulti`-shaped provider
(the shape every multiF instance's `HmultiX` has, restricted to one window). -/
theorem hstepMode_multiF (G : SearchGraph (Var n)) (mv : Var n)
    (F env : Formula (Var n)) (P : Program (Var n))
    (hF : mv ∉ F.fv) (henv : mv ∉ env.fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframe : FramesMv P mv)
    (H : ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and F env) σ →
      ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
        (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and F env)) σ) :
    ∀ σ, Formula.sat (Formula.and (Formula.and F env) (mvValid mv G.modes.length)) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) P (Program.star (rightAutomatonBody G mv))
        (Formula.and (Formula.and F env) (mvValid mv G.modes.length))) σ := by
  intro σ hσ
  obtain ⟨q, hq, hmvq⟩ := sat_mvValid.mp hσ.2
  obtain ⟨segs, halign, hchain, hhead, hfa⟩ := H q hq σ hmvq hσ.1
  exact hstep_single_multiF G mv q F env P hF henv hframe hq hfresh htt hlt
    segs halign hchain hhead hmvq hfa

/-- The same for the region-carrying R-chain (`phiInvR`). -/
theorem hstepMode_multiR (G : SearchGraph (Var n)) (mv : Var n)
    (F env : Formula (Var n)) (regions : ℕ → Formula (Var n)) (P : Program (Var n))
    (hF : mv ∉ F.fv) (henv : mv ∉ env.fv) (hregf : ∀ q', mv ∉ (regions q').fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (hframe : FramesMv P mv)
    (H : ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and F env) (regions q)) σ →
      ∃ segs : List (ℕ × RMode (Var n) × REdge (Var n)),
        (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and F env) (regions (qfOf segs q)))) σ) :
    ∀ σ, Formula.sat (Formula.and (Formula.and F env) (mvRegion mv regions G.modes.length)) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) P (Program.star (rightAutomatonBody G mv))
        (Formula.and (Formula.and F env) (mvRegion mv regions G.modes.length))) σ := by
  intro σ hσ
  obtain ⟨q, hq, hmvq, hreg⟩ := sat_mvRegion.mp hσ.2
  obtain ⟨segs, halign, hchain, hhead, hfa⟩ := H q hq σ hmvq ⟨hσ.1, hreg⟩
  exact hstep_single_multiR G mv q F env regions P hF henv hregf hframe hq hfresh htt hlt
    segs halign hchain hhead hmvq hfa

/-! ## Theorem 3, mode-keyed -/

/-- **Theorem 3 for a mode-dependent invariant.** `Φ → [|(L*, R*)⟩⟩ Φ` with `L` the left
automaton (jump-then-flow over the declared transitions) and `Φ` the mode-keyed invariant
plus bookkeeping. The `hstep` is `hstep_modeKeyed`'s conclusion; the two disjointness
side conditions are discharged by `hd_modeKeyed` / `hddF_modeKeyed` below. -/
theorem theorem3_modeKeyed (A : LeftAut n) (ul : Var n) (G : SearchGraph (Var n)) (mv : Var n)
    (F : ℕ → Formula (Var n)) (ϕ : ℕ → RFormula (Var n))
    (domL domR : Formula (Var n)) (Bk : Formula (Var n)) (BkR : RFormula (Var n))
    (hψ : ∀ m, encode (Equiv.refl (Var n)) (ϕ m) = F m)
    (hB : encode (Equiv.refl (Var n)) BkR = Bk)
    (hd : Disjoint (Program.vars (leftAutomatonBody A ul))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hstep : ∀ σ, Formula.sat (phiInvK ul F A.numModes (Formula.and domL domR) Bk) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (leftAutomatonBody A ul)
        (Program.star (rightAutomatonBody G mv))
        (phiInvK ul F A.numModes (Formula.and domL domR) Bk)) σ)
    (hddF : Disjoint (faShape (Program.star (leftAutomatonBody A ul))
          (Program.star (rightAutomatonBody G mv))
          (psiK ul ϕ A.numModes domL domR BkR)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (leftAutomatonBody A ul))
          (Program.star (rightAutomatonBody G mv))
          (psiK ul ϕ A.numModes domL domR BkR)).varsR)) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody A ul) (rightAutomatonBody G mv)
      (psiK ul ϕ A.numModes domL domR BkR)) := by
  set ψpost := psiK ul ϕ A.numModes domL domR BkR with hψpost
  set Lp := Program.star (leftAutomatonBody A ul)
  set Rp := Program.star (rightAutomatonBody G mv)
  have hencψ : encode (Equiv.refl (Var n)) ψpost
      = phiInvK ul F A.numModes (Formula.and domL domR) Bk :=
    encode_psiK ul ϕ F A.numModes domL domR BkR Bk hψ hB
  intro bs
  rw [theorem3Form]
  refine (RFormula_sat_imp _ _ bs).mpr ?_
  intro hpre
  obtain ⟨ν, hbdg⟩ := exists_bridge (Equiv.refl (Var n))
    (faShape Lp Rp ψpost).varsL (faShape Lp Rp ψpost).varsR hddF bs
  have hbψ : Bridges (Equiv.refl (Var n)) ψpost.varsL ψpost.varsR bs ν :=
    hbdg.mono (varsL_subset_faShape Lp Rp ψpost) (varsR_subset_faShape Lp Rp ψpost)
  have hdψ : Disjoint ψpost.varsL (Equiv.refl (Var n) '' ψpost.varsR) :=
    hddF.mono (varsL_subset_faShape Lp Rp ψpost)
      (Set.image_mono (varsR_subset_faShape Lp Rp ψpost))
  have hInvν : Formula.sat (phiInvK ul F A.numModes (Formula.and domL domR) Bk) ν := by
    rw [← hencψ]
    exact (RFormula.encoding_correct (Equiv.refl (Var n)) ψpost hdψ bs ν hbψ).mp hpre
  exact relational_loop_multi (leftAutomatonBody A ul) (rightAutomatonBody G mv) ψpost ν bs hd
    (by rw [hencψ]; exact hInvν)
    (fun σ hσ => by rw [hencψ] at hσ ⊢; exact hstep σ hσ) hddF hbdg

/-! ## Side-split dischargers -/

/-- Variables of the left automaton body: `u_L`, the windows', the guards'. -/
theorem vars_leftAutomatonBody_sub (A : LeftAut n) (ul : Var n) (S : Set (Var n))
    (hul : ul ∈ S)
    (hwin : ∀ t < A.numModes, Program.vars (A.window t) ⊆ S)
    (hgrd : ∀ t < A.numModes, (A.guard t).fv ⊆ S)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes) :
    Program.vars (leftAutomatonBody A ul) ⊆ S := by
  refine vars_bigChoiceP_sub _ _ ?_
  intro p hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨m', hm', rfl⟩ := hp
  intro x hx
  rcases vars_seq_sub _ _ hx with hx | hx
  · -- the mode test reads `u_L`
    simp only [Program.vars, Program.fv, Program.bv, modeIs, Formula.fv, Term.fv,
      Set.union_empty, Set.mem_singleton_iff] at hx
    rw [hx]; exact hul
  · have hsub : Program.vars (bigChoiceP ((A.succ m').map (leftEdge A ul))) ⊆ S := by
      refine vars_bigChoiceP_sub _ _ ?_
      intro e he
      simp only [List.mem_map] at he
      obtain ⟨t, ht, rfl⟩ := he
      have ht' := hnext m' hm' t ht
      intro y hy
      rcases vars_seq_sub _ _ hy with hy | hy
      · simp only [Program.vars, Program.fv, Program.bv, Set.union_empty] at hy
        exact hgrd t ht' hy
      · rcases vars_seq_sub _ _ hy with hy | hy
        · simp only [Program.vars, Program.fv, Program.bv, Term.fv, Set.empty_union,
            Set.mem_singleton_iff] at hy
          rw [hy]; exact hul
        · exact hwin t ht' hy
    exact hsub hx

/-- Three auxiliary coordinates — `mv = (Aux, a)` on the right, `tg = (Aux, b)` and
`u_L = (Aux, c)` on the left — are pairwise distinct from the other side's, so left and
right footprints are disjoint. -/
theorem sides_disjoint3 {S T : Set (Var n)} (a b c : Fin n) (hba : b ≠ a) (hca : c ≠ a)
    (hS : S ⊆ ({((Side.Aux, b) : Var n), ((Side.Aux, c) : Var n)} : Set (Var n)) ∪ range Lv)
    (hT : T ⊆ {((Side.Aux, a) : Var n)} ∪ range Rv) : Disjoint S T := by
  rw [Set.disjoint_left]
  intro x hxS hxT
  rcases hS hxS with hx | ⟨i, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hT hxT with hx' | ⟨j, hj⟩
    · rw [Set.mem_singleton_iff] at hx'
      rcases hx with rfl | rfl
      · exact hba (by simpa [Prod.ext_iff] using hx')
      · exact hca (by simpa [Prod.ext_iff] using hx')
    · rcases hx with rfl | rfl <;> exact absurd hj (by simp [Rv, Prod.ext_iff])
  · rcases hT hxT with hx' | ⟨j, hj⟩
    · rw [Set.mem_singleton_iff] at hx'
      exact absurd hx' (by simp [Lv, Prod.ext_iff])
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])

/-- **The `hd` discharger**: the left automaton over `windowSeg` windows with left-only
guards is footprint-disjoint from the right automaton. -/
theorem hd_modeKeyed (A : LeftAut n) (G : SearchGraph (Var n)) (a b c : Fin n)
    (hba : b ≠ a) (hca : c ≠ a)
    (hwin : ∀ t < A.numModes, Program.vars (A.window t)
      ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv)
    (hgrd : ∀ t < A.numModes, (A.guard t).fv ⊆ range Lv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    Disjoint (Program.vars (leftAutomatonBody A ((Side.Aux, c) : Var n)))
      (Program.vars ((rightAutomatonBody G ((Side.Aux, a) : Var n)).rename
        (Equiv.refl (Var n)))) := by
  refine sides_disjoint3 a b c hba hca ?_ ?_
  · refine vars_leftAutomatonBody_sub A _ _ ?_ ?_ ?_ hnext
    · exact Or.inl (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))
    · intro t ht x hx
      rcases hwin t ht hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
    · intro t ht x hx
      exact Or.inr (hgrd t ht hx)
  · intro x hx
    rw [Program.rename_refl] at hx
    rcases vars_bodyU_sub G _ htt hRv hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx

theorem modeKeyedR_varsL_sub (ul : Var n) (ϕ : ℕ → RFormula (Var n)) (nL : ℕ)
    (S : Set (Var n)) (hul : ul ∈ S) (hϕ : ∀ m < nL, (ϕ m).varsL ⊆ S) :
    (modeKeyedR ul ϕ nL).varsL ⊆ S := by
  unfold modeKeyedR
  have key : ∀ ms : List ℕ, (∀ m ∈ ms, m < nL) →
      (rbigAnd (ms.map (fun m =>
        RFormula.imp (RFormula.proj DLRel.Side.L (modeIs ul m)) (ϕ m)))).varsL ⊆ S := by
    intro ms
    induction ms with
    | nil => intro _; simp [rbigAnd, RFormula.tt, RFormula.varsL, Formula.fv]
    | cons m ms ih =>
        intro hms x hx
        simp only [List.map_cons, rbigAnd, RFormula.varsL] at hx
        rcases hx with hx | hx
        · simp only [RFormula.imp, RFormula.or, RFormula.varsL, modeIs, Formula.fv, Term.fv,
            Set.union_empty, Set.mem_union, Set.mem_singleton_iff] at hx
          rcases hx with rfl | hx
          · exact hul
          · exact hϕ m (hms m List.mem_cons_self) hx
        · exact ih (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) hx
  exact key _ (fun m hm => List.mem_range.mp hm)

theorem modeKeyedR_varsR_sub (ul : Var n) (ϕ : ℕ → RFormula (Var n)) (nL : ℕ)
    (S : Set (Var n)) (hϕ : ∀ m < nL, (ϕ m).varsR ⊆ S) :
    (modeKeyedR ul ϕ nL).varsR ⊆ S := by
  unfold modeKeyedR
  have key : ∀ ms : List ℕ, (∀ m ∈ ms, m < nL) →
      (rbigAnd (ms.map (fun m =>
        RFormula.imp (RFormula.proj DLRel.Side.L (modeIs ul m)) (ϕ m)))).varsR ⊆ S := by
    intro ms
    induction ms with
    | nil => intro _; simp [rbigAnd, RFormula.tt, RFormula.varsR]
    | cons m ms ih =>
        intro hms x hx
        simp only [List.map_cons, rbigAnd, RFormula.varsR] at hx
        rcases hx with hx | hx
        · simp only [RFormula.imp, RFormula.or, RFormula.varsR, Set.empty_union] at hx
          exact hϕ m (hms m List.mem_cons_self) hx
        · exact ih (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) hx
  exact key _ (fun m hm => List.mem_range.mp hm)

theorem psiK_varsL_sub (ul : Var n) (ϕ : ℕ → RFormula (Var n)) (nL : ℕ)
    (domL domR : Formula (Var n)) (BkR : RFormula (Var n)) (S : Set (Var n))
    (hul : ul ∈ S) (hϕ : ∀ m < nL, (ϕ m).varsL ⊆ S) (hdomL : domL.fv ⊆ S)
    (hBk : BkR.varsL ⊆ S) :
    (psiK ul ϕ nL domL domR BkR).varsL ⊆ S := by
  intro x hx
  simp only [psiK, RFormula.varsL, ulValidL, envLR_varsL, Set.mem_union] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact modeKeyedR_varsL_sub ul ϕ nL S hul hϕ hx
  · exact hdomL hx
  · exact hBk hx
  · exact (mvValid_fv_sub ul nL hx) ▸ hul

theorem psiK_varsR_sub (ul : Var n) (ϕ : ℕ → RFormula (Var n)) (nL : ℕ)
    (domL domR : Formula (Var n)) (BkR : RFormula (Var n)) (S : Set (Var n))
    (hϕ : ∀ m < nL, (ϕ m).varsR ⊆ S) (hdomR : domR.fv ⊆ S) (hBk : BkR.varsR ⊆ S) :
    (psiK ul ϕ nL domL domR BkR).varsR ⊆ S := by
  intro x hx
  simp only [psiK, RFormula.varsR, ulValidL, envLR_varsR, Set.mem_union,
    Set.mem_empty_iff_false, or_false] at hx
  rcases hx with ((hx | hx) | hx)
  · exact modeKeyedR_varsR_sub ul ϕ nL S hϕ hx
  · exact hdomR hx
  · exact hBk hx

/-- **The `hddF` discharger** for the mode-keyed shape. -/
theorem hddF_modeKeyed (A : LeftAut n) (G : SearchGraph (Var n)) (a b c : Fin n)
    (hba : b ≠ a) (hca : c ≠ a)
    (ϕ : ℕ → RFormula (Var n)) (domL domR : Formula (Var n)) (BkR : RFormula (Var n))
    (hwin : ∀ t < A.numModes, Program.vars (A.window t)
      ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv)
    (hgrd : ∀ t < A.numModes, (A.guard t).fv ⊆ range Lv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv)
    (hϕL : ∀ m < A.numModes, (ϕ m).varsL ⊆ range Lv)
    (hϕR : ∀ m < A.numModes, (ϕ m).varsR ⊆ range Rv)
    (hdomLv : domL.fv ⊆ range Lv) (hdomRv : domR.fv ⊆ range Rv)
    (hBkL : BkR.varsL = ∅)
    (hBkR : BkR.varsR ⊆ {((Side.Aux, a) : Var n)} ∪ range Rv) :
    Disjoint (faShape (Program.star (leftAutomatonBody A ((Side.Aux, c) : Var n)))
        (Program.star (rightAutomatonBody G ((Side.Aux, a) : Var n)))
        (psiK ((Side.Aux, c) : Var n) ϕ A.numModes domL domR BkR)).varsL
      (Equiv.refl (Var n) '' (faShape (Program.star (leftAutomatonBody A ((Side.Aux, c) : Var n)))
        (Program.star (rightAutomatonBody G ((Side.Aux, a) : Var n)))
        (psiK ((Side.Aux, c) : Var n) ϕ A.numModes domL domR BkR)).varsR) := by
  rw [show ∀ S : Set (Var n), Equiv.refl (Var n) '' S = S by intro S; simp]
  refine sides_disjoint3 a b c hba hca ?_ ?_
  · rw [faShape_varsL', pvars_star']
    refine Set.union_subset ?_ ?_
    · refine vars_leftAutomatonBody_sub A _ _ ?_ ?_ ?_ hnext
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))
      · intro t ht x hx
        rcases hwin t ht hx with hx | hx
        · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
        · exact Or.inr hx
      · intro t ht x hx
        exact Or.inr (hgrd t ht hx)
    · refine psiK_varsL_sub _ ϕ _ domL domR BkR _ ?_ ?_ ?_ ?_
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))
      · intro m hm x hx; exact Or.inr (hϕL m hm hx)
      · intro x hx; exact Or.inr (hdomLv hx)
      · rw [hBkL]; exact Set.empty_subset _
  · rw [faShape_varsR', pvars_star']
    refine Set.union_subset ?_ ?_
    · intro v hv
      rcases vars_bodyU_sub G _ htt hRv hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr hv
    · refine psiK_varsR_sub _ ϕ _ domL domR BkR _ ?_ ?_ hBkR
      · intro m hm x hx; exact Or.inr (hϕR m hm hx)
      · intro x hx; exact Or.inr (hdomRv hx)

/-- A left mode's lowered guard reads only left coordinates (the guard mentions no
`R_`-prefixed name — kernel-checked per instance by `decide`/`simp` on the IR literal). -/
theorem hostGuard_fv_L (vars : List String) (m : Parse.PMode)
    (hfree : Parse.PForm.namesFree "R_" m.guard = true) :
    (hostGuard vars n Side.L m).fv ⊆ range Lv := by
  intro x hx
  unfold hostGuard at hx
  rcases hlow : Run.lowerF vars n Side.L m.guard with _ | ff
  · rw [hlow] at hx; exact absurd hx (by simp [Formula.fv])
  · rw [hlow, Option.map_some, Option.getD_some] at hx
    exact side_eq_L_mem (Run.lowerF_fv_side (resolvesTo_L vars) hfree hlow x hx)

/-- The right automaton body writes only `mv` and right coordinates, so a left-side
auxiliary is never bound by it. -/
theorem notMem_bv_rightAutomatonBody (G : SearchGraph (Var n)) (mv : Var n) (x : Var n)
    (hx : x ≠ mv) (hxR : x ∉ range Rv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hRv : ∀ q m, G.modeAt q = some m →
      m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv) :
    x ∉ (rightAutomatonBody G mv).bv := by
  intro h
  have hv : x ∈ Program.vars (rightAutomatonBody G mv) := Or.inr h
  rcases vars_bodyU_sub G mv htt hRv hv with hx' | hx'
  · exact hx (Set.mem_singleton_iff.mp hx')
  · exact hxR hx'

/-! ## The handoff hypothesis from the runner's query

`Trusted/Handoff.lean`'s `ihandoffQuery` is what `relcert --run-verdicts` prints to Z3 for
each declared left transition. Its host denotation says: no state satisfies the source
row, the target guard, and the negated target row — i.e. the handoff implication. -/

theorem sat_iinvConj_toHost (comps : List (ITerm n)) (base : IForm n) (σ : State (Var n)) :
    Formula.sat (Handoff.iinvConj comps base).toHost σ ↔
      Formula.sat base.toHost σ ∧ ∀ g ∈ comps, Term.eval g.toHost σ ≤ 0 := by
  induction comps generalizing base with
  | nil => simp [Handoff.iinvConj]
  | cons g gs ih =>
      show Formula.sat (Handoff.iinvConj gs (IForm.and base (IForm.cmp .le g (.rat 0)))).toHost σ
        ↔ _
      rw [ih]
      simp only [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
        Rat.cast_zero, List.mem_cons, forall_eq_or_imp]
      tauto

/-- **The handoff implication from a Z3 `unsat` on the runner's query.** `cs`/`ct` are the
lowered components of the source/target rows and `gT` the lowered target guard — exactly
what `ihandoffQuery` assembles. -/
theorem handoff_of_unsat (cs ct : List (ITerm n)) (gT : IForm n)
    (hz : z3solve (IForm.and (Handoff.iinvConj cs gT)
      (IForm.neg (Handoff.iinvConj ct IForm.tt))).toHost = Verdict.unsat) :
    ∀ σ : State (Var n), (∀ g ∈ cs, Term.eval g.toHost σ ≤ 0) → Formula.sat gT.toHost σ →
      ∀ g ∈ ct, Term.eval g.toHost σ ≤ 0 := by
  intro σ hsrc hg
  by_contra hneg
  apply z3_unsat_sound hz σ
  refine ⟨(sat_iinvConj_toHost cs gT σ).mpr ⟨hg, hsrc⟩, ?_⟩
  show ¬ Formula.sat (Handoff.iinvConj ct IForm.tt).toHost σ
  rw [sat_iinvConj_toHost]
  exact fun h => hneg h.2

/-- `ihandoffQuery` unfolded: its pieces, when it lowers. -/
theorem ihandoffQuery_eq {vars : List String} {invSrc guardT invTgt : Parse.PForm}
    {q : IForm n} (hq : Handoff.ihandoffQuery vars n invSrc guardT invTgt = some q) :
    ∃ cs gT ct, Oracle.invComponents vars n invSrc = some cs ∧
      Run.lowerF vars n Side.L guardT = some gT ∧
      Oracle.invComponents vars n invTgt = some ct ∧
      q = IForm.and (Handoff.iinvConj cs gT) (IForm.neg (Handoff.iinvConj ct IForm.tt)) := by
  unfold Handoff.ihandoffQuery at hq
  rcases h1 : Oracle.invComponents vars n invSrc with _ | cs
  · rw [h1] at hq; simp at hq
  rcases h2 : Run.lowerF vars n Side.L guardT with _ | gT
  · rw [h1, h2] at hq; simp at hq
  rcases h3 : Oracle.invComponents vars n invTgt with _ | ct
  · rw [h1, h2, h3] at hq; simp at hq
  rw [h1, h2, h3] at hq
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hq
  exact ⟨cs, gT, ct, rfl, rfl, rfl, hq.symm⟩

end RelCertifier
