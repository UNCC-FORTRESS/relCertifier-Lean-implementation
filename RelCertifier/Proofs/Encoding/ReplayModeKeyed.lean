/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The cover replays, carried to the mode-keyed left automaton

A cover replay answers a GATED left window: the entered mode's guard holds at the window's
start (the packs' domains carry the left cut atoms the guard implies). The mode-keyed
instances state their left automaton with plain windows and the lowered guards on the edges
(`leftEdge t = ?guard_t ; u_L := t ; window_t`), so the guard does hold at the window's start;
`hstep_modeKeyed` forgets it. `hstep_modeKeyed_g` is the same assembly with the per-mode step
given the entered mode's guard, and `faModal_ungate` turns a step over the gated window into
one over the plain window wherever the guard holds.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.GuardedSwitch

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-- **A step over the gated window is a step over the plain window where the guard holds.** -/
theorem faModal_ungate {φ : Formula (Var n)} {P R : Program (Var n)} {post : Formula (Var n)}
    {σ : State (Var n)} (hφ : Formula.sat φ σ)
    (h : Formula.sat (faModal (Equiv.refl (Var n)) (Program.seq (Program.test φ) P) R post) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) P R post) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  exact h ν ⟨σ, ⟨rfl, hφ⟩, hν⟩

/-- **`hstep_modeKeyed` with the entered mode's guard**: the per-mode step may assume the
guard of the mode it enters (the edge tests it, and it does not read `u_L`). -/
theorem hstep_modeKeyed_g (A : LeftAut n) (ul : Var n) (R : Program (Var n))
    (F : ℕ → Formula (Var n)) (env Bk : Formula (Var n))
    (hulF : ∀ m, ul ∉ (F m).fv) (hulenv : ul ∉ env.fv) (hulBk : ul ∉ Bk.fv)
    (hulG : ∀ t, ul ∉ (A.guard t).fv)
    (hframes : ∀ t, FramesMv (A.window t) ul)
    (hulR : ul ∉ R.bv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hstepM : ∀ t < A.numModes, ∀ σ, Formula.sat (Formula.and (Formula.and (F t) env) Bk) σ →
      Formula.sat (A.guard t) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (A.window t) (Program.star R)
        (Formula.and (Formula.and (F t) env) Bk)) σ)
    (hhand : ∀ m' < A.numModes, ∀ t ∈ A.succ m', ∀ ω,
      Formula.sat (F m') ω → Formula.sat env ω → Formula.sat (A.guard t) ω →
      Formula.sat (F t) ω) :
    ∀ σ, Formula.sat (phiInvK ul F A.numModes env Bk) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (leftAutomatonBody A ul) (Program.star R)
        (phiInvK ul F A.numModes env Bk)) σ := by
  intro σ hσ
  obtain ⟨⟨⟨hMK, henv⟩, hBk⟩, hul⟩ := hσ
  obtain ⟨m', hm', hulm'⟩ := sat_mvValid.mp hul
  rw [faModal_sat]
  intro ν hleft
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
  have hσ₃ : σ₃ = Function.update σ ul (t : ℝ) := by
    funext x
    by_cases hx : x = ul
    · subst hx
      rw [Function.update_self]
      simpa [Term.eval] using hassign.1
    · rw [Function.update_of_ne hx]
      exact hassign.2 x hx
  have hFm' : Formula.sat (F m'') σ := (sat_modeKeyed.mp hMK) m'' hm' hulm'
  have hFt : Formula.sat (F t) σ := hhand m'' hm' t ht σ hFm' henv hguard
  have hcoin : ∀ (G : Formula (Var n)), ul ∉ G.fv →
      (Formula.sat G σ₃ ↔ Formula.sat G σ) := by
    intro G hG
    rw [hσ₃]
    exact (Formula.coincidence G (fun y hy =>
      (Function.update_of_ne (fun hc => hG (by rw [← hc]; exact hy)) _ _).symm)).symm
  have hσ₃sat : Formula.sat (Formula.and (Formula.and (F t) env) Bk) σ₃ :=
    ⟨⟨(hcoin _ (hulF t)).mpr hFt, (hcoin _ hulenv).mpr henv⟩, (hcoin _ hulBk).mpr hBk⟩
  have hfa := hstepM t ht' σ₃ hσ₃sat ((hcoin _ (hulG t)).mpr hguard)
  rw [faModal_sat] at hfa
  obtain ⟨μ, hRμ, ⟨hFtμ, henvμ⟩, hBkμ⟩ := hfa ν hwin
  refine ⟨μ, hRμ, ?_⟩
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

end RelCertifier
