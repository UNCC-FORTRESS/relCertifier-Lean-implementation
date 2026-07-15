/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The Faithful-soundness bridge, part 1: `QF` denotation

`Faithful.lean` computes with raw `ℤ × ℤ` fractions (`QF`) so its verdicts kernel-reduce.
This file gives those computations meaning: `QF.val` denotes a fraction in ℝ, every
operation is sound for positive-denominator inputs, and positivity is closed under the
operations `exprPoly` uses. Downstream (parts 2+), `shapeFaithful`'s Boolean coefficient
laws become the real-valued pushforward identities that `GuardSettlingB_rescale` consumes.
-/
import RelCertifier.Faithful
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace RelCertifier

/-! ## Denotation and the positive-denominator invariant -/

/-- The real value of a raw fraction. -/
noncomputable def QF.val (a : QF) : ℝ := (a.n : ℝ) / (a.d : ℝ)

/-- The invariant every `Faithful`-built fraction satisfies. -/
def QF.pos (a : QF) : Prop := 0 < a.d

theorem QF.pos.dR_pos {a : QF} (h : a.pos) : (0 : ℝ) < (a.d : ℝ) := by
  exact_mod_cast h

theorem QF.pos.dR_ne {a : QF} (h : a.pos) : ((a.d : ℝ)) ≠ 0 := ne_of_gt h.dR_pos

/-! ## Value soundness of the operations -/

@[simp] theorem qOfInt_val (z : ℤ) : (qOfInt z).val = (z : ℝ) := by
  simp [qOfInt, QF.val]

theorem qOfInt_pos (z : ℤ) : (qOfInt z).pos := by simp [qOfInt, QF.pos]

theorem qMk_val (nn dd : ℤ) : (qMk nn dd).val = (nn : ℝ) / (dd : ℝ) := by
  unfold qMk
  split
  · simp only [QF.val, Int.cast_neg]
    rw [neg_div_neg_eq]
  · rfl

theorem qMk_pos {dd : ℤ} (h : dd ≠ 0) (nn : ℤ) : (qMk nn dd).pos := by
  unfold qMk QF.pos
  split <;> dsimp only <;> omega

theorem qAdd_val {a b : QF} (ha : a.pos) (hb : b.pos) :
    (qAdd a b).val = a.val + b.val := by
  have hane := ha.dR_ne
  have hbne := hb.dR_ne
  unfold qAdd QF.val
  push_cast
  field_simp

theorem qAdd_pos {a b : QF} (ha : a.pos) (hb : b.pos) : (qAdd a b).pos :=
  mul_pos ha hb

@[simp] theorem qNeg_val (a : QF) : (qNeg a).val = -a.val := by
  unfold qNeg QF.val
  push_cast
  ring

theorem qNeg_pos {a : QF} (ha : a.pos) : (qNeg a).pos := ha

theorem qSub_val {a b : QF} (ha : a.pos) (hb : b.pos) :
    (qSub a b).val = a.val - b.val := by
  unfold qSub
  rw [qAdd_val ha (qNeg_pos hb), qNeg_val]
  ring

theorem qSub_pos {a b : QF} (ha : a.pos) (hb : b.pos) : (qSub a b).pos :=
  qAdd_pos ha (qNeg_pos hb)

theorem qMul_val (a b : QF) : (qMul a b).val = a.val * b.val := by
  unfold qMul QF.val
  push_cast
  rw [div_mul_div_comm]

theorem qMul_pos {a b : QF} (ha : a.pos) (hb : b.pos) : (qMul a b).pos :=
  mul_pos ha hb

/-- Division is sound for positive denominators — including `b.n = 0`, where both sides
are `0` by ℝ's division convention. -/
theorem qDiv_val {a b : QF} (ha : a.pos) (hb : b.pos) :
    (qDiv a b).val = a.val / b.val := by
  unfold qDiv
  rw [qMk_val]
  unfold QF.val
  rcases eq_or_ne b.n 0 with hn | hn
  · simp [hn]
  · have hbn : ((b.n : ℝ)) ≠ 0 := by exact_mod_cast hn
    have hane := ha.dR_ne
    have hbne := hb.dR_ne
    push_cast
    field_simp

theorem qDiv_pos {a b : QF} (ha : a.pos) (hn : b.n ≠ 0) : (qDiv a b).pos :=
  qMk_pos (mul_ne_zero (ne_of_gt ha) hn) _

/-! ## Comparison soundness -/

theorem qEq_val {a b : QF} (ha : a.pos) (hb : b.pos) (h : qEq a b = true) :
    a.val = b.val := by
  unfold qEq at h
  have hz : a.n * b.d = b.n * a.d := by exact_mod_cast beq_iff_eq.mp h
  unfold QF.val
  rw [div_eq_div_iff ha.dR_ne hb.dR_ne]
  exact_mod_cast hz

theorem qLt_val {a b : QF} (ha : a.pos) (hb : b.pos) (h : qLt a b = true) :
    a.val < b.val := by
  unfold qLt at h
  have hz : a.n * b.d < b.n * a.d := by exact_mod_cast decide_eq_true_eq.mp h
  unfold QF.val
  rw [div_lt_div_iff₀ ha.dR_pos hb.dR_pos]
  exact_mod_cast hz

theorem qIsZero_val {a : QF} (ha : a.pos) (h : qIsZero a = true) : a.val = 0 := by
  unfold qIsZero at h
  have : a.n = 0 := beq_iff_eq.mp h
  simp [QF.val, this]

theorem qIsZero_false_val {a : QF} (ha : a.pos) (h : qIsZero a = false) : a.val ≠ 0 := by
  unfold qIsZero at h
  have hn : a.n ≠ 0 := by simpa using h
  unfold QF.val
  exact div_ne_zero (by exact_mod_cast hn) ha.dR_ne

theorem qPow10_pos (k : Nat) : (qPow10 k).pos := by
  unfold qPow10 QF.pos
  positivity

/-! ## Part 2: monomial semantics

A `Mono` denotes the product of its variable powers. `monoEq` (multiset equality) is
sound for the denotation because products are order-insensitive; we interpret through
`Multiset` so that symmetry/transitivity of `monoEq` (needed to walk association lists)
come from multiset equality. The backward direction (multiset equality ⟹ `monoEq`)
holds for monomials whose variable names are distinct — every monomial `exprPoly`
builds is of this form. -/

/-- The real value of a monomial in an environment. -/
noncomputable def Mono.evalR (ρ : String → ℝ) (m : Mono) : ℝ :=
  (m.map (fun p => ρ p.1 ^ p.2)).prod

@[simp] theorem Mono.evalR_nil (ρ : String → ℝ) : Mono.evalR ρ [] = 1 := rfl

@[simp] theorem Mono.evalR_cons (ρ : String → ℝ) (v : String) (k : Nat) (m : Mono) :
    Mono.evalR ρ ((v, k) :: m) = ρ v ^ k * Mono.evalR ρ m := by
  simp [Mono.evalR]

/-- Multiset value (well-defined: the product commutes). -/
noncomputable def Mono.evalM (ρ : String → ℝ) (s : Multiset (String × Nat)) : ℝ :=
  (s.map (fun p => ρ p.1 ^ p.2)).prod

theorem Mono.evalR_eq_evalM (ρ : String → ℝ) (m : Mono) :
    Mono.evalR ρ m = Mono.evalM ρ (m : Multiset (String × Nat)) := rfl

/-- `monoExtract` decomposes the multiset. -/
theorem monoExtract_multiset {v : String} : ∀ {m : Mono} {k : Nat} {m' : Mono},
    monoExtract v m = some (k, m') →
    (m : Multiset (String × Nat)) = (v, k) ::ₘ (m' : Multiset (String × Nat)) := by
  intro m
  induction m with
  | nil => intro k m' h; exact absurd h (by simp [monoExtract])
  | cons p rest ih =>
      obtain ⟨w, l⟩ := p
      intro k m' h
      unfold monoExtract at h
      split at h
      · rename_i heq
        injection h with h'
        injection h' with h1 h2
        subst h1
        subst h2
        have hvw : v = w := beq_iff_eq.mp heq
        subst hvw
        rfl
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨k2, m2⟩, hr, hh⟩ := h
        injection hh with h1 h2
        subst h1
        subst h2
        have hrest := ih hr
        show ((w, l) ::ₘ (rest : Multiset (String × Nat)))
          = (v, k2) ::ₘ ((w, l) ::ₘ (m2 : Multiset (String × Nat)))
        rw [hrest, Multiset.cons_swap]

/-- Soundness: `monoEq` implies multiset equality. -/
theorem monoEq_multiset : ∀ {a b : Mono}, monoEq a b = true →
    (a : Multiset (String × Nat)) = (b : Multiset (String × Nat)) := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons p r => exact absurd h (by simp [monoEq])
  | cons p rest ih =>
      obtain ⟨v, k⟩ := p
      intro b h
      unfold monoEq at h
      split at h
      · rename_i l b' hex
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hkl, hres⟩ := h
        subst hkl
        have hb := monoExtract_multiset hex
        rw [hb, ← ih hres]
        rfl
      · exact absurd h (by simp)

/-- The denotation respects `monoEq`. -/
theorem monoEq_evalR {a b : Mono} (h : monoEq a b = true) (ρ : String → ℝ) :
    Mono.evalR ρ a = Mono.evalR ρ b := by
  rw [Mono.evalR_eq_evalM, Mono.evalR_eq_evalM, monoEq_multiset h]

/-! ### The backward direction, for distinct-variable monomials -/

/-- Variable names occur at most once (true of every `exprPoly` monomial). -/
def Mono.varsNodup (m : Mono) : Prop := (m.map Prod.fst).Nodup

theorem Mono.varsNodup_nil : Mono.varsNodup [] := List.nodup_nil

/-- On a distinct-variable monomial, membership pins down `monoExtract`'s exponent. -/
theorem monoExtract_of_mem {v : String} {k : Nat} : ∀ {b : Mono},
    Mono.varsNodup b → (v, k) ∈ b →
    ∃ b', monoExtract v b = some (k, b') ∧
      (b : Multiset (String × Nat)) = (v, k) ::ₘ (b' : Multiset (String × Nat)) := by
  intro b
  induction b with
  | nil => intro _ hm; exact absurd hm (by simp)
  | cons p rest ih =>
      obtain ⟨w, l⟩ := p
      intro hnd hm
      by_cases hvw : v = w
      · subst hvw
        have hk : k = l := by
          rcases List.mem_cons.mp hm with hh | ht
          · cases hh
            rfl
          · exact absurd (List.mem_map.mpr ⟨(v, k), ht, rfl⟩)
              ((List.nodup_cons.mp hnd).1)
        subst hk
        exact ⟨rest, by simp [monoExtract], rfl⟩
      · have ht : (v, k) ∈ rest := by
          rcases List.mem_cons.mp hm with hh | ht
          · injection hh with h1 _; exact absurd h1 hvw
          · exact ht
        obtain ⟨b', hex, hms⟩ := ih (List.nodup_cons.mp hnd).2 ht
        refine ⟨(w, l) :: b', ?_, ?_⟩
        · simp only [monoExtract, hex]
          rw [if_neg (by simpa using hvw)]
          rfl
        · show ((w, l) ::ₘ (rest : Multiset (String × Nat)))
            = (v, k) ::ₘ ((w, l) ::ₘ (b' : Multiset (String × Nat)))
          rw [hms, Multiset.cons_swap]

/-- Completeness on distinct-variable monomials: multiset equality implies `monoEq`. -/
theorem monoEq_of_multiset : ∀ {a b : Mono}, Mono.varsNodup b →
    (a : Multiset (String × Nat)) = (b : Multiset (String × Nat)) →
    monoEq a b = true := by
  intro a
  induction a with
  | nil =>
      intro b _ h
      have : b = [] := List.Perm.eq_nil (Multiset.coe_eq_coe.mp h.symm)
      subst this
      rfl
  | cons p rest ih =>
      obtain ⟨v, k⟩ := p
      intro b hnd h
      have hmem : (v, k) ∈ b := by
        have : (v, k) ∈ (b : Multiset (String × Nat)) := by
          rw [← h]
          simp
        simpa using this
      obtain ⟨b', hex, hms⟩ := monoExtract_of_mem hnd hmem
      unfold monoEq
      rw [hex]
      simp only [Bool.and_eq_true, beq_self_eq_true, true_and]
      refine ih ?_ ?_
      · -- b' inherits distinct variables
        have : Mono.varsNodup b := hnd
        unfold Mono.varsNodup at this ⊢
        have hperm : (b : Multiset (String × Nat)).map Prod.fst
            = (v, k).1 ::ₘ (b' : Multiset (String × Nat)).map Prod.fst := by
          rw [hms, Multiset.map_cons]
        have hnodM : ((b : Multiset (String × Nat)).map Prod.fst).Nodup := by
          simpa using this
        rw [hperm] at hnodM
        have := (Multiset.nodup_cons.mp hnodM).2
        simpa using this
      · -- the tails' multisets agree
        have := h
        rw [hms] at this
        have hc : ((v, k) ::ₘ (rest : Multiset (String × Nat)))
            = (v, k) ::ₘ (b' : Multiset (String × Nat)) := this
        exact (Multiset.cons_inj_right _).mp hc

theorem monoEq_refl {a : Mono} (h : Mono.varsNodup a) : monoEq a a = true :=
  monoEq_of_multiset h rfl

theorem monoEq_symm {a b : Mono} (hb : Mono.varsNodup a) (h : monoEq a b = true) :
    monoEq b a = true :=
  monoEq_of_multiset hb (monoEq_multiset h).symm

theorem monoEq_trans {a b c : Mono} (hc : Mono.varsNodup c)
    (hab : monoEq a b = true) (hbc : monoEq b c = true) : monoEq a c = true :=
  monoEq_of_multiset hc ((monoEq_multiset hab).trans (monoEq_multiset hbc))

/-! ### `monoInsert` / `monoMul` semantics -/

theorem monoInsert_evalR (ρ : String → ℝ) (v : String) (k : Nat) : ∀ (m : Mono),
    Mono.evalR ρ (monoInsert v k m) = ρ v ^ k * Mono.evalR ρ m := by
  intro m
  induction m with
  | nil => simp [monoInsert]
  | cons p rest ih =>
      obtain ⟨w, l⟩ := p
      unfold monoInsert
      by_cases hvw : v = w
      · subst hvw
        rw [if_pos (by simp)]
        simp only [Mono.evalR_cons]
        rw [pow_add]
        ring
      · rw [if_neg (by simpa using hvw)]
        simp only [Mono.evalR_cons, ih]
        ring

theorem monoMul_evalR (ρ : String → ℝ) : ∀ (a b : Mono),
    Mono.evalR ρ (monoMul a b) = Mono.evalR ρ a * Mono.evalR ρ b := by
  intro a
  induction a with
  | nil => intro b; simp [monoMul]
  | cons p rest ih =>
      obtain ⟨v, k⟩ := p
      intro b
      unfold monoMul
      rw [ih, monoInsert_evalR]
      simp only [Mono.evalR_cons]
      ring

theorem monoInsert_varsNodup {v : String} {k : Nat} : ∀ {m : Mono},
    Mono.varsNodup m → Mono.varsNodup (monoInsert v k m) := by
  intro m
  induction m with
  | nil => intro _; simp [monoInsert, Mono.varsNodup]
  | cons p rest ih =>
      obtain ⟨w, l⟩ := p
      intro hnd
      unfold monoInsert
      by_cases hvw : v = w
      · subst hvw
        rw [if_pos (by simp)]
        exact hnd
      · rw [if_neg (by simpa using hvw)]
        unfold Mono.varsNodup at hnd ⊢
        simp only [List.map_cons, List.nodup_cons] at hnd ⊢
        refine ⟨?_, ih hnd.2⟩
        intro hmem
        -- w ∈ vars (monoInsert v k rest) = {v} ∪ vars rest, and w ≠ v
        have hvars : ∀ (r : Mono) (x : String),
            x ∈ (monoInsert v k r).map Prod.fst → x = v ∨ x ∈ r.map Prod.fst := by
          intro r
          induction r with
          | nil => intro x hx; simpa [monoInsert] using hx
          | cons q rr ihq =>
              obtain ⟨y, j⟩ := q
              intro x hx
              unfold monoInsert at hx
              by_cases hvy : v = y
              · subst hvy
                rw [if_pos (by simp)] at hx
                simp only [List.map_cons, List.mem_cons] at hx
                rcases hx with hx | hx
                · exact Or.inl hx
                · exact Or.inr (by simp [hx])
              · rw [if_neg (by simpa using hvy)] at hx
                simp only [List.map_cons, List.mem_cons] at hx
                rcases hx with hx | hx
                · exact Or.inr (by simp [hx])
                · rcases ihq x hx with hx' | hx'
                  · exact Or.inl hx'
                  · exact Or.inr (by simp [hx'])
        rcases hvars rest w hmem with hw | hw
        · exact hvw hw.symm
        · exact hnd.1 hw

theorem monoMul_varsNodup : ∀ {a b : Mono},
    Mono.varsNodup b → Mono.varsNodup (monoMul a b) := by
  intro a
  induction a with
  | nil => intro b hb; exact hb
  | cons p rest ih =>
      obtain ⟨v, k⟩ := p
      intro b hb
      unfold monoMul
      exact ih (monoInsert_varsNodup hb)


end RelCertifier
