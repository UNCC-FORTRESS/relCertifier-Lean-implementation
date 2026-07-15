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
import RelCertifier.Checker.Faithful
import RelCertifier.Proofs.Transfer.Rescale
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Nodup

namespace RelCertifier

/-! ## Denotation and the positive-denominator invariant -/

/-- The real value of a raw fraction. -/
noncomputable def QF.val (a : QF) : ℝ := (a.n : ℝ) / (a.d : ℝ)

/-- The invariant every `Faithful`-built fraction satisfies. -/
def QF.pos (a : QF) : Prop := 0 < a.d

instance (a : QF) : Decidable a.pos := inferInstanceAs (Decidable (0 < a.d))

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


/-! ## Part 3: polynomial semantics — invariants, `coeffOf`, and the support sum

`shapeFaithful` reads a polynomial only through `coeffOf` and `supportIn`. The crux
lemma (`evalR_support`) turns those Boolean reads into the polynomial's real value:
if the support lies in a duplicate-free monomial list `ms`, the value is the sum over
`ms` of coefficient × monomial. All that is needed of the polynomial itself is the
invariant `exprPoly` maintains: positive coefficient denominators, distinct-variable
keys, pairwise `monoEq`-distinct keys. -/

/-- The real value of a polynomial in an environment. -/
noncomputable def QPoly.evalR (ρ : String → ℝ) (p : QPoly) : ℝ :=
  (p.map (fun e => e.2.val * Mono.evalR ρ e.1)).sum

@[simp] theorem QPoly.evalR_nil (ρ : String → ℝ) : QPoly.evalR ρ [] = 0 := rfl

@[simp] theorem QPoly.evalR_cons (ρ : String → ℝ) (e : Mono × QF) (p : QPoly) :
    QPoly.evalR ρ (e :: p) = e.2.val * Mono.evalR ρ e.1 + QPoly.evalR ρ p := by
  simp [QPoly.evalR]

/-- The invariant `exprPoly` maintains. -/
structure PolyInv (p : QPoly) : Prop where
  pos : ∀ e ∈ p, e.2.pos
  keysNodup : ∀ e ∈ p, Mono.varsNodup e.1
  keysDistinct : p.Pairwise (fun e f => monoEq e.1 f.1 = false)

theorem PolyInv.nil : PolyInv [] := ⟨by simp, by simp, List.Pairwise.nil⟩

theorem PolyInv.of_cons {a : Mono × QF} {p : QPoly} (h : PolyInv (a :: p)) : PolyInv p :=
  ⟨fun e he => h.pos e (List.mem_cons_of_mem a he),
   fun e he => h.keysNodup e (List.mem_cons_of_mem a he),
   (List.pairwise_cons.mp h.keysDistinct).2⟩

/-! ### `coeffOf` structure -/

theorem coeffOf_nil (m : Mono) : coeffOf [] m = qOfInt 0 := rfl

theorem coeffOf_cons_hit {a : Mono × QF} {m : Mono} (h : monoEq a.1 m = true)
    (p : QPoly) : coeffOf (a :: p) m = a.2 := by
  simp [coeffOf, List.find?, h]

theorem coeffOf_cons_miss {a : Mono × QF} {m : Mono} (h : monoEq a.1 m = false)
    (p : QPoly) : coeffOf (a :: p) m = coeffOf p m := by
  simp [coeffOf, List.find?, h]

theorem coeffOf_notin {m : Mono} : ∀ {p : QPoly},
    (∀ e ∈ p, monoEq e.1 m = false) → coeffOf p m = qOfInt 0 := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons a q ih =>
      intro h
      rw [coeffOf_cons_miss (h a (List.mem_cons_self ..))]
      exact ih (fun e he => h e (List.mem_cons_of_mem a he))

theorem coeffOf_pos {p : QPoly} (hp : ∀ e ∈ p, e.2.pos) (m : Mono) :
    (coeffOf p m).pos := by
  unfold coeffOf
  rcases hf : p.find? (fun e => monoEq e.1 m) with _ | e <;> rw [hf]
  · exact qOfInt_pos 0
  · simpa using hp e (List.mem_of_find?_eq_some hf)

/-- Two keys `monoEq` to the same distinct-variable monomial are `monoEq` to each other. -/
theorem monoEq_common {a b m : Mono} (hb : Mono.varsNodup b)
    (ha : monoEq a m = true) (hbm : monoEq b m = true) : monoEq a b = true :=
  monoEq_of_multiset hb ((monoEq_multiset ha).trans (monoEq_multiset hbm).symm)

/-! ### The support-sum crux -/

/-- Pulling the head entry out of the coefficient sum over a duplicate-free support. -/
theorem coeffSum_cons (ρ : String → ℝ) (a : Mono × QF) (p : QPoly)
    (hnda : Mono.varsNodup a.1)
    (hkeys : ∀ e ∈ p, Mono.varsNodup e.1)
    (hsep : ∀ e ∈ p, monoEq a.1 e.1 = false) :
    ∀ (ms : List Mono), (∀ m ∈ ms, Mono.varsNodup m) →
    ms.Pairwise (fun m m' => monoEq m m' = false) →
    (∃ m ∈ ms, monoEq a.1 m = true) →
    (ms.map (fun m => (coeffOf (a :: p) m).val * Mono.evalR ρ m)).sum
      = a.2.val * Mono.evalR ρ a.1
        + (ms.map (fun m => (coeffOf p m).val * Mono.evalR ρ m)).sum := by
  intro ms
  induction ms with
  | nil => intro _ _ hex; exact absurd hex (by simp)
  | cons m ms' ih =>
      intro hnd hpw hex
      have hndm := hnd m (List.mem_cons_self ..)
      have hnd' := fun x hx => hnd x (List.mem_cons_of_mem m hx)
      obtain ⟨hpwm, hpw'⟩ := List.pairwise_cons.mp hpw
      rcases hhit : monoEq a.1 m with _ | _
      · -- head of ms not hit: the witness is in the tail
        have hex' : ∃ m' ∈ ms', monoEq a.1 m' = true := by
          rcases hex with ⟨m0, hm0, h0⟩
          rcases List.mem_cons.mp hm0 with rfl | hm0'
          · rw [h0] at hhit; exact absurd hhit (by simp)
          · exact ⟨m0, hm0', h0⟩
        simp only [List.map_cons, List.sum_cons]
        rw [coeffOf_cons_miss hhit, ih hnd' hpw' hex']
        ring
      · -- head of ms hit
        simp only [List.map_cons, List.sum_cons]
        rw [coeffOf_cons_hit hhit]
        -- the tail of ms misses a.1
        have hmiss : ∀ m' ∈ ms', monoEq a.1 m' = false := by
          intro m' hm'
          rcases hq : monoEq a.1 m' with _ | _
          · rfl
          · -- then m ~ a.1 ~ m', contradicting ms-pairwise
            have hmm' : monoEq m m' = true :=
              monoEq_of_multiset (hnd' m' hm')
                ((monoEq_multiset hhit).symm.trans (monoEq_multiset hq))
            rw [hpwm m' hm'] at hmm'
            exact absurd hmm' (by simp)
        -- coeffOf (a::p) on the tail = coeffOf p on the tail
        have htail : (ms'.map (fun m' => (coeffOf (a :: p) m').val * Mono.evalR ρ m')).sum
            = (ms'.map (fun m' => (coeffOf p m').val * Mono.evalR ρ m')).sum := by
          congr 1
          refine List.map_congr_left ?_
          intro m' hm'
          rw [coeffOf_cons_miss (hmiss m' hm')]
        -- p misses m (an entry hitting m would collide with a's key)
        have hpm : coeffOf p m = qOfInt 0 := by
          refine coeffOf_notin ?_
          intro e he
          rcases hq : monoEq e.1 m with _ | _
          · rfl
          · have : monoEq a.1 e.1 = true := monoEq_common (hkeys e he) hhit hq
            rw [hsep e he] at this
            exact absurd this (by simp)
        rw [htail, hpm]
        have heval : Mono.evalR ρ m = Mono.evalR ρ a.1 := (monoEq_evalR hhit ρ).symm
        rw [heval]
        simp

/-- **The support-sum crux**: a polynomial supported inside a duplicate-free monomial
list is the sum, over that list, of coefficient × monomial value. -/
theorem evalR_support (ρ : String → ℝ) : ∀ (p : QPoly),
    PolyInv p →
    ∀ (ms : List Mono), (∀ m ∈ ms, Mono.varsNodup m) →
    ms.Pairwise (fun m m' => monoEq m m' = false) →
    supportIn p ms = true →
    QPoly.evalR ρ p = (ms.map (fun m => (coeffOf p m).val * Mono.evalR ρ m)).sum := by
  intro p
  induction p with
  | nil =>
      intro _ ms _ _ _
      rw [QPoly.evalR_nil]
      have hz : ∀ ms' : List Mono,
          (0 : ℝ) = (ms'.map (fun m => (coeffOf [] m).val * Mono.evalR ρ m)).sum := by
        intro ms'
        induction ms' with
        | nil => rfl
        | cons m ms'' ihm =>
            simp only [List.map_cons, List.sum_cons, coeffOf_nil, qOfInt_val,
              Int.cast_zero, zero_mul, zero_add]
            simpa using ihm
      exact hz ms
  | cons a p ih =>
      intro hinv ms hnd hpw hsup
      have hex : ∃ m ∈ ms, monoEq a.1 m = true := by
        have := hsup
        unfold supportIn at this
        simp only [List.all_cons, Bool.and_eq_true, List.any_eq_true] at this
        exact this.1
      have hsup' : supportIn p ms = true := by
        unfold supportIn at hsup ⊢
        simp only [List.all_cons, Bool.and_eq_true] at hsup
        exact hsup.2
      have hsep : ∀ e ∈ p, monoEq a.1 e.1 = false :=
        List.pairwise_cons.mp hinv.keysDistinct |>.1
      rw [QPoly.evalR_cons,
        coeffSum_cons ρ a p (hinv.keysNodup a (List.mem_cons_self ..))
          (fun e he => hinv.keysNodup e (List.mem_cons_of_mem a he)) hsep
          ms hnd hpw hex,
        ih hinv.of_cons ms hnd hpw hsup']

/-! ## Part 3b: `exprPoly` maintains the invariant -/

theorem polyInsert_key_sub {m : Mono} {c : QF} : ∀ {p : QPoly} {e : Mono × QF},
    e ∈ polyInsert m c p → e.1 = m ∨ ∃ f ∈ p, e.1 = f.1 := by
  intro p
  induction p with
  | nil =>
      intro e he
      unfold polyInsert at he
      split at he
      · exact absurd he (by simp)
      · rcases List.mem_singleton.mp he with rfl
        exact Or.inl rfl
  | cons a q ih =>
      obtain ⟨nn, dd⟩ := a
      intro e he
      unfold polyInsert at he
      split at he
      · have he' : e ∈ (if qIsZero (qAdd c dd) = true then q
            else (nn, qAdd c dd) :: q) := he
        split at he'
        · exact Or.inr ⟨e, List.mem_cons_of_mem _ he', rfl⟩
        · rcases List.mem_cons.mp he' with rfl | he''
          · exact Or.inr ⟨(nn, dd), List.mem_cons_self .., rfl⟩
          · exact Or.inr ⟨e, List.mem_cons_of_mem _ he'', rfl⟩
      · rcases List.mem_cons.mp he with rfl | he'
        · exact Or.inr ⟨(nn, dd), List.mem_cons_self .., rfl⟩
        · rcases ih he' with hm | ⟨f, hf, hef⟩
          · exact Or.inl hm
          · exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, hef⟩

theorem polyInsert_pos {m : Mono} {c : QF} (hc : c.pos) : ∀ {p : QPoly},
    (∀ e ∈ p, e.2.pos) → ∀ e ∈ polyInsert m c p, e.2.pos := by
  intro p
  induction p with
  | nil =>
      intro _ e he
      unfold polyInsert at he
      split at he
      · exact absurd he (by simp)
      · rcases List.mem_singleton.mp he with rfl
        exact hc
  | cons a q ih =>
      obtain ⟨nn, dd⟩ := a
      intro hp e he
      have hdd : dd.pos := hp (nn, dd) (List.mem_cons_self ..)
      have hq : ∀ e ∈ q, e.2.pos := fun e he => hp e (List.mem_cons_of_mem _ he)
      unfold polyInsert at he
      split at he
      · have he' : e ∈ (if qIsZero (qAdd c dd) = true then q
            else (nn, qAdd c dd) :: q) := he
        split at he'
        · exact hq e he'
        · rcases List.mem_cons.mp he' with rfl | he''
          · exact qAdd_pos hc hdd
          · exact hq e he''
      · rcases List.mem_cons.mp he with rfl | he'
        · exact hdd
        · exact ih hq e he'

theorem polyInsert_inv {m : Mono} {c : QF} (hm : Mono.varsNodup m) (hc : c.pos) :
    ∀ {p : QPoly}, PolyInv p → PolyInv (polyInsert m c p) := by
  intro p
  induction p with
  | nil =>
      intro _
      unfold polyInsert
      split
      · exact PolyInv.nil
      · exact ⟨by simpa using hc, by simpa using hm, by simp⟩
  | cons a q ih =>
      obtain ⟨nn, dd⟩ := a
      intro hp
      have hqinv := hp.of_cons
      have hnn : Mono.varsNodup nn := hp.keysNodup (nn, dd) (List.mem_cons_self ..)
      have hsep : ∀ f ∈ q, monoEq nn f.1 = false :=
        (List.pairwise_cons.mp hp.keysDistinct).1
      unfold polyInsert
      split
      · rename_i hguard
        show PolyInv (if qIsZero (qAdd c dd) = true then q else (nn, qAdd c dd) :: q)
        split
        · exact hqinv
        · exact ⟨
            (fun e he => by
              rcases List.mem_cons.mp he with rfl | he'
              · exact qAdd_pos hc (hp.pos (nn, dd) (List.mem_cons_self ..))
              · exact hqinv.pos e he'),
            (fun e he => by
              rcases List.mem_cons.mp he with rfl | he'
              · exact hnn
              · exact hqinv.keysNodup e he'),
            (List.pairwise_cons.mpr ⟨hsep, hqinv.keysDistinct⟩)⟩
      · rename_i hguard
        have hmn : monoEq m nn = false := by
          rcases hx : monoEq m nn with _ | _
          · rfl
          · exact absurd hx hguard
        have hins := ih hqinv
        refine ⟨
          (fun e he => by
            rcases List.mem_cons.mp he with rfl | he'
            · exact hp.pos (nn, dd) (List.mem_cons_self ..)
            · exact hins.pos e he'),
          (fun e he => by
            rcases List.mem_cons.mp he with rfl | he'
            · exact hnn
            · exact hins.keysNodup e he'),
          List.pairwise_cons.mpr ⟨?_, hins.keysDistinct⟩⟩
        intro f hf
        rcases polyInsert_key_sub hf with hfm | ⟨g, hg, hfg⟩
        · -- f's key is m; nn ≁ m since m ≁ nn
          rw [hfm]
          rcases hx : monoEq nn m with _ | _
          · rfl
          · have := monoEq_symm hnn hx
            rw [hmn] at this
            exact absurd this (by simp)
        · rw [hfg]
          exact hsep g hg

theorem polyAdd_inv : ∀ {b : QPoly} {a : QPoly}, PolyInv a →
    (∀ e ∈ b, Mono.varsNodup e.1) → (∀ e ∈ b, e.2.pos) → PolyInv (polyAdd a b) := by
  intro b
  induction b with
  | nil => intro a ha _ _; exact ha
  | cons e b ih =>
      intro a ha hk hp
      show PolyInv (polyAdd (polyInsert e.1 e.2 a) b)
      exact ih (polyInsert_inv (hk e (List.mem_cons_self ..))
          (hp e (List.mem_cons_self ..)) ha)
        (fun f hf => hk f (List.mem_cons_of_mem _ hf))
        (fun f hf => hp f (List.mem_cons_of_mem _ hf))

theorem polyNeg_inv {a : QPoly} (ha : PolyInv a) : PolyInv (polyNeg a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [polyNeg, List.mem_map] at he
    obtain ⟨f, hf, rfl⟩ := he
    exact qNeg_pos (ha.pos f hf)
  · intro e he
    simp only [polyNeg, List.mem_map] at he
    obtain ⟨f, hf, rfl⟩ := he
    exact ha.keysNodup f hf
  · unfold polyNeg
    refine List.Pairwise.map _ ?_ ha.keysDistinct
    intro e f h
    exact h

theorem polyScale_inv {q : QF} {a : QPoly} (hq : q.pos) (ha : PolyInv a) :
    PolyInv (polyScale q a) := by
  unfold polyScale
  split
  · exact PolyInv.nil
  · refine ⟨?_, ?_, ?_⟩
    · intro e he
      simp only [List.mem_map] at he
      obtain ⟨f, hf, rfl⟩ := he
      exact qMul_pos hq (ha.pos f hf)
    · intro e he
      simp only [List.mem_map] at he
      obtain ⟨f, hf, rfl⟩ := he
      exact ha.keysNodup f hf
    · refine List.Pairwise.map _ ?_ ha.keysDistinct
      intro e f h
      exact h

theorem polyMul_inv {a b : QPoly} (ha : PolyInv a) (hb : PolyInv b) :
    PolyInv (polyMul a b) := by
  unfold polyMul
  suffices hgen : ∀ (l : QPoly), (∀ e ∈ l, Mono.varsNodup e.1) → (∀ e ∈ l, e.2.pos) →
      ∀ (acc : QPoly), PolyInv acc →
      PolyInv (l.foldl (fun acc mc =>
        polyAdd acc (b.map (fun nd => (monoMul mc.1 nd.1, qMul mc.2 nd.2)))) acc) by
    exact hgen a ha.keysNodup ha.pos [] PolyInv.nil
  intro l
  induction l with
  | nil => intro _ _ acc hacc; exact hacc
  | cons mc l ih =>
      intro hk hp acc hacc
      refine ih (fun e he => hk e (List.mem_cons_of_mem _ he))
        (fun e he => hp e (List.mem_cons_of_mem _ he)) _ ?_
      refine polyAdd_inv hacc ?_ ?_
      · intro e he
        simp only [List.mem_map] at he
        obtain ⟨nd, hnd, rfl⟩ := he
        exact monoMul_varsNodup (hb.keysNodup nd hnd)
      · intro e he
        simp only [List.mem_map] at he
        obtain ⟨nd, hnd, rfl⟩ := he
        exact qMul_pos (hp mc (List.mem_cons_self ..)) (hb.pos nd hnd)

theorem polyConstOf_inv {q : QF} (hq : q.pos) : PolyInv (polyConstOf q) := by
  unfold polyConstOf
  split
  · exact PolyInv.nil
  · exact ⟨by simpa using hq, by simp [Mono.varsNodup_nil], by simp⟩

theorem polyVarOf_inv (v : String) : PolyInv (polyVarOf v) := by
  refine ⟨by simp [polyVarOf, qOfInt_pos], ?_, by simp [polyVarOf]⟩
  intro e he
  simp only [polyVarOf, List.mem_singleton] at he
  subst he
  simp [Mono.varsNodup]

/-! ### `parseQ` outputs are positive-denominator -/

theorem parseQPos_pos {cs : List Char} {q : QF}
    (h : parseQChars.parseQPos cs = some q) : q.pos := by
  unfold parseQChars.parseQPos at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨nn, -, rfl⟩ := h
    exact qOfInt_pos _
  · rcases hw : digitsToNat _ with _ | nn <;> rw [hw] at h
    · exact absurd h (by simp)
    rcases hf : digitsToNat _ with _ | mm <;> rw [hf] at h
    · exact absurd h (by simp)
    injection h with h'
    subst h'
    exact qAdd_pos (qOfInt_pos _) (qMul_pos (qOfInt_pos _) (qPow10_pos _))

theorem parseQChars_pos {cs : List Char} {q : QF} (h : parseQChars cs = some q) :
    q.pos := by
  unfold parseQChars at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact qNeg_pos (parseQPos_pos hr)
  · exact parseQPos_pos h

theorem parseQ_pos {s : String} {q : QF} (h : parseQ s = some q) : q.pos :=
  parseQChars_pos h

/-! ### `exprPoly` invariant -/

theorem exprPoly_inv : ∀ {e : Parse.PExpr} {p : QPoly}, exprPoly e = some p → PolyInv p := by
  intro e
  induction e with
  | var v =>
      intro p h
      injection h with h'
      subst h'
      exact polyVarOf_inv v
  | num c =>
      intro p h
      simp only [exprPoly, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      exact polyConstOf_inv (parseQ_pos hq)
  | neg a ih =>
      intro p h
      simp only [exprPoly, Option.map_eq_some_iff] at h
      obtain ⟨pa, hpa, rfl⟩ := h
      exact polyNeg_inv (ih hpa)
  | bin op a b iha ihb =>
      intro p h
      simp only [exprPoly] at h
      rcases hpa : exprPoly a with _ | pa <;> rw [hpa] at h
      · simp at h
      rcases hpb : exprPoly b with _ | pb <;> rw [hpb] at h
      · simp at h
      have hia := iha hpa
      have hib := ihb hpb
      simp only [Option.bind_eq_bind, Option.bind] at h
      split at h
      · injection h with h'
        subst h'
        exact polyAdd_inv hia hib.keysNodup hib.pos
      · injection h with h'
        subst h'
        exact polyAdd_inv hia (polyNeg_inv hib).keysNodup (polyNeg_inv hib).pos
      · injection h with h'
        subst h'
        exact polyMul_inv hia hib
      · -- division by a nonzero constant
        split at h
        · rename_i dd
          split at h
          · exact absurd h (by simp)
          · rename_i hz
            injection h with h'
            subst h'
            have hdn : dd.n ≠ 0 := by
              unfold qIsZero at hz
              simpa using hz
            exact polyScale_inv (qDiv_pos (qOfInt_pos 1) hdn) hia
        · exact absurd h (by simp)
      · exact absurd h (by simp)

/-! ## Part 4: the real-side model — polynomials as host terms

The bridge's real-side field for a coordinate is its parsed ode as a host `Term`,
built directly from the `exprPoly` output. `rhoOf` reads a joint state through the
benchmark's variable list (right-side coordinates), and evaluation of the built term
is exactly `QPoly.evalR` in that environment. -/

open DL

variable {n : ℕ}

/-- The environment a joint state induces on benchmark variable names. -/
noncomputable def rhoOf (vs : List String) (n : ℕ) (ν : DL.State (Var n)) :
    String → ℝ :=
  fun v => match vs.idxOf? v with
    | some i => if h : i < n then ν (Rv ⟨i, h⟩) else 0
    | none => 0

/-- Variable name → host term (unresolvable names map to `0`, mirroring `rhoOf`). -/
noncomputable def varToTerm (vs : List String) (n : ℕ) (v : String) : Term (Var n) :=
  match vs.idxOf? v with
  | some i => if h : i < n then Term.var (Rv ⟨i, h⟩) else Term.const 0
  | none => Term.const 0

theorem varToTerm_eval (vs : List String) (v : String) (ν : DL.State (Var n)) :
    Term.eval (varToTerm vs n v) ν = rhoOf vs n ν v := by
  unfold varToTerm rhoOf
  rcases hix : vs.idxOf? v with _ | i <;> simp only [hix]
  · rfl
  · by_cases h : i < n
    · simp only [h, dite_true]
      rfl
    · simp only [h, dite_false]
      rfl

/-- `k`-fold product of a term. -/
noncomputable def termPow (t : Term (Var n)) : Nat → Term (Var n)
  | 0 => Term.const 1
  | k + 1 => Term.binop AOp.mul t (termPow t k)

theorem termPow_eval (t : Term (Var n)) (ν : DL.State (Var n)) :
    ∀ k, Term.eval (termPow t k) ν = (Term.eval t ν) ^ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      show Term.eval t ν * Term.eval (termPow t k) ν = _
      rw [ih, pow_succ]
      ring

/-- Monomial → host term. -/
noncomputable def monoToTerm (vs : List String) (n : ℕ) (m : Mono) : Term (Var n) :=
  m.foldr (fun p acc =>
    Term.binop AOp.mul (termPow (varToTerm vs n p.1) p.2) acc) (Term.const 1)

theorem monoToTerm_eval (vs : List String) (ν : DL.State (Var n)) : ∀ (m : Mono),
    Term.eval (monoToTerm vs n m) ν = Mono.evalR (rhoOf vs n ν) m := by
  intro m
  induction m with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨v, k⟩ := p
      show Term.eval (termPow (varToTerm vs n v) k) ν
          * Term.eval (monoToTerm vs n rest) ν = _
      rw [termPow_eval, varToTerm_eval, ih, Mono.evalR_cons]

/-- Polynomial → host term (the bridge's real-side field). -/
noncomputable def polyToTerm (vs : List String) (n : ℕ) (p : QPoly) : Term (Var n) :=
  p.foldr (fun e acc =>
    Term.binop AOp.add
      (Term.binop AOp.mul (Term.const e.2.val) (monoToTerm vs n e.1)) acc)
    (Term.const 0)

theorem polyToTerm_eval (vs : List String) (ν : DL.State (Var n)) : ∀ (p : QPoly),
    Term.eval (polyToTerm vs n p) ν = QPoly.evalR (rhoOf vs n ν) p := by
  intro p
  induction p with
  | nil => rfl
  | cons e q ih =>
      show e.2.val * Term.eval (monoToTerm vs n e.1) ν
          + Term.eval (polyToTerm vs n q) ν = _
      rw [monoToTerm_eval, ih, QPoly.evalR_cons]

/-- On a duplicate-free variable list, position lookup inverts `getD`. -/
theorem idxOf?_getD {vs : List String} (hnod : vs.Nodup) {j : Nat}
    (hj : j < vs.length) : vs.idxOf? (vs.getD j "") = some j := by
  rw [List.getD_eq_getElem _ _ hj]
  rw [List.idxOf?_eq_some_iff]
  refine ⟨hj, rfl, ?_⟩
  intro k hk h
  have := (List.Nodup.getElem_inj_iff hnod).mp h
  omega

/-- `rhoOf` at the `j`-th benchmark variable reads the `j`-th right coordinate. -/
theorem rhoOf_getD {vs : List String} (hnod : vs.Nodup) (hlen : vs.length = n)
    (ν : DL.State (Var n)) {j : Nat} (hj : j < n) :
    rhoOf vs n ν (vs.getD j "") = ν (Rv ⟨j, hj⟩) := by
  unfold rhoOf
  rw [idxOf?_getD hnod (by omega)]
  simp only [hj, dite_true]

/-! ## Part 5: the per-shape pushforward bridges

For each `CoordShape`, `shapeFaithful`'s Boolean coefficient laws upgrade to the real
pushforward identity `GuardSettlingB_rescale` consumes:

    eval (field i sh) (scaleState σ ν) = σ i · (u · eval (polyToTerm vs p) ν).
-/

/-! ### Small monomial facts -/

@[simp] theorem monoEq_nil_cons (x : String × Nat) (m : Mono) :
    monoEq [] (x :: m) = false := rfl

theorem monoEq_single_ne {v w : String} (h : v ≠ w) (k l : Nat) :
    monoEq [(v, k)] [(w, l)] = false := by
  unfold monoEq monoExtract
  rw [if_neg (by simpa using h)]
  simp [monoExtract]

theorem monoEq_single_exp_ne {v w : String} {k l : Nat} (h : k ≠ l) :
    monoEq [(v, k)] [(w, l)] = false := by
  unfold monoEq monoExtract
  by_cases hvw : v = w
  · rw [if_pos (by simpa using hvw)]
    simp [monoEq, h]
  · rw [if_neg (by simpa using hvw)]
    simp [monoExtract]

theorem varsNodup_single (v : String) (k : Nat) : Mono.varsNodup [(v, k)] := by
  simp [Mono.varsNodup]

/-- Value of a singleton-support polynomial. -/
theorem evalR_support_one {p : QPoly} (hp : PolyInv p) (m : Mono)
    (hm : Mono.varsNodup m) (hsup : supportIn p [m] = true) (ρ : String → ℝ) :
    QPoly.evalR ρ p = (coeffOf p m).val * Mono.evalR ρ m := by
  rw [evalR_support ρ p hp [m] (by simpa using hm) (by simp) hsup]
  simp

/-- Value of a two-monomial-support polynomial. -/
theorem evalR_support_two {p : QPoly} (hp : PolyInv p) (m1 m2 : Mono)
    (h1 : Mono.varsNodup m1) (h2 : Mono.varsNodup m2)
    (h12 : monoEq m1 m2 = false)
    (hsup : supportIn p [m1, m2] = true) (ρ : String → ℝ) :
    QPoly.evalR ρ p = (coeffOf p m1).val * Mono.evalR ρ m1
      + (coeffOf p m2).val * Mono.evalR ρ m2 := by
  rw [evalR_support ρ p hp [m1, m2]
    (by
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h1
      · rw [List.mem_singleton.mp hm]
        exact h2)
    (by simp [h12]) hsup]
  simp

/-! ### The bridge frame -/

/-- Value scales induced by the transcription's `QF` scales. -/
noncomputable def sigmaOf (σq : List QF) : Fin n → ℝ :=
  fun j => (σq.getD j.val (qOfInt 0)).val

theorem scaleState_rhoOf {vs : List String} (hnod : vs.Nodup) (hlen : vs.length = n)
    (σq : List QF) (ν : DL.State (Var n)) {j : Nat} (hj : j < n) :
    rhoOf vs n (scaleState (sigmaOf σq) ν) (vs.getD j "")
      = sigmaOf σq ⟨j, hj⟩ * ν (Rv ⟨j, hj⟩) := by
  rw [rhoOf_getD hnod hlen _ hj]
  rfl

/-! ### Wave 1 shape bridges -/

section ShapeBridges

variable {vs : List String} {σq : List QF} {uq : QF}

/-- `frozen`: zero field, empty polynomial. -/
theorem bridge_frozen (i : Fin n) {p : QPoly}
    (hsf : shapeFaithful vs σq uq i.val (CoordShape.frozen : CoordShape n) p = true)
    (ν : DL.State (Var n)) :
    Term.eval (CoordShape.field i CoordShape.frozen) (scaleState (sigmaOf σq) ν)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν) := by
  have hpe : p = [] := by
    unfold shapeFaithful at hsf
    exact List.isEmpty_iff.mp hsf
  subst hpe
  show (0 : ℝ) = sigmaOf σq i * (uq.val * Term.eval (Term.const 0) ν)
  show (0 : ℝ) = sigmaOf σq i * (uq.val * 0)
  ring

/-- `constRate c`: constant field, constant polynomial. -/
theorem bridge_constRate (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos)
    (hud : uq.pos) (i : Fin n) {p : QPoly} {c : ℤ}
    (hp : PolyInv p)
    (hsf : shapeFaithful vs σq uq i.val (CoordShape.constRate c : CoordShape n) p = true)
    (ν : DL.State (Var n)) :
    Term.eval (CoordShape.field i (CoordShape.constRate c)) (scaleState (sigmaOf σq) ν)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν) := by
  unfold shapeFaithful at hsf
  simp only [Bool.and_eq_true] at hsf
  obtain ⟨hsup, heq⟩ := hsf
  have hσi := hσd i.val i.isLt
  have hA : (coeffOf p []).pos := coeffOf_pos hp.pos []
  have hval : (c : ℝ) = (coeffOf p []).val * sigmaOf σq i * uq.val := by
    have := qEq_val (qOfInt_pos c) (qMul_pos (qMul_pos hA hσi) hud) heq
    rw [qOfInt_val, qMul_val, qMul_val] at this
    exact this
  show (c : ℝ) = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν)
  rw [polyToTerm_eval, evalR_support_one hp [] Mono.varsNodup_nil hsup,
    Mono.evalR_nil, hval]
  ring

/-- `contract k c`: affine contraction toward `c` at integer rate `k`. -/
theorem bridge_contract (hnod : vs.Nodup) (hlen : vs.length = n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos) (hud : uq.pos)
    (i : Fin n) {p : QPoly} {k c : ℤ}
    (hp : PolyInv p)
    (hsf : shapeFaithful vs σq uq i.val (CoordShape.contract k c : CoordShape n) p = true)
    (ν : DL.State (Var n)) :
    Term.eval (CoordShape.field i (CoordShape.contract k c)) (scaleState (sigmaOf σq) ν)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν) := by
  unfold shapeFaithful at hsf
  simp only [Bool.and_eq_true] at hsf
  obtain ⟨⟨⟨hsup, hBneg⟩, hk⟩, hc⟩ := hsf
  set v := vs.getD i.val "" with hv
  have hσi := hσd i.val i.isLt
  have hA : (coeffOf p []).pos := coeffOf_pos hp.pos []
  have hB : (coeffOf p [(v, 1)]).pos := coeffOf_pos hp.pos [(v, 1)]
  have hBval : (coeffOf p [(v, 1)]).val < 0 := by
    have := qLt_val hB (qOfInt_pos 0) hBneg
    simpa using this
  have hkval : (k : ℝ) = -(coeffOf p [(v, 1)]).val * uq.val := by
    have := qEq_val (qOfInt_pos k) (qMul_pos (qNeg_pos hB) hud) hk
    rw [qOfInt_val, qMul_val, qNeg_val] at this
    exact this
  have hcval : (c : ℝ)
      = (coeffOf p []).val / -(coeffOf p [(v, 1)]).val * sigmaOf σq i := by
    have := qEq_val (qOfInt_pos c)
      (qMul_pos (qDiv_pos hA (by
        show (qNeg (coeffOf p [(v, 1)])).n ≠ 0
        unfold qNeg
        have : (coeffOf p [(v, 1)]).n ≠ 0 := by
          intro h0
          rw [QF.val] at hBval
          rw [h0] at hBval
          simp at hBval
        simpa using this)) hσi) hc
    rw [qOfInt_val, qMul_val, qDiv_val hA (qNeg_pos hB), qNeg_val] at this
    exact this
  have hρ := scaleState_rhoOf (n := n) hnod hlen σq ν i.isLt
  show (k : ℝ) * ((c : ℝ) - scaleState (sigmaOf σq) ν (Rv i))
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν)
  rw [polyToTerm_eval,
    evalR_support_two hp [] [(v, 1)] Mono.varsNodup_nil (varsNodup_single v 1)
      rfl hsup,
    Mono.evalR_nil, Mono.evalR_cons, Mono.evalR_nil]
  have hRv : scaleState (sigmaOf σq) ν (Rv i) = sigmaOf σq i * ν (Rv i) := rfl
  have hρv : rhoOf vs n ν v = ν (Rv i) := by
    rw [hv, rhoOf_getD hnod hlen ν i.isLt]
  rw [hRv, hρv, hkval, hcval]
  have hBne : (coeffOf p [(v, 1)]).val ≠ 0 := by linarith
  field_simp
  ring

/-- `contractQ kn kd c`: contraction at rational rate `kn/kd`. -/
theorem bridge_contractQ (hnod : vs.Nodup) (hlen : vs.length = n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos) (hud : uq.pos)
    (i : Fin n) {p : QPoly} {kn kd c : ℤ}
    (hp : PolyInv p)
    (hsf : shapeFaithful vs σq uq i.val
      (CoordShape.contractQ kn kd c : CoordShape n) p = true)
    (ν : DL.State (Var n)) :
    Term.eval (CoordShape.field i (CoordShape.contractQ kn kd c))
        (scaleState (sigmaOf σq) ν)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν) := by
  unfold shapeFaithful at hsf
  simp only [Bool.and_eq_true] at hsf
  obtain ⟨⟨⟨⟨hsup, hBneg⟩, hkd⟩, hk⟩, hc⟩ := hsf
  set v := vs.getD i.val "" with hv
  have hσi := hσd i.val i.isLt
  have hA : (coeffOf p []).pos := coeffOf_pos hp.pos []
  have hB : (coeffOf p [(v, 1)]).pos := coeffOf_pos hp.pos [(v, 1)]
  have hBval : (coeffOf p [(v, 1)]).val < 0 := by
    have := qLt_val hB (qOfInt_pos 0) hBneg
    simpa using this
  have hkdne : (kd : ℤ) ≠ 0 := by simpa using hkd
  have hkval : (kn : ℝ) / (kd : ℝ) = -(coeffOf p [(v, 1)]).val * uq.val := by
    have := qEq_val (qDiv_pos (qOfInt_pos kn) (by simpa [qOfInt] using hkdne))
      (qMul_pos (qNeg_pos hB) hud) hk
    rw [qDiv_val (qOfInt_pos kn) (qOfInt_pos kd), qOfInt_val, qOfInt_val,
      qMul_val, qNeg_val] at this
    exact this
  have hcval : (c : ℝ)
      = (coeffOf p []).val / -(coeffOf p [(v, 1)]).val * sigmaOf σq i := by
    have := qEq_val (qOfInt_pos c)
      (qMul_pos (qDiv_pos hA (by
        show (qNeg (coeffOf p [(v, 1)])).n ≠ 0
        unfold qNeg
        have : (coeffOf p [(v, 1)]).n ≠ 0 := by
          intro h0
          rw [QF.val] at hBval
          rw [h0] at hBval
          simp at hBval
        simpa using this)) hσi) hc
    rw [qOfInt_val, qMul_val, qDiv_val hA (qNeg_pos hB), qNeg_val] at this
    exact this
  show (kn : ℝ) / (kd : ℝ) * ((c : ℝ) - scaleState (sigmaOf σq) ν (Rv i))
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν)
  rw [polyToTerm_eval,
    evalR_support_two hp [] [(v, 1)] Mono.varsNodup_nil (varsNodup_single v 1)
      rfl hsup,
    Mono.evalR_nil, Mono.evalR_cons, Mono.evalR_nil]
  have hRv : scaleState (sigmaOf σq) ν (Rv i) = sigmaOf σq i * ν (Rv i) := rfl
  have hρv : rhoOf vs n ν v = ν (Rv i) := by
    rw [hv, rhoOf_getD hnod hlen ν i.isLt]
  rw [hRv, hρv, hkval, hcval]
  have hBne : (coeffOf p [(v, 1)]).val ≠ 0 := by linarith
  field_simp
  ring

/-- `driven j`: the coordinate is driven by coordinate `j`'s value. -/
theorem bridge_driven (hnod : vs.Nodup) (hlen : vs.length = n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos) (hud : uq.pos)
    (i : Fin n) {p : QPoly} {j : Fin n}
    (hp : PolyInv p)
    (hsf : shapeFaithful vs σq uq i.val (CoordShape.driven j : CoordShape n) p = true)
    (ν : DL.State (Var n)) :
    Term.eval (CoordShape.field i (CoordShape.driven j)) (scaleState (sigmaOf σq) ν)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν) := by
  unfold shapeFaithful at hsf
  simp only [Bool.and_eq_true] at hsf
  obtain ⟨⟨hsup, hCz⟩, hC⟩ := hsf
  set w := vs.getD j.val "" with hw
  have hσi := hσd i.val i.isLt
  have hσj := hσd j.val j.isLt
  have hCp : (coeffOf p [(w, 1)]).pos := coeffOf_pos hp.pos [(w, 1)]
  have hCval : (coeffOf p [(w, 1)]).val * sigmaOf σq i * uq.val = sigmaOf σq j := by
    have := qEq_val (qMul_pos (qMul_pos hCp hσi) hud) hσj hC
    rw [qMul_val, qMul_val] at this
    exact this
  show scaleState (sigmaOf σq) ν (Rv j)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν)
  rw [polyToTerm_eval,
    evalR_support_one hp [(w, 1)] (varsNodup_single w 1) hsup,
    Mono.evalR_cons, Mono.evalR_nil]
  have hRv : scaleState (sigmaOf σq) ν (Rv j) = sigmaOf σq j * ν (Rv j) := rfl
  have hρw : rhoOf vs n ν w = ν (Rv j) := by
    rw [hw, rhoOf_getD hnod hlen ν j.isLt]
  rw [hRv, hρw, ← hCval]
  ring

/-- `chase j k`: chases coordinate `j` at rate `k`. Needs `j ≠ i` (distinct driver). -/
theorem bridge_chase (hnod : vs.Nodup) (hlen : vs.length = n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos) (hud : uq.pos)
    (i : Fin n) {p : QPoly} {j : Fin n} {k : ℤ} (hij : j ≠ i)
    (hp : PolyInv p)
    (hsf : shapeFaithful vs σq uq i.val (CoordShape.chase j k : CoordShape n) p = true)
    (ν : DL.State (Var n)) :
    Term.eval (CoordShape.field i (CoordShape.chase j k)) (scaleState (sigmaOf σq) ν)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν) := by
  unfold shapeFaithful at hsf
  simp only [Bool.and_eq_true] at hsf
  obtain ⟨⟨⟨hsup, hCz⟩, hk⟩, hC⟩ := hsf
  set v := vs.getD i.val "" with hv
  set w := vs.getD j.val "" with hw
  have hvw : v ≠ w := by
    rw [hv, hw]
    intro hcontra
    apply hij
    have hiv : vs.getD i.val "" = vs[i.val]'(by omega) :=
      List.getD_eq_getElem _ _ (by omega)
    have hjv : vs.getD j.val "" = vs[j.val]'(by omega) :=
      List.getD_eq_getElem _ _ (by omega)
    rw [hiv, hjv] at hcontra
    have := (List.Nodup.getElem_inj_iff hnod).mp hcontra.symm
    exact Fin.ext this
  have hσi := hσd i.val i.isLt
  have hσj := hσd j.val j.isLt
  have hB : (coeffOf p [(v, 1)]).pos := coeffOf_pos hp.pos [(v, 1)]
  have hCp : (coeffOf p [(w, 1)]).pos := coeffOf_pos hp.pos [(w, 1)]
  have hkval : (k : ℝ) = -(coeffOf p [(v, 1)]).val * uq.val := by
    have := qEq_val (qOfInt_pos k) (qMul_pos (qNeg_pos hB) hud) hk
    rw [qOfInt_val, qMul_val, qNeg_val] at this
    exact this
  have hCval : (coeffOf p [(w, 1)]).val * sigmaOf σq i * uq.val = sigmaOf σq j := by
    have := qEq_val (qMul_pos (qMul_pos hCp hσi) hud) hσj hC
    rw [qMul_val, qMul_val] at this
    exact this
  show scaleState (sigmaOf σq) ν (Rv j)
      - (k : ℝ) * scaleState (sigmaOf σq) ν (Rv i)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν)
  rw [polyToTerm_eval,
    evalR_support_two hp [(v, 1)] [(w, 1)] (varsNodup_single v 1)
      (varsNodup_single w 1) (monoEq_single_ne hvw 1 1) hsup,
    Mono.evalR_cons, Mono.evalR_cons, Mono.evalR_nil]
  have hRvj : scaleState (sigmaOf σq) ν (Rv j) = sigmaOf σq j * ν (Rv j) := rfl
  have hRvi : scaleState (sigmaOf σq) ν (Rv i) = sigmaOf σq i * ν (Rv i) := rfl
  have hρv : rhoOf vs n ν v = ν (Rv i) := by
    rw [hv, rhoOf_getD hnod hlen ν i.isLt]
  have hρw : rhoOf vs n ν w = ν (Rv j) := by
    rw [hw, rhoOf_getD hnod hlen ν j.isLt]
  rw [hRvj, hRvi, hρv, hρw, hkval, ← hCval]
  ring

/-- `riccati b a`: quadratic drag `ḃ = b − (a/10⁶)x²`. -/
theorem bridge_riccati (hnod : vs.Nodup) (hlen : vs.length = n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf σq j) (hud : uq.pos)
    (i : Fin n) {p : QPoly} {b a : ℤ}
    (hp : PolyInv p)
    (hsf : shapeFaithful vs σq uq i.val (CoordShape.riccati b a : CoordShape n) p = true)
    (ν : DL.State (Var n)) :
    Term.eval (CoordShape.field i (CoordShape.riccati b a)) (scaleState (sigmaOf σq) ν)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν) := by
  unfold shapeFaithful at hsf
  simp only [Bool.and_eq_true] at hsf
  obtain ⟨⟨⟨hsup, hσz⟩, hb⟩, ha⟩ := hsf
  set v := vs.getD i.val "" with hv
  have hσi := hσd i.val i.isLt
  have hσine : sigmaOf σq i ≠ 0 := ne_of_gt (hσv i)
  have hA : (coeffOf p []).pos := coeffOf_pos hp.pos []
  have hBq : (coeffOf p [(v, 2)]).pos := coeffOf_pos hp.pos [(v, 2)]
  have hbval : (b : ℝ) = (coeffOf p []).val * sigmaOf σq i * uq.val := by
    have := qEq_val (qOfInt_pos b) (qMul_pos (qMul_pos hA hσi) hud) hb
    rw [qOfInt_val, qMul_val, qMul_val] at this
    exact this
  have haval : (a : ℝ) / 1000000
      = -(coeffOf p [(v, 2)]).val * uq.val / sigmaOf σq i := by
    have hσn : (σq.getD i.val (qOfInt 0)).n ≠ 0 := by
      unfold qIsZero at hσz
      simpa using hσz
    have := qEq_val (qDiv_pos (qOfInt_pos a) (by simp [qOfInt]))
      (qDiv_pos (qMul_pos (qNeg_pos hBq) hud) hσn) ha
    rw [qDiv_val (qOfInt_pos a) (qOfInt_pos 1000000),
      qDiv_val (qMul_pos (qNeg_pos hBq) hud) hσi,
      qOfInt_val, qOfInt_val, qMul_val, qNeg_val] at this
    push_cast at this
    exact this
  show (b : ℝ) - (a : ℝ) / 1000000
        * (scaleState (sigmaOf σq) ν (Rv i) * scaleState (sigmaOf σq) ν (Rv i))
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν)
  rw [polyToTerm_eval,
    evalR_support_two hp [] [(v, 2)] Mono.varsNodup_nil (varsNodup_single v 2)
      rfl hsup,
    Mono.evalR_nil, Mono.evalR_cons, Mono.evalR_nil]
  have hRvi : scaleState (sigmaOf σq) ν (Rv i) = sigmaOf σq i * ν (Rv i) := rfl
  have hρv : rhoOf vs n ν v = ν (Rv i) := by
    rw [hv, rhoOf_getD hnod hlen ν i.isLt]
  rw [hRvi, hρv, hbval, haval]
  field_simp
  ring

end ShapeBridges

/-! ### Wave 2 shape bridges: `pairSym` and `drivenDamp` -/

/-- Value of a three-monomial-support polynomial. -/
theorem evalR_support_three {p : QPoly} (hp : PolyInv p) (m1 m2 m3 : Mono)
    (h1 : Mono.varsNodup m1) (h2 : Mono.varsNodup m2) (h3 : Mono.varsNodup m3)
    (h12 : monoEq m1 m2 = false) (h13 : monoEq m1 m3 = false)
    (h23 : monoEq m2 m3 = false)
    (hsup : supportIn p [m1, m2, m3] = true) (ρ : String → ℝ) :
    QPoly.evalR ρ p = (coeffOf p m1).val * Mono.evalR ρ m1
      + (coeffOf p m2).val * Mono.evalR ρ m2
      + (coeffOf p m3).val * Mono.evalR ρ m3 := by
  rw [evalR_support ρ p hp [m1, m2, m3]
    (by
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h1
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h2
      · rw [List.mem_singleton.mp hm]
        exact h3)
    (by simp [h12, h13, h23]) hsup]
  simp [add_assoc]

/-- Distinct benchmark indices name distinct variables. -/
theorem getD_ne_of_ne {vs : List String} (hnod : vs.Nodup) (hlen : vs.length = n)
    {i j : Fin n} (hij : i ≠ j) : vs.getD i.val "" ≠ vs.getD j.val "" := by
  intro hcontra
  apply hij
  have hiv : vs.getD i.val "" = vs[i.val]'(by omega) :=
    List.getD_eq_getElem _ _ (by omega)
  have hjv : vs.getD j.val "" = vs[j.val]'(by omega) :=
    List.getD_eq_getElem _ _ (by omega)
  rw [hiv, hjv] at hcontra
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnod).mp hcontra)

/-- Nonzero value forces nonzero numerator. -/
theorem QF.n_ne_of_val_ne {a : QF} (h : a.val ≠ 0) : a.n ≠ 0 := by
  intro h0
  apply h
  unfold QF.val
  rw [h0]
  simp

/-- `monoEq` is length-invariant (multisets have equal card), so different lengths
are never `monoEq`. -/
theorem monoEq_of_ne_length {a b : Mono} (h : a.length ≠ b.length) :
    monoEq a b = false := by
  rcases hq : monoEq a b with _ | _
  · rfl
  · have := monoEq_multiset hq
    have hcard : a.length = b.length := by
      have := congrArg Multiset.card this
      simpa using this
    exact absurd hcard h

/-- `pairSym j c h`: one member of a weakly coupled symmetric pair. Needs `j ≠ i`. -/
theorem bridge_pairSym {vs : List String} {σq : List QF} {uq : QF}
    (hnod : vs.Nodup) (hlen : vs.length = n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos) (hud : uq.pos)
    (i : Fin n) {p : QPoly} {j : Fin n} {c h : ℤ} (hij : j ≠ i)
    (hp : PolyInv p)
    (hsf : shapeFaithful vs σq uq i.val (CoordShape.pairSym j c h : CoordShape n) p
      = true)
    (ν : DL.State (Var n)) :
    Term.eval (CoordShape.field i (CoordShape.pairSym j c h))
        (scaleState (sigmaOf σq) ν)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν) := by
  unfold shapeFaithful at hsf
  simp only [Bool.and_eq_true] at hsf
  obtain ⟨⟨⟨⟨hsup, hσjz⟩, hB1⟩, hh⟩, hc⟩ := hsf
  set v := vs.getD i.val "" with hv
  set w := vs.getD j.val "" with hw
  have hvw : v ≠ w := getD_ne_of_ne hnod hlen (fun hcontra => hij hcontra.symm)
  have hσi := hσd i.val i.isLt
  have hσj := hσd j.val j.isLt
  have hσjne : (σq.getD j.val (qOfInt 0)).val ≠ 0 :=
    qIsZero_false_val hσj (by simpa using hσjz)
  have hA : (coeffOf p []).pos := coeffOf_pos hp.pos []
  have hB : (coeffOf p [(v, 1)]).pos := coeffOf_pos hp.pos [(v, 1)]
  have hC : (coeffOf p [(w, 1)]).pos := coeffOf_pos hp.pos [(w, 1)]
  have hB1v : -(coeffOf p [(v, 1)]).val * uq.val = 1 := by
    have := qEq_val (qMul_pos (qNeg_pos hB) hud) (qOfInt_pos 1) hB1
    rw [qMul_val, qNeg_val, qOfInt_val] at this
    simpa using this
  have hBne : (coeffOf p [(v, 1)]).val ≠ 0 := by
    intro h0
    rw [h0] at hB1v
    simp at hB1v
  have hhv : (h : ℝ) / 1000
      = (coeffOf p [(w, 1)]).val * uq.val * sigmaOf σq i
        / (σq.getD j.val (qOfInt 0)).val := by
    have hσjn : (σq.getD j.val (qOfInt 0)).n ≠ 0 := QF.n_ne_of_val_ne hσjne
    have := qEq_val (qDiv_pos (qOfInt_pos h) (by simp [qOfInt]))
      (qDiv_pos (qMul_pos (qMul_pos hC hud) hσi) hσjn) hh
    rw [qDiv_val (qOfInt_pos h) (qOfInt_pos 1000),
      qDiv_val (qMul_pos (qMul_pos hC hud) hσi) hσj,
      qOfInt_val, qOfInt_val, qMul_val, qMul_val] at this
    push_cast at this
    exact this
  have hcv : (c : ℝ)
      = (coeffOf p []).val / -(coeffOf p [(v, 1)]).val * sigmaOf σq i := by
    have := qEq_val (qOfInt_pos c)
      (qMul_pos (qDiv_pos hA (by
        show (qNeg (coeffOf p [(v, 1)])).n ≠ 0
        unfold qNeg
        simpa using QF.n_ne_of_val_ne hBne)) hσi) hc
    rw [qOfInt_val, qMul_val, qDiv_val hA (qNeg_pos hB), qNeg_val] at this
    exact this
  have hu_eq : uq.val = (-(coeffOf p [(v, 1)]).val)⁻¹ :=
    eq_inv_of_mul_eq_one_right hB1v
  show (c : ℝ) - scaleState (sigmaOf σq) ν (Rv i)
      + (h : ℝ) / 1000 * scaleState (sigmaOf σq) ν (Rv j)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν)
  rw [polyToTerm_eval,
    evalR_support_three hp [] [(v, 1)] [(w, 1)] Mono.varsNodup_nil
      (varsNodup_single v 1) (varsNodup_single w 1) rfl rfl
      (monoEq_single_ne hvw 1 1) hsup,
    Mono.evalR_nil, Mono.evalR_cons, Mono.evalR_cons, Mono.evalR_nil]
  have hRvi : scaleState (sigmaOf σq) ν (Rv i) = sigmaOf σq i * ν (Rv i) := rfl
  have hRvj : scaleState (sigmaOf σq) ν (Rv j) = sigmaOf σq j * ν (Rv j) := rfl
  have hρv : rhoOf vs n ν v = ν (Rv i) := by
    rw [hv, rhoOf_getD hnod hlen ν i.isLt]
  have hρw : rhoOf vs n ν w = ν (Rv j) := by
    rw [hw, rhoOf_getD hnod hlen ν j.isLt]
  have hσjs : sigmaOf σq j = (σq.getD j.val (qOfInt 0)).val := rfl
  rw [hRvi, hRvj, hρv, hρw, hcv, hhv, hu_eq, hσjs]
  have hnBne : -(coeffOf p [(v, 1)]).val ≠ 0 := neg_ne_zero.mpr hBne
  field_simp
  ring

/-- The damper product term evaluates to `1 − Σ (aₙ/a_d)·x_d²`. -/
theorem dampFoldr_eval (ν' : DL.State (Var n)) : ∀ (ds : List (Fin n × ℤ × ℤ)),
    Term.eval (ds.foldr (fun d acc =>
      Term.binop AOp.sub acc
        (Term.binop AOp.mul (Term.const ((d.2.1 : ℝ) / (d.2.2 : ℝ)))
          (Term.binop AOp.mul (Term.var (Rv d.1)) (Term.var (Rv d.1)))))
      (Term.const 1)) ν'
    = 1 - (ds.map (fun d =>
        (d.2.1 : ℝ) / (d.2.2 : ℝ) * (ν' (Rv d.1) * ν' (Rv d.1)))).sum := by
  intro ds
  induction ds with
  | nil => simp [Term.eval]
  | cons d ds ih =>
      show Term.eval _ ν' - (d.2.1 : ℝ) / (d.2.2 : ℝ) * (ν' (Rv d.1) * ν' (Rv d.1)) = _
      rw [ih]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- `monoMul` of distinct singleton monomials, explicitly. -/
theorem monoMul_single_single {w x : String} (hwx : w ≠ x) (k l : Nat) :
    monoMul [(w, k)] [(x, l)] = [(x, l), (w, k)] := by
  show monoMul [] (monoInsert w k [(x, l)]) = _
  unfold monoMul monoInsert
  rw [if_neg (by simpa using hwx)]
  rfl

/-- Distinct-headed damper pairs are not `monoEq`. -/
theorem monoEq_pair_ne {x x' w : String} (hxx' : x ≠ x') (hxw : x ≠ w)
    (k k' l l' : Nat) : monoEq [(x, k), (w, l)] [(x', k'), (w, l')] = false := by
  have hex : monoExtract x [(x', k'), (w, l')] = none := by
    unfold monoExtract
    rw [if_neg (by simpa using hxx')]
    unfold monoExtract
    rw [if_neg (by simpa using hxw)]
    rfl
  unfold monoEq
  rw [hex]

/-- Products distribute over list sums (left factor). -/
theorem sumMulLeft {α : Type*} (l : List α) (f : α → ℝ) (r : ℝ) :
    (l.map fun x => r * f x).sum = r * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- `drivenDamp j dampers`: damped integrator. Needs the driver and dampers distinct
(`j` differs from every damper index; damper indices are duplicate-free). -/
theorem bridge_drivenDamp {vs : List String} {σq : List QF} {uq : QF}
    (hnod : vs.Nodup) (hlen : vs.length = n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos) (hud : uq.pos)
    (i : Fin n) {p : QPoly} {j : Fin n} {dampers : List (Fin n × ℤ × ℤ)}
    (hdj : ∀ d ∈ dampers, d.1 ≠ j)
    (hddn : (dampers.map (·.1)).Nodup)
    (hp : PolyInv p)
    (hsf : shapeFaithful vs σq uq i.val
      (CoordShape.drivenDamp j dampers : CoordShape n) p = true)
    (ν : DL.State (Var n)) :
    Term.eval (CoordShape.field i (CoordShape.drivenDamp j dampers))
        (scaleState (sigmaOf σq) ν)
      = sigmaOf σq i * (uq.val * Term.eval (polyToTerm vs n p) ν) := by
  unfold shapeFaithful at hsf
  simp only [Bool.and_eq_true] at hsf
  obtain ⟨⟨⟨hCz, hC⟩, hsup⟩, hall⟩ := hsf
  set w := vs.getD j.val "" with hw
  have hσi := hσd i.val i.isLt
  have hσj := hσd j.val j.isLt
  have hCp : (coeffOf p [(w, 1)]).pos := coeffOf_pos hp.pos [(w, 1)]
  have hCne : (coeffOf p [(w, 1)]).val ≠ 0 :=
    qIsZero_false_val hCp (by simpa using hCz)
  have hCval : (coeffOf p [(w, 1)]).val * sigmaOf σq i * uq.val = sigmaOf σq j := by
    have := qEq_val (qMul_pos (qMul_pos hCp hσi) hud) hσj hC
    rw [qMul_val, qMul_val] at this
    exact this
  have hdw : ∀ d ∈ dampers, vs.getD d.1.val "" ≠ w := by
    intro d hd
    exact getD_ne_of_ne hnod hlen (hdj d hd)
  have hmm : ∀ d ∈ dampers,
      monoMul [(w, 1)] [(vs.getD d.1.val "", 2)]
        = [(vs.getD d.1.val "", 2), (w, 1)] := by
    intro d hd
    exact monoMul_single_single (fun hcontra => hdw d hd hcontra.symm) 1 2
  have hms_eq : dampers.map (fun d => monoMul [(w, 1)] [(vs.getD d.1.val "", 2)])
      = dampers.map (fun d => [(vs.getD d.1.val "", 2), (w, 1)]) :=
    List.map_congr_left hmm
  rw [hms_eq] at hsup
  -- duplicate-free support list
  have hnd : ∀ m ∈ ([(w, 1)] :: dampers.map
      (fun d => [(vs.getD d.1.val "", 2), (w, 1)])), Mono.varsNodup m := by
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact varsNodup_single w 1
    · simp only [List.mem_map] at hm
      obtain ⟨d, hd, rfl⟩ := hm
      unfold Mono.varsNodup
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
        List.not_mem_nil, not_false_iff, List.nodup_nil, and_true]
      simpa using hdw d hd
  have hpw : ([(w, 1)] :: dampers.map
      (fun d => [(vs.getD d.1.val "", 2), (w, 1)])).Pairwise
      (fun m m' => monoEq m m' = false) := by
    refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · intro m hm
      simp only [List.mem_map] at hm
      obtain ⟨d, hd, rfl⟩ := hm
      exact monoEq_of_ne_length (by simp)
    · rw [List.pairwise_map]
      have hpar : dampers.Pairwise (fun d d' => d.1 ≠ d'.1) := by
        have h' := hddn
        unfold List.Nodup at h'
        rwa [List.pairwise_map] at h'
      refine List.Pairwise.imp_of_mem ?_ hpar
      intro d d' hd hd' hne
      exact monoEq_pair_ne (getD_ne_of_ne hnod hlen hne)
        (getD_ne_of_ne hnod hlen (hdj d hd)) 2 2 1 1
  have hcrux := evalR_support (rhoOf vs n ν) p hp _ hnd hpw hsup
  -- per-damper value law
  have hdval : ∀ d ∈ dampers,
      (d.2.1 : ℝ) / (d.2.2 : ℝ)
        * ((σq.getD d.1.val (qOfInt 0)).val * (σq.getD d.1.val (qOfInt 0)).val)
      = -(coeffOf p [(vs.getD d.1.val "", 2), (w, 1)]).val
        / (coeffOf p [(w, 1)]).val := by
    intro d hd
    have hfact := List.all_eq_true.mp hall d hd
    simp only [Bool.and_eq_true] at hfact
    obtain ⟨hdd, hqe⟩ := hfact
    rw [hmm d hd] at hqe
    have hddne : (d.2.2 : ℤ) ≠ 0 := by simpa using hdd
    have hcoeffp := coeffOf_pos hp.pos [(vs.getD d.1.val "", 2), (w, 1)]
    have hσdp := hσd d.1.val d.1.isLt
    have hval := qEq_val
      (qMul_pos (qDiv_pos (qOfInt_pos d.2.1) (by simpa [qOfInt] using hddne))
        (qMul_pos hσdp hσdp))
      (qDiv_pos (qNeg_pos hcoeffp) (QF.n_ne_of_val_ne hCne)) hqe
    rw [qMul_val, qDiv_val (qOfInt_pos d.2.1) (qOfInt_pos d.2.2), qMul_val,
      qDiv_val (qNeg_pos hcoeffp) hCp, qNeg_val, qOfInt_val, qOfInt_val] at hval
    exact hval
  -- assemble
  have hfield : Term.eval (CoordShape.field i (CoordShape.drivenDamp j dampers))
      (scaleState (sigmaOf σq) ν)
      = scaleState (sigmaOf σq) ν (Rv j)
        * (1 - (dampers.map (fun d =>
            (d.2.1 : ℝ) / (d.2.2 : ℝ)
            * (scaleState (sigmaOf σq) ν (Rv d.1)
              * scaleState (sigmaOf σq) ν (Rv d.1)))).sum) := by
    show scaleState (sigmaOf σq) ν (Rv j) * Term.eval _ _ = _
    rw [dampFoldr_eval]
  rw [hfield, polyToTerm_eval, hcrux]
  simp only [List.map_cons, List.sum_cons, List.map_map]
  have hRvj : scaleState (sigmaOf σq) ν (Rv j) = sigmaOf σq j * ν (Rv j) := rfl
  have hρw : rhoOf vs n ν w = ν (Rv j) := by
    rw [hw, rhoOf_getD hnod hlen ν j.isLt]
  -- the damper sums cancel term-by-term
  have hcomb : ∀ (ds : List (Fin n × ℤ × ℤ)), (∀ d ∈ ds, d ∈ dampers) →
      sigmaOf σq j * ν (Rv j) * (ds.map (fun d =>
        (d.2.1 : ℝ) / (d.2.2 : ℝ)
        * (scaleState (sigmaOf σq) ν (Rv d.1)
          * scaleState (sigmaOf σq) ν (Rv d.1)))).sum
      = -(sigmaOf σq i * (uq.val * (ds.map ((fun m =>
          (coeffOf p m).val * Mono.evalR (rhoOf vs n ν) m) ∘
          fun d => [(vs.getD d.1.val "", 2), (w, 1)])).sum)) := by
    intro ds
    induction ds with
    | nil => simp
    | cons d ds ih =>
        intro hsub
        have hd : d ∈ dampers := hsub d (List.mem_cons_self ..)
        have hvd := hdval d hd
        simp only [List.map_cons, List.sum_cons, Function.comp_apply]
        rw [mul_add, ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx))]
        have hRvd : scaleState (sigmaOf σq) ν (Rv d.1)
            = sigmaOf σq d.1 * ν (Rv d.1) := rfl
        have hρd : rhoOf vs n ν (vs.getD d.1.val "") = ν (Rv d.1) :=
          rhoOf_getD hnod hlen ν d.1.isLt
        have hσds : sigmaOf σq d.1 = (σq.getD d.1.val (qOfInt 0)).val := rfl
        have hvd' : (d.2.1 : ℝ) / (d.2.2 : ℝ)
            * ((σq.getD d.1.val (qOfInt 0)).val * (σq.getD d.1.val (qOfInt 0)).val)
            * (coeffOf p [(w, 1)]).val
            = -(coeffOf p [(vs.getD d.1.val "", 2), (w, 1)]).val := by
          rw [hvd]
          field_simp
        simp only [Mono.evalR_cons, Mono.evalR_nil]
        rw [hRvd, hρd, hρw, hσds, ← hCval]
        linear_combination (sigmaOf σq i * uq.val * ν (Rv j)
          * (ν (Rv d.1) * ν (Rv d.1))) * hvd'
  have hsum := hcomb dampers (fun d hd => hd)
  simp only [Mono.evalR_cons, Mono.evalR_nil]
  rw [hRvj, hρw, mul_sub, hsum, ← hCval]
  ring


/-! ## Part 6: envelope and guard correspondence under scaling

The scaled model's domain/guard formulas carry integer constants; the real side's carry
the parsed rational bounds. `envFaithful`'s cross-multiplied checks say exactly that each
integer constant is the rational bound times the (positive) coordinate scale, which turns
satisfaction at a scaled state into satisfaction of the real bound at the raw state. -/

/-! ### Bounds positivity -/

/-- All bounds in a `boundsOfForm` output have positive denominators. -/
def BoundsPos (bs : List (String × Option QF × Option QF)) : Prop :=
  ∀ e ∈ bs, (∀ q, e.2.1 = some q → q.pos) ∧ (∀ q, e.2.2 = some q → q.pos)

theorem BoundsPos.nil : BoundsPos [] := by intro e he; exact absurd he (by simp)

/-- The and-merge step preserves bounds positivity. -/
theorem boundsMerge_pos {ba : List (String × Option QF × Option QF)}
    (hba : BoundsPos ba) :
    ∀ {bb : List (String × Option QF × Option QF)}, BoundsPos bb →
    BoundsPos (bb.foldl (fun acc e =>
      let (v, lo, hi) := e
      match acc.find? (fun e2 => e2.1 == v) with
      | none => acc ++ [(v, lo, hi)]
      | some e0 =>
          let lo' := match e0.2.1, lo with
            | none, x => x | x, none => x
            | some x, some y => some (if qLt x y then y else x)
          let hi' := match e0.2.2, hi with
            | none, x => x | x, none => x
            | some x, some y => some (if qLt x y then x else y)
          acc.map (fun e2 => if e2.1 == v then (v, lo', hi') else e2)) ba) := by
  intro bb
  induction bb generalizing ba with
  | nil => intro _; exact hba
  | cons e bb ih =>
      intro hbb
      obtain ⟨v, lo, hi⟩ := e
      have he := hbb (v, lo, hi) (List.mem_cons_self ..)
      have hbb' : BoundsPos bb := fun f hf => hbb f (List.mem_cons_of_mem _ hf)
      simp only [List.foldl_cons]
      -- the one-step accumulator is positive again
      rcases hfind : ba.find? (fun e2 => e2.1 == v) with _ | e0
      · rw [hfind]
        refine ih (ba := ba ++ [(v, lo, hi)]) ?_ hbb'
        intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hba f hf
        · rw [List.mem_singleton.mp hf]
          exact he
      · rw [hfind]
        have he0 := hba e0 (List.mem_of_find?_eq_some hfind)
        refine ih (ba := _) ?_ hbb'
        intro f hf
        simp only [List.mem_map] at hf
        obtain ⟨g, hg, rfl⟩ := hf
        by_cases hgv : (g.1 == v) = true
        · rw [if_pos hgv]
          constructor
          · intro qq hqq
            simp only at hqq
            revert hqq
            rcases h0 : e0.2.1 with _ | x <;> rcases hy : lo with _ | y
            · intro h; exact absurd h (by simp)
            · intro h
              injection h with h'
              exact h'.symm ▸ he.1 y hy
            · intro h
              injection h with h'
              exact h'.symm ▸ he0.1 x h0
            · intro h
              injection h with h'
              subst h'
              split
              · exact he.1 y hy
              · exact he0.1 x h0
          · intro qq hqq
            simp only at hqq
            revert hqq
            rcases h0 : e0.2.2 with _ | x <;> rcases hy : hi with _ | y
            · intro h; exact absurd h (by simp)
            · intro h
              injection h with h'
              exact h'.symm ▸ he.2 y hy
            · intro h
              injection h with h'
              exact h'.symm ▸ he0.2 x h0
            · intro h
              injection h with h'
              subst h'
              split
              · exact he0.2 x h0
              · exact he.2 y hy
        · rw [if_neg hgv]
          exact hba g hg

theorem boundsOfForm_pos : ∀ {f : Parse.PForm} {bs},
    boundsOfForm f = some bs → BoundsPos bs := by
  intro f
  induction f with
  | tt =>
      intro bs h
      injection h with h'
      subst h'
      exact BoundsPos.nil
  | cmp op a b =>
      intro bs h
      have hsingle : ∀ (v : String) (lo hi : Option QF),
          (∀ q, lo = some q → q.pos) → (∀ q, hi = some q → q.pos) →
          BoundsPos [(v, lo, hi)] := by
        intro v lo hi hl hh e he
        rw [List.mem_singleton.mp he]
        exact ⟨hl, hh⟩
      unfold boundsOfForm at h
      split at h
      · -- var ⋈ num
        rcases hq : parseQ _ with _ | q <;> rw [hq] at h
        · simp at h
        have hqp := parseQ_pos hq
        simp only [Option.bind_eq_bind, Option.bind] at h
        split at h <;>
          first
            | (injection h with h'
               subst h'
               refine hsingle _ _ _ ?_ ?_ <;>
                 intro r hr <;>
                 first
                   | (injection hr with h2
                      subst h2
                      exact hqp)
                   | injection hr)
            | simp at h
      · -- num ⋈ var
        rcases hq : parseQ _ with _ | q <;> rw [hq] at h
        · simp at h
        have hqp := parseQ_pos hq
        simp only [Option.bind_eq_bind, Option.bind] at h
        split at h <;>
          first
            | (injection h with h'
               subst h'
               refine hsingle _ _ _ ?_ ?_ <;>
                 intro r hr <;>
                 first
                   | (injection hr with h2
                      subst h2
                      exact hqp)
                   | injection hr)
            | simp at h
      · simp at h
  | and a b iha ihb =>
      intro bs h
      unfold boundsOfForm at h
      rcases hba : boundsOfForm a with _ | ba <;> rw [hba] at h
      · simp at h
      rcases hbb : boundsOfForm b with _ | bb <;> rw [hbb] at h
      · simp at h
      injection h with h'
      subst h'
      exact boundsMerge_pos (iha hba) (ihb hbb)
  | or a b iha ihb => intro bs h; exact absurd h (by simp [boundsOfForm])
  | not a iha => intro bs h; exact absurd h (by simp [boundsOfForm])

theorem boundOf_pos {bs} (hbs : BoundsPos bs) (v : String) :
    (∀ q, (boundOf bs v).1 = some q → q.pos)
    ∧ (∀ q, (boundOf bs v).2 = some q → q.pos) := by
  unfold boundOf
  rcases hf : bs.find? (fun e => e.1 == v) with _ | e <;> rw [hf]
  · exact ⟨fun q h => absurd h (by simp), fun q h => absurd h (by simp)⟩
  · have := hbs e (List.mem_of_find?_eq_some hf)
    simpa using this

/-! ### Real-side band formulas -/

/-- Real-side band conjunct for one coordinate. -/
noncomputable def bandFormulaR (i : Fin n) (lo hi : Option QF) : Formula (Var n) :=
  Formula.and
    (match lo with
     | some q => Formula.cmp CompOp.le (Term.const q.val) (Term.var (Rv i))
     | none => Formula.tt)
    (match hi with
     | some q => Formula.cmp CompOp.le (Term.var (Rv i)) (Term.const q.val)
     | none => Formula.tt)

/-- One-band correspondence: real satisfaction ↔ scaled satisfaction. -/
theorem envFaithful_sat {σq : List QF} {b : Band} {lo hi : Option QF} (i : Fin n)
    (hσd : (σq.getD i.val (qOfInt 0)).pos) (hσv : 0 < sigmaOf σq i)
    (hlop : ∀ q, lo = some q → q.pos) (hhip : ∀ q, hi = some q → q.pos)
    (hef : envFaithful (σq.getD i.val (qOfInt 0)) b lo hi = true)
    (ν : DL.State (Var n)) :
    Formula.sat (bandFormulaR i lo hi) ν
      ↔ Formula.sat (Band.formula i b) (scaleState (sigmaOf σq) ν) := by
  unfold envFaithful at hef
  simp only [Bool.and_eq_true] at hef
  obtain ⟨hlo, hhi⟩ := hef
  unfold bandFormulaR Band.formula
  simp only [Formula.sat]
  have hRvi : scaleState (sigmaOf σq) ν (Rv i) = sigmaOf σq i * ν (Rv i) := rfl
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · revert hlo
      rcases b.lo with _ | z <;> rcases hloe : lo with _ | q <;> intro hlo
      · simp [Formula.sat]
      · exact absurd hlo (by simp)
      · exact absurd hlo (by simp)
      · have hzval : (z : ℝ) = q.val * sigmaOf σq i := by
          have := qEq_val (qOfInt_pos z) (qMul_pos (hlop q hloe) hσd) hlo
          rw [qOfInt_val, qMul_val] at this
          exact this
        rw [hloe] at h1
        simp only [Formula.sat, CompOp.interp, Term.eval] at h1 ⊢
        rw [hRvi, hzval]
        calc q.val * sigmaOf σq i ≤ ν (Rv i) * sigmaOf σq i := by
              exact mul_le_mul_of_nonneg_right h1 hσv.le
          _ = sigmaOf σq i * ν (Rv i) := by ring
    · revert hhi
      rcases b.hi with _ | z <;> rcases hhie : hi with _ | q <;> intro hhi
      · simp [Formula.sat]
      · exact absurd hhi (by simp)
      · exact absurd hhi (by simp)
      · have hzval : (z : ℝ) = q.val * sigmaOf σq i := by
          have := qEq_val (qOfInt_pos z) (qMul_pos (hhip q hhie) hσd) hhi
          rw [qOfInt_val, qMul_val] at this
          exact this
        rw [hhie] at h2
        simp only [Formula.sat, CompOp.interp, Term.eval] at h2 ⊢
        rw [hRvi, hzval]
        calc sigmaOf σq i * ν (Rv i) = ν (Rv i) * sigmaOf σq i := by ring
          _ ≤ q.val * sigmaOf σq i := mul_le_mul_of_nonneg_right h2 hσv.le
  · rintro ⟨h1, h2⟩
    constructor
    · revert hlo
      rcases hbe : b.lo with _ | z <;> rcases hloe : lo with _ | q <;> intro hlo
      · simp [Formula.sat]
      · exact absurd hlo (by simp)
      · exact absurd hlo (by simp)
      · have hzval : (z : ℝ) = q.val * sigmaOf σq i := by
          have := qEq_val (qOfInt_pos z) (qMul_pos (hlop q hloe) hσd) hlo
          rw [qOfInt_val, qMul_val] at this
          exact this
        rw [hbe] at h1
        simp only [Formula.sat, CompOp.interp, Term.eval] at h1 ⊢
        rw [hRvi, hzval] at h1
        exact le_of_mul_le_mul_right (by
          calc q.val * sigmaOf σq i ≤ sigmaOf σq i * ν (Rv i) := h1
            _ = ν (Rv i) * sigmaOf σq i := by ring) hσv
    · revert hhi
      rcases hbe : b.hi with _ | z <;> rcases hhie : hi with _ | q <;> intro hhi
      · simp [Formula.sat]
      · exact absurd hhi (by simp)
      · exact absurd hhi (by simp)
      · have hzval : (z : ℝ) = q.val * sigmaOf σq i := by
          have := qEq_val (qOfInt_pos z) (qMul_pos (hhip q hhie) hσd) hhi
          rw [qOfInt_val, qMul_val] at this
          exact this
        rw [hbe] at h2
        simp only [Formula.sat, CompOp.interp, Term.eval] at h2 ⊢
        rw [hRvi, hzval] at h2
        exact le_of_mul_le_mul_right (by
          calc ν (Rv i) * sigmaOf σq i = sigmaOf σq i * ν (Rv i) := by ring
            _ ≤ q.val * sigmaOf σq i := h2) hσv

/-! ### Envelope and guard formulas -/

/-- Real-side envelope: the per-coordinate parsed bounds, conjoined. -/
noncomputable def envFormulaR (vs : List String) (n : ℕ)
    (eb : List (String × Option QF × Option QF)) : Formula (Var n) :=
  (List.finRange n).foldr (fun i acc =>
    Formula.and (bandFormulaR i (boundOf eb (vs.getD i.val "")).1
      (boundOf eb (vs.getD i.val "")).2) acc) Formula.tt

/-- Conjunction folds correspond pointwise. -/
theorem foldr_and_sat {l : List (Fin n)} {f g : Fin n → Formula (Var n)}
    {ν ν' : DL.State (Var n)}
    (h : ∀ i ∈ l, (Formula.sat (f i) ν ↔ Formula.sat (g i) ν')) :
    (Formula.sat (l.foldr (fun i acc => Formula.and (f i) acc) Formula.tt) ν
      ↔ Formula.sat (l.foldr (fun i acc => Formula.and (g i) acc) Formula.tt) ν') := by
  induction l with
  | nil => simp [Formula.sat]
  | cons i l ih =>
      simp only [List.foldr_cons, Formula.sat]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(h i (List.mem_cons_self ..)).mp h1,
          (ih (fun x hx => h x (List.mem_cons_of_mem _ hx))).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(h i (List.mem_cons_self ..)).mpr h1,
          (ih (fun x hx => h x (List.mem_cons_of_mem _ hx))).mpr h2⟩

/-- **The `hdom` discharger**: the real envelope corresponds to the scaled envelope. -/
theorem envFormulaR_sat (M : SettlingModel n) {vs : List String} {σq : List QF}
    {eb : List (String × Option QF × Option QF)}
    (hbs : BoundsPos eb)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf σq j)
    (hef : ∀ i : Fin n, envFaithful (σq.getD i.val (qOfInt 0)) (M.env i)
        (boundOf eb (vs.getD i.val "")).1 (boundOf eb (vs.getD i.val "")).2 = true)
    (ν : DL.State (Var n)) :
    Formula.sat (envFormulaR vs n eb) ν
      ↔ Formula.sat M.envF (scaleState (sigmaOf σq) ν) := by
  unfold envFormulaR SettlingModel.envF
  refine foldr_and_sat ?_
  intro i _
  exact envFaithful_sat i (hσd i.val i.isLt) (hσv i)
    (boundOf_pos hbs (vs.getD i.val "")).1 (boundOf_pos hbs (vs.getD i.val "")).2
    (hef i) ν

/-- **The guard-band correspondence** (settling variant): the parsed guard bounds match
the scaled mode band. `bandDom` is definitionally the two-sided `Band.formula`, so this
is the one-band lemma at a both-sides-present band. -/
theorem bandSettling_sat {vs : List String} {σq : List QF}
    {gb : List (String × Option QF × Option QF)} (hgb : BoundsPos gb)
    (m : SettlingMode n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf σq j)
    (hband :
      (match (boundOf gb (vs.getD m.gcoord.val "")).1 with
       | some q => qEq (qOfInt m.glo) (qMul q (σq.getD m.gcoord.val (qOfInt 0)))
       | none => false) = true ∧
      (match (boundOf gb (vs.getD m.gcoord.val "")).2 with
       | some q => qEq (qOfInt m.ghi) (qMul q (σq.getD m.gcoord.val (qOfInt 0)))
       | none => false) = true)
    (ν : DL.State (Var n)) :
    Formula.sat (bandFormulaR m.gcoord (boundOf gb (vs.getD m.gcoord.val "")).1
        (boundOf gb (vs.getD m.gcoord.val "")).2) ν
      ↔ Formula.sat (bandDom m.gcoord (m.glo : ℝ) (m.ghi : ℝ))
          (scaleState (sigmaOf σq) ν) := by
  obtain ⟨hlo, hhi⟩ := hband
  -- both bounds are present
  rcases hloe : (boundOf gb (vs.getD m.gcoord.val "")).1 with _ | qlo
  · rw [hloe] at hlo
    exact absurd hlo (by simp)
  rcases hhie : (boundOf gb (vs.getD m.gcoord.val "")).2 with _ | qhi
  · rw [hhie] at hhi
    exact absurd hhi (by simp)
  rw [hloe] at hlo
  rw [hhie] at hhi
  -- reuse the band lemma at the two-sided band
  have hef : envFaithful (σq.getD m.gcoord.val (qOfInt 0))
      ⟨some m.glo, some m.ghi⟩ (some qlo) (some qhi) = true := by
    unfold envFaithful
    simp only [Bool.and_eq_true]
    exact ⟨hlo, hhi⟩
  have hcorr := envFaithful_sat m.gcoord (hσd m.gcoord.val m.gcoord.isLt)
    (hσv m.gcoord)
    (fun r hr => by
      have h' : qlo = r := by injection hr
      exact h' ▸ (boundOf_pos hgb (vs.getD m.gcoord.val "")).1 qlo hloe)
    (fun r hr => by
      have h' : qhi = r := by injection hr
      exact h' ▸ (boundOf_pos hgb (vs.getD m.gcoord.val "")).2 qhi hhie)
    hef ν
  exact hcorr

/-! ## Part 7: assembly — `faithfulSettling` discharges the rescale hypotheses

Extraction of the kernel Boolean into per-mode, per-coordinate facts, the real-side
model definitions, and the per-mode pushforward dispatch. -/

/-- The real-side field of a parsed mode: each coordinate's ode as a polynomial term. -/
noncomputable def realFieldOf (vs : List String) (pm : Parse.PMode) (n : ℕ) :
    Fin n → Term (Var n) :=
  fun i => match pm.odes.find? (fun o => o.1 == vs.getD i.val "") with
    | some o => match exprPoly o.2 with
      | some p => polyToTerm vs n p
      | none => Term.const 0
    | none => Term.const 0

/-- Decidable index-hygiene of a shape (the side conditions the shape bridges need). -/
def shapeIdxOkB (i : Fin n) : CoordShape n → Bool
  | .chase j _ => j != i
  | .pairSym j _ _ => j != i
  | .drivenDamp j ds =>
      ds.all (fun d => d.1 != j) && decide (ds.map (·.1)).Nodup
  | _ => true

/-! ### Extraction lemmas -/

/-- Per-coordinate ode facts from `modeCore` (full-width models: `vs.length = n`). -/
theorem modeCore_ode_facts {vs : List String} {σq : List QF} {uq : QF}
    {names : List String} {self : Nat} {pm : Parse.PMode} {m : SettlingMode n}
    {env : Fin n → Band} (hlen : vs.length = n)
    (hmc : modeCore vs σq uq names self pm m env = true) (i : Fin n) :
    ∃ o p, pm.odes.find? (fun o => o.1 == vs.getD i.val "") = some o
      ∧ exprPoly o.2 = some p
      ∧ shapeFaithful vs σq uq i.val (m.shapes i) p = true := by
  unfold modeCore at hmc
  simp only [Bool.and_eq_true] at hmc
  have hall := hmc.1.1.1
  have hi : i.val ∈ List.range vs.length := List.mem_range.mpr (by omega)
  have hfact := List.all_eq_true.mp hall i.val hi
  rw [dif_pos i.isLt] at hfact
  rcases hfind : pm.odes.find? (fun o => o.1 == vs.getD i.val "") with _ | o <;>
    rw [hfind] at hfact
  · exact absurd hfact (by simp)
  have hfact' : (match exprPoly o.2 with
      | some p => shapeFaithful vs σq uq i.val (m.shapes ⟨i.val, i.isLt⟩) p
      | none => false) = true := hfact
  rcases hep : exprPoly o.2 with _ | pq <;> rw [hep] at hfact'
  · exact absurd hfact' (by simp)
  exact ⟨o, pq, hfind, hep, by simpa using hfact'⟩

/-- Envelope facts from `modeCore`. -/
theorem modeCore_env_facts {vs : List String} {σq : List QF} {uq : QF}
    {names : List String} {self : Nat} {pm : Parse.PMode} {m : SettlingMode n}
    {env : Fin n → Band} (hlen : vs.length = n)
    (hmc : modeCore vs σq uq names self pm m env = true) :
    ∃ eb, boundsOfForm pm.evolve = some eb
      ∧ ∀ i : Fin n, envFaithful (σq.getD i.val (qOfInt 0)) (env i)
          (boundOf eb (vs.getD i.val "")).1 (boundOf eb (vs.getD i.val "")).2 = true := by
  unfold modeCore at hmc
  simp only [Bool.and_eq_true] at hmc
  have henv := hmc.1.2
  rcases heb : boundsOfForm pm.evolve with _ | eb <;> rw [heb] at henv
  · exact absurd henv (by simp)
  refine ⟨eb, rfl, ?_⟩
  intro i
  have hi : i.val ∈ List.range vs.length := List.mem_range.mpr (by omega)
  have hfact := List.all_eq_true.mp henv i.val hi
  rw [dif_pos i.isLt] at hfact
  simpa using hfact

/-- Guard-band facts from `bandSettling`. -/
theorem bandSettling_facts {vs : List String} {σq : List QF} {pm : Parse.PMode}
    {m : SettlingMode n} (hbs : bandSettling vs σq pm m = true) :
    ∃ gb, boundsOfForm pm.guard = some gb
      ∧ (match (boundOf gb (vs.getD m.gcoord.val "")).1 with
         | some q => qEq (qOfInt m.glo) (qMul q (σq.getD m.gcoord.val (qOfInt 0)))
         | none => false) = true
      ∧ (match (boundOf gb (vs.getD m.gcoord.val "")).2 with
         | some q => qEq (qOfInt m.ghi) (qMul q (σq.getD m.gcoord.val (qOfInt 0)))
         | none => false) = true := by
  unfold bandSettling at hbs
  rcases hgb : boundsOfForm pm.guard with _ | gb <;> rw [hgb] at hbs
  · exact absurd hbs (by simp)
  simp only [Bool.and_eq_true] at hbs
  exact ⟨gb, rfl, hbs.1, hbs.2⟩

/-- Frame facts from `faithfulSettling`. -/
theorem faithfulSettling_facts {P : Parse.PProblem} {mt : TransMeta}
    {M : SettlingModel n} {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hf : faithfulSettling P mt M = true) :
    mt.lam.n ≠ 0 ∧ M.dtQ ≠ 0
    ∧ P.R.stateVars.length ≤ n
    ∧ P.R.modes.length = M.modes.length
    ∧ ∀ q pm m, P.R.modes[q]? = some pm → M.modes[q]? = some m →
        modeCore P.R.stateVars mt.scales (qDiv (qDiv εR mt.lam) (qOfInt M.dtQ))
          (P.R.modes.map (·.name)) q pm m M.env = true
        ∧ bandSettling P.R.stateVars mt.scales pm m = true := by
  unfold faithfulSettling faithfulFrame at hf
  rw [hεR] at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨hlam, hdt⟩, hle⟩, hsc⟩, hml⟩, hall⟩ := hf
  refine ⟨by unfold qIsZero at hlam; simpa using hlam, by simpa using hdt,
    by simpa using hle,
    by first
      | exact of_decide_eq_true hml
      | exact Nat.eq_of_beq_eq_true hml
      | simpa using hml, ?_⟩
  intro q pm m hpm hm
  have hq : q < P.R.modes.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hpm
    exact h
  have hfact := List.all_eq_true.mp hall q (List.mem_range.mpr hq)
  rw [hpm, hm] at hfact
  simpa [Bool.and_eq_true] using hfact

/-! ### The real-side domain and guard map -/

/-- Real-side evolution domain of a parsed mode. -/
noncomputable def realEnvOf (vs : List String) (n : ℕ) (pm : Parse.PMode) :
    Formula (Var n) :=
  match boundsOfForm pm.evolve with
  | some eb => envFormulaR vs n eb
  | none => Formula.tt

/-- Real-side guard map: per mode, the parsed evolve bounds ∧ the parsed guard band. -/
noncomputable def realGdOf (P : Parse.PProblem) (M : SettlingModel n) :
    ℕ → Formula (Var n) :=
  fun q => match P.R.modes[q]?, M.modes[q]? with
    | some pm, some m =>
        match boundsOfForm pm.evolve, boundsOfForm pm.guard with
        | some eb, some gb =>
            Formula.and (envFormulaR P.R.stateVars n eb)
              (bandFormulaR m.gcoord
                (boundOf gb (P.R.stateVars.getD m.gcoord.val "")).1
                (boundOf gb (P.R.stateVars.getD m.gcoord.val "")).2)
        | _, _ => Formula.tt
    | _, _ => Formula.tt

/-- **The `hGd` discharger**: the real guard map corresponds to the scaled one at every
mode index. -/
theorem realGdOf_sat (P : Parse.PProblem) (mt : TransMeta) (M : SettlingModel n)
    {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hf : faithfulSettling P mt M = true)
    (hlen : P.R.stateVars.length = n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf mt.scales j) :
    ∀ (q' : ℕ) (ν : DL.State (Var n)),
      Formula.sat (realGdOf P M q') ν
        ↔ Formula.sat (M.GdOf q') (scaleState (sigmaOf mt.scales) ν) := by
  obtain ⟨-, -, -, hml, hmode⟩ := faithfulSettling_facts hεR hf
  intro q' ν
  rcases hpm : P.R.modes[q']? with _ | pm
  · have hmnone : M.modes[q']? = none := by
      rw [List.getElem?_eq_none_iff] at hpm ⊢
      omega
    unfold realGdOf SettlingModel.GdOf
    rw [hpm, hmnone]
    simp [Formula.sat]
  · rcases hm : M.modes[q']? with _ | m
    · exfalso
      rw [List.getElem?_eq_none_iff] at hm
      have : q' < P.R.modes.length := by
        obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hpm
        exact h
      omega
    obtain ⟨hmc, hbsb⟩ := hmode q' pm m hpm hm
    obtain ⟨eb, heb, hef⟩ := modeCore_env_facts hlen hmc
    obtain ⟨gb, hgb, hblo, hbhi⟩ := bandSettling_facts hbsb
    have hgdred : realGdOf P M q'
        = Formula.and (envFormulaR P.R.stateVars n eb)
            (bandFormulaR m.gcoord
              (boundOf gb (P.R.stateVars.getD m.gcoord.val "")).1
              (boundOf gb (P.R.stateVars.getD m.gcoord.val "")).2) := by
      unfold realGdOf
      simp only [hpm, hm, heb, hgb]
    have hGdred : M.GdOf q'
        = Formula.and M.envF (bandDom m.gcoord (m.glo : ℝ) (m.ghi : ℝ)) := by
      unfold SettlingModel.GdOf
      rw [hm]
    rw [hgdred, hGdred]
    simp only [Formula.sat]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(envFormulaR_sat M (boundsOfForm_pos heb) hσd hσv hef ν).mp h1,
        (bandSettling_sat (boundsOfForm_pos hgb) m hσd hσv ⟨hblo, hbhi⟩ ν).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(envFormulaR_sat M (boundsOfForm_pos heb) hσd hσv hef ν).mpr h1,
        (bandSettling_sat (boundsOfForm_pos hgb) m hσd hσv ⟨hblo, hbhi⟩ ν).mpr h2⟩

/-! ### The per-mode field dispatch -/

/-- **The `hfield` discharger**: every coordinate's scaled field pushes forward to the
real parsed field. -/
theorem fieldOf_bridge {vs : List String} {σq : List QF} {uq : QF}
    (hnod : vs.Nodup) (hlen : vs.length = n)
    (hσd : ∀ j, j < n → (σq.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf σq j) (hud : uq.pos)
    (pm : Parse.PMode) (m : SettlingMode n)
    (hode : ∀ i : Fin n, ∃ o p,
      pm.odes.find? (fun o => o.1 == vs.getD i.val "") = some o
      ∧ exprPoly o.2 = some p
      ∧ shapeFaithful vs σq uq i.val (m.shapes i) p = true)
    (hidx : ∀ i : Fin n, shapeIdxOkB i (m.shapes i) = true) :
    ∀ (i : Fin n) (ν : DL.State (Var n)),
      Term.eval (m.fieldOf i) (scaleState (sigmaOf σq) ν)
        = sigmaOf σq i * (uq.val * Term.eval (realFieldOf vs pm n i) ν) := by
  intro i ν
  obtain ⟨o, p, hfind, hep, hsf⟩ := hode i
  have hreal : realFieldOf vs pm n i = polyToTerm vs n p := by
    unfold realFieldOf
    simp only [hfind, hep]
  rw [hreal]
  have hp := exprPoly_inv hep
  have hidxi := hidx i
  show Term.eval ((m.shapes i).field i) (scaleState (sigmaOf σq) ν) = _
  cases hsh : m.shapes i with
  | frozen =>
      rw [hsh] at hsf
      exact bridge_frozen i hsf ν
  | constRate c =>
      rw [hsh] at hsf
      exact bridge_constRate hσd hud i hp hsf ν
  | contract k c =>
      rw [hsh] at hsf
      exact bridge_contract hnod hlen hσd hud i hp hsf ν
  | contractQ kn kd c =>
      rw [hsh] at hsf
      exact bridge_contractQ hnod hlen hσd hud i hp hsf ν
  | driven j =>
      rw [hsh] at hsf
      exact bridge_driven hnod hlen hσd hud i hp hsf ν
  | drivenDamp j ds =>
      rw [hsh] at hsf
      rw [hsh] at hidxi
      unfold shapeIdxOkB at hidxi
      simp only [Bool.and_eq_true] at hidxi
      exact bridge_drivenDamp hnod hlen hσd hud i
        (fun d hd => by
          have := List.all_eq_true.mp hidxi.1 d hd
          simpa using this)
        (of_decide_eq_true hidxi.2) hp hsf ν
  | riccati b a =>
      rw [hsh] at hsf
      exact bridge_riccati hnod hlen hσd hσv hud i hp hsf ν
  | pairSym j c h =>
      rw [hsh] at hsf
      rw [hsh] at hidxi
      unfold shapeIdxOkB at hidxi
      exact bridge_pairSym hnod hlen hσd hud i (by simpa using hidxi) hp hsf ν
  | chase j k =>
      rw [hsh] at hsf
      rw [hsh] at hidxi
      unfold shapeIdxOkB at hidxi
      exact bridge_chase hnod hlen hσd hud i (by simpa using hidxi) hp hsf ν

/-! ### The assembly -/

/-- **The Faithful-soundness bridge, assembled.** A `faithfulSettling` verdict upgrades
the scaled model's per-mode settling certificate to the REAL parsed model — real fields
(`realFieldOf`), real evolution domain (`realEnvOf`), real guard map (`realGdOf`) — at
the real duration `u·dts`, where `u = (ε_R/λ)/dtQ` is the transcription's time unit.
Residual side conditions are per-benchmark decidables: distinct variable names,
full width, positive scales, positive time unit, and shape index hygiene. -/
theorem faithfulSettling_rescale (P : Parse.PProblem) (mt : TransMeta)
    (M : SettlingModel n) {εR : QF} (hεR : parseQ P.R.epsilon = some εR)
    (hf : faithfulSettling P mt M = true)
    (hnod : P.R.stateVars.Nodup) (hlen : P.R.stateVars.length = n)
    (hσd : ∀ j, j < n → (mt.scales.getD j (qOfInt 0)).pos)
    (hσv : ∀ j : Fin n, 0 < sigmaOf mt.scales j)
    (huv : 0 < (qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).val)
    (hidx : ∀ m ∈ M.modes, ∀ i : Fin n, shapeIdxOkB i (m.shapes i) = true)
    {q : ℕ} {pm : Parse.PMode} {m : SettlingMode n}
    (hpm : P.R.modes[q]? = some pm) (hm : M.modes[q]? = some m)
    (dts : ℝ)
    (hB : GuardSettlingB M.graph M.GdOf m.fieldOf (Term.const 1) M.envF dts q) :
    GuardSettlingB M.graph (realGdOf P M) (realFieldOf P.R.stateVars pm n)
      (Term.const 1) (realEnvOf P.R.stateVars n pm)
      ((qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).val * dts) q := by
  obtain ⟨hlam, hdt, -, hml, hmode⟩ := faithfulSettling_facts hεR hf
  have hud : (qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).pos :=
    qDiv_pos (qDiv_pos (parseQ_pos hεR) hlam) (by simpa [qOfInt] using hdt)
  obtain ⟨hmc, hbsb⟩ := hmode q pm m hpm hm
  obtain ⟨eb, heb, hef⟩ := modeCore_env_facts hlen hmc
  have hmm : m ∈ M.modes := by
    obtain ⟨h, hEq⟩ := List.getElem?_eq_some_iff.mp hm
    exact hEq ▸ List.getElem_mem h
  refine GuardSettlingB_rescale M.graph M.GdOf (realGdOf P M) m.fieldOf
    (realFieldOf P.R.stateVars pm n) M.envF (realEnvOf P.R.stateVars n pm)
    (sigmaOf mt.scales) (qDiv (qDiv εR mt.lam) (qOfInt M.dtQ)).val dts q
    (fun i => ne_of_gt (hσv i)) huv
    (fieldOf_bridge hnod hlen hσd hσv hud pm m
      (modeCore_ode_facts hlen hmc) (hidx m hmm))
    (realGdOf_sat P mt M hεR hf hlen hσd hσv)
    ?_ hB
  intro ν
  have hered : realEnvOf P.R.stateVars n pm = envFormulaR P.R.stateVars n eb := by
    unfold realEnvOf
    simp only [heb]
  rw [hered]
  exact envFormulaR_sat M (boundsOfForm_pos heb) hσd hσv hef ν

end RelCertifier
