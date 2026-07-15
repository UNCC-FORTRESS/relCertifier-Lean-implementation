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

end RelCertifier
