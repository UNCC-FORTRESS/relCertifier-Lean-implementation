/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Kernel-fast exact rationals (`QF`) and the strict decimal parser

Split out of `Faithful.lean` so that the trusted lowering (`Run.parseRat` and through it
`lowerE` on numerals) can share the same kernel-reducing arithmetic. Mathlib's ℚ
numeral/field instance chains do not kernel-reduce under `rfl`; `QF` computes with raw
`ℤ × ℤ` fractions (denominator kept positive, NO normalization — every comparison is a
cross-multiplication), and all string processing is STRUCTURAL recursion over
`String.data` (well-founded–recursive core functions do not kernel-reduce).
-/
import RelCertifier.Parse
import Mathlib.Data.Int.Basic

namespace RelCertifier

/-! ## Kernel-fast exact rationals (`QF`) and polynomial normal form over the IR

Mathlib's ℚ numeral/field instance chains do not kernel-reduce under `rfl`, so `Faithful`
computes with raw `ℤ × ℤ` fractions (denominator kept positive, NO normalization — every
comparison is a cross-multiplication). All operations are plain `Int` arithmetic, which
the kernel evaluates fast on binary representations. -/

/-- Unnormalized exact rational: numerator, positive denominator. -/
structure QF where
  n : ℤ
  d : ℤ
  deriving Repr, DecidableEq

def qMk (n d : ℤ) : QF := if d < 0 then ⟨-n, -d⟩ else ⟨n, d⟩
def qOfInt (n : ℤ) : QF := ⟨n, 1⟩
def qAdd (a b : QF) : QF := ⟨a.n * b.d + b.n * a.d, a.d * b.d⟩
def qNeg (a : QF) : QF := ⟨-a.n, a.d⟩
def qSub (a b : QF) : QF := qAdd a (qNeg b)
def qMul (a b : QF) : QF := ⟨a.n * b.n, a.d * b.d⟩
def qDiv (a b : QF) : QF := qMk (a.n * b.d) (a.d * b.n)
def qEq (a b : QF) : Bool := a.n * b.d == b.n * a.d
def qLt (a b : QF) : Bool := a.n * b.d < b.n * a.d
def qIsZero (a : QF) : Bool := a.n == 0
def qPow10 (k : Nat) : QF := ⟨1, (10 : ℤ) ^ k⟩

/-- Digits of a char list → `Nat` (structural; `none` on empty or non-digit).
All string processing in this file is by STRUCTURAL recursion over `String.data`, because
well-founded–recursive core functions (`String.splitOn` …) do not kernel-reduce under
`rfl`. -/
def digitsToNat : List Char → Option Nat
  | [] => none
  | cs => go cs 0
where
  go : List Char → Nat → Option Nat
    | [], acc => some acc
    | c :: cs, acc =>
        if c.isDigit then go cs (acc * 10 + (c.toNat - '0'.toNat))
        else none

/-- Decimal numeral → `QF` (strict: optional `-`, digits, at most one point). -/
def parseQChars : List Char → Option QF
  | '-' :: cs => (parseQPos cs).map qNeg
  | cs => parseQPos cs
where
  splitDot : List Char → List Char × Option (List Char)
    | [] => ([], none)
    | '.' :: cs => ([], some cs)
    | c :: cs =>
        let (w, f) := splitDot cs
        (c :: w, f)
  parseQPos (cs : List Char) : Option QF :=
    match splitDot cs with
    | (w, none) => (digitsToNat w).map (fun n => qOfInt n)
    | (w, some f) => do
        let n ← digitsToNat w
        let m ← digitsToNat f
        return qAdd (qOfInt n) (qMul (qOfInt m) (qPow10 f.length))

def parseQ (s : String) : Option QF := parseQChars s.data


end RelCertifier
