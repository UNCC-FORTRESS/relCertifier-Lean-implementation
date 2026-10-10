/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Parse pins shared by the guarded instances

`Run.parseRat` of the numerals the benchmark files write, each checked by `decide` on the
parser and normalized. Used by the guarded instance files to evaluate lowered guards and
fields by `simp`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.Run

namespace RelCertifier
namespace GPins

open Parse

theorem gp_0 : Run.parseRat "0" = some (0:ℚ) := by
  have h : parseQ "0" = some (⟨0, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_0 : Run.parseRat "0.0" = some (0:ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_1 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_15 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_2 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_25 : Run.parseRat "0.25" = some ((1:ℚ)/4) := by
  have h : parseQ "0.25" = some (⟨25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_3 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_30 : Run.parseRat "0.30" = some ((3:ℚ)/10) := by
  have h : parseQ "0.30" = some (⟨30, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_35 : Run.parseRat "0.35" = some ((7:ℚ)/20) := by
  have h : parseQ "0.35" = some (⟨35, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_4 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_5 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_50 : Run.parseRat "0.50" = some ((1:ℚ)/2) := by
  have h : parseQ "0.50" = some (⟨50, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_6 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_65 : Run.parseRat "0.65" = some ((13:ℚ)/20) := by
  have h : parseQ "0.65" = some (⟨65, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_7 : Run.parseRat "0.7" = some ((7:ℚ)/10) := by
  have h : parseQ "0.7" = some (⟨7, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_75 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_8 : Run.parseRat "0.8" = some ((4:ℚ)/5) := by
  have h : parseQ "0.8" = some (⟨8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_9 : Run.parseRat "0.9" = some ((9:ℚ)/10) := by
  have h : parseQ "0.9" = some (⟨9, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1 : Run.parseRat "1" = some (1:ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_0 : Run.parseRat "1.0" = some (1:ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_1 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_2 : Run.parseRat "1.2" = some ((6:ℚ)/5) := by
  have h : parseQ "1.2" = some (⟨12, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_4 : Run.parseRat "1.4" = some ((7:ℚ)/5) := by
  have h : parseQ "1.4" = some (⟨14, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_5 : Run.parseRat "1.5" = some ((3:ℚ)/2) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_6 : Run.parseRat "1.6" = some ((8:ℚ)/5) := by
  have h : parseQ "1.6" = some (⟨16, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_2 : Run.parseRat "2" = some (2:ℚ) := by
  have h : parseQ "2" = some (⟨2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_2_0 : Run.parseRat "2.0" = some (2:ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_3 : Run.parseRat "3" = some (3:ℚ) := by
  have h : parseQ "3" = some (⟨3, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_4 : Run.parseRat "4" = some (4:ℚ) := by
  have h : parseQ "4" = some (⟨4, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_5 : Run.parseRat "5" = some (5:ℚ) := by
  have h : parseQ "5" = some (⟨5, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_10 : Run.parseRat "10" = some (10:ℚ) := by
  have h : parseQ "10" = some (⟨10, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_5 : Run.parseRat "-0.5" = some ((-1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_25 : Run.parseRat "-0.25" = some ((-1:ℚ)/4) := by
  have h : parseQ "-0.25" = some (⟨-25, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m1 : Run.parseRat "-1" = some (-1:ℚ) := by
  have h : parseQ "-1" = some (⟨-1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m1_0 : Run.parseRat "-1.0" = some (-1:ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m2 : Run.parseRat "-2" = some (-2:ℚ) := by
  have h : parseQ "-2" = some (⟨-2, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_3 : Run.parseRat "-0.3" = some ((-3:ℚ)/10) := by
  have h : parseQ "-0.3" = some (⟨-3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_6 : Run.parseRat "-0.6" = some ((-3:ℚ)/5) := by
  have h : parseQ "-0.6" = some (⟨-6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_125 : Run.parseRat "0.125" = some ((1:ℚ)/8) := by
  have h : parseQ "0.125" = some (⟨125, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_125 : Run.parseRat "1.125" = some ((9:ℚ)/8) := by
  have h : parseQ "1.125" = some (⟨1125, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_156 : Run.parseRat "0.156" = some ((39:ℚ)/250) := by
  have h : parseQ "0.156" = some (⟨156, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_33 : Run.parseRat "0.33" = some ((33:ℚ)/100) := by
  have h : parseQ "0.33" = some (⟨33, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_899_95 : Run.parseRat "899.95" = some ((17999:ℚ)/20) := by
  have h : parseQ "899.95" = some (⟨89995, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m1_5 : Run.parseRat "-1.5" = some ((-3:ℚ)/2) := by
  have h : parseQ "-1.5" = some (⟨-15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_52 : Run.parseRat "1.52" = some ((38:ℚ)/25) := by
  have h : parseQ "1.52" = some (⟨152, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m1_52 : Run.parseRat "-1.52" = some ((-38:ℚ)/25) := by
  have h : parseQ "-1.52" = some (⟨-152, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m3_04 : Run.parseRat "-3.04" = some ((-76:ℚ)/25) := by
  have h : parseQ "-3.04" = some (⟨-304, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_3_04 : Run.parseRat "3.04" = some ((76:ℚ)/25) := by
  have h : parseQ "3.04" = some (⟨304, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_8 : Run.parseRat "-0.8" = some ((-4:ℚ)/5) := by
  have h : parseQ "-0.8" = some (⟨-8, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_05 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_45 : Run.parseRat "0.45" = some ((9:ℚ)/20) := by
  have h : parseQ "0.45" = some (⟨45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_55 : Run.parseRat "0.55" = some ((11:ℚ)/20) := by
  have h : parseQ "0.55" = some (⟨55, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_06 : Run.parseRat "0.06" = some ((3:ℚ)/50) := by
  have h : parseQ "0.06" = some (⟨6, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

end GPins
end RelCertifier
