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

theorem gp_m0_01 : Run.parseRat "-0.01" = some ((-1:ℚ)/100) := by
  have h : parseQ "-0.01" = some (⟨-1, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_125 : Run.parseRat "-0.125" = some ((-1:ℚ)/8) := by
  have h : parseQ "-0.125" = some (⟨-125, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_2 : Run.parseRat "-0.2" = some ((-1:ℚ)/5) := by
  have h : parseQ "-0.2" = some (⟨-2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_4 : Run.parseRat "-0.4" = some ((-2:ℚ)/5) := by
  have h : parseQ "-0.4" = some (⟨-4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_42 : Run.parseRat "-0.42" = some ((-21:ℚ)/50) := by
  have h : parseQ "-0.42" = some (⟨-42, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_45 : Run.parseRat "-0.45" = some ((-9:ℚ)/20) := by
  have h : parseQ "-0.45" = some (⟨-45, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_7 : Run.parseRat "-0.7" = some ((-7:ℚ)/10) := by
  have h : parseQ "-0.7" = some (⟨-7, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m0_75 : Run.parseRat "-0.75" = some ((-3:ℚ)/4) := by
  have h : parseQ "-0.75" = some (⟨-75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m10_0 : Run.parseRat "-10.0" = some (-10:ℚ) := by
  have h : parseQ "-10.0" = some (⟨-100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m2_0 : Run.parseRat "-2.0" = some (-2:ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m2_5 : Run.parseRat "-2.5" = some ((-5:ℚ)/2) := by
  have h : parseQ "-2.5" = some (⟨-25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_m4 : Run.parseRat "-4" = some (-4:ℚ) := by
  have h : parseQ "-4" = some (⟨-4, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_0625 : Run.parseRat "0.0625" = some ((1:ℚ)/16) := by
  have h : parseQ "0.0625" = some (⟨625, 10000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_07 : Run.parseRat "0.07" = some ((7:ℚ)/100) := by
  have h : parseQ "0.07" = some (⟨7, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_0775 : Run.parseRat "0.0775" = some ((31:ℚ)/400) := by
  have h : parseQ "0.0775" = some (⟨775, 10000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_08 : Run.parseRat "0.08" = some ((2:ℚ)/25) := by
  have h : parseQ "0.08" = some (⟨8, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_085 : Run.parseRat "0.085" = some ((17:ℚ)/200) := by
  have h : parseQ "0.085" = some (⟨85, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_205 : Run.parseRat "0.205" = some ((41:ℚ)/200) := by
  have h : parseQ "0.205" = some (⟨205, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_255 : Run.parseRat "0.255" = some ((51:ℚ)/200) := by
  have h : parseQ "0.255" = some (⟨255, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_355 : Run.parseRat "0.355" = some ((71:ℚ)/200) := by
  have h : parseQ "0.355" = some (⟨355, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_48 : Run.parseRat "0.48" = some ((12:ℚ)/25) := by
  have h : parseQ "0.48" = some (⟨48, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_6775 : Run.parseRat "0.6775" = some ((271:ℚ)/400) := by
  have h : parseQ "0.6775" = some (⟨6775, 10000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_72 : Run.parseRat "0.72" = some ((18:ℚ)/25) := by
  have h : parseQ "0.72" = some (⟨72, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_84 : Run.parseRat "0.84" = some ((21:ℚ)/25) := by
  have h : parseQ "0.84" = some (⟨84, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_855 : Run.parseRat "0.855" = some ((171:ℚ)/200) := by
  have h : parseQ "0.855" = some (⟨855, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_88 : Run.parseRat "0.88" = some ((22:ℚ)/25) := by
  have h : parseQ "0.88" = some (⟨88, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_0_95 : Run.parseRat "0.95" = some ((19:ℚ)/20) := by
  have h : parseQ "0.95" = some (⟨95, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_001 : Run.parseRat "1.001" = some ((1001:ℚ)/1000) := by
  have h : parseQ "1.001" = some (⟨1001, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_15 : Run.parseRat "1.15" = some ((23:ℚ)/20) := by
  have h : parseQ "1.15" = some (⟨115, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_25 : Run.parseRat "1.25" = some ((5:ℚ)/4) := by
  have h : parseQ "1.25" = some (⟨125, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_3 : Run.parseRat "1.3" = some ((13:ℚ)/10) := by
  have h : parseQ "1.3" = some (⟨13, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_62 : Run.parseRat "1.62" = some ((81:ℚ)/50) := by
  have h : parseQ "1.62" = some (⟨162, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_68 : Run.parseRat "1.68" = some ((42:ℚ)/25) := by
  have h : parseQ "1.68" = some (⟨168, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1_8 : Run.parseRat "1.8" = some ((9:ℚ)/5) := by
  have h : parseQ "1.8" = some (⟨18, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_10_0 : Run.parseRat "10.0" = some (10:ℚ) := by
  have h : parseQ "10.0" = some (⟨100, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_100_0 : Run.parseRat "100.0" = some (100:ℚ) := by
  have h : parseQ "100.0" = some (⟨1000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_1000_0 : Run.parseRat "1000.0" = some (1000:ℚ) := by
  have h : parseQ "1000.0" = some (⟨10000, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_12_0 : Run.parseRat "12.0" = some (12:ℚ) := by
  have h : parseQ "12.0" = some (⟨120, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_12_45 : Run.parseRat "12.45" = some ((249:ℚ)/20) := by
  have h : parseQ "12.45" = some (⟨1245, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_12_5 : Run.parseRat "12.5" = some ((25:ℚ)/2) := by
  have h : parseQ "12.5" = some (⟨125, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_13_0 : Run.parseRat "13.0" = some (13:ℚ) := by
  have h : parseQ "13.0" = some (⟨130, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_15_0 : Run.parseRat "15.0" = some (15:ℚ) := by
  have h : parseQ "15.0" = some (⟨150, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_15_5 : Run.parseRat "15.5" = some ((31:ℚ)/2) := by
  have h : parseQ "15.5" = some (⟨155, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_16 : Run.parseRat "16" = some (16:ℚ) := by
  have h : parseQ "16" = some (⟨16, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_16_0 : Run.parseRat "16.0" = some (16:ℚ) := by
  have h : parseQ "16.0" = some (⟨160, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_17_0 : Run.parseRat "17.0" = some (17:ℚ) := by
  have h : parseQ "17.0" = some (⟨170, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_2_1 : Run.parseRat "2.1" = some ((21:ℚ)/10) := by
  have h : parseQ "2.1" = some (⟨21, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_2_2 : Run.parseRat "2.2" = some ((11:ℚ)/5) := by
  have h : parseQ "2.2" = some (⟨22, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_2_25 : Run.parseRat "2.25" = some ((9:ℚ)/4) := by
  have h : parseQ "2.25" = some (⟨225, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_2_5 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_2_6 : Run.parseRat "2.6" = some ((13:ℚ)/5) := by
  have h : parseQ "2.6" = some (⟨26, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_20_0 : Run.parseRat "20.0" = some (20:ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_21_0 : Run.parseRat "21.0" = some (21:ℚ) := by
  have h : parseQ "21.0" = some (⟨210, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_22_0 : Run.parseRat "22.0" = some (22:ℚ) := by
  have h : parseQ "22.0" = some (⟨220, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_23_0 : Run.parseRat "23.0" = some (23:ℚ) := by
  have h : parseQ "23.0" = some (⟨230, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_24_0 : Run.parseRat "24.0" = some (24:ℚ) := by
  have h : parseQ "24.0" = some (⟨240, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_25_0 : Run.parseRat "25.0" = some (25:ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_26_0 : Run.parseRat "26.0" = some (26:ℚ) := by
  have h : parseQ "26.0" = some (⟨260, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_27_0 : Run.parseRat "27.0" = some (27:ℚ) := by
  have h : parseQ "27.0" = some (⟨270, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_28_0 : Run.parseRat "28.0" = some (28:ℚ) := by
  have h : parseQ "28.0" = some (⟨280, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_29_0 : Run.parseRat "29.0" = some (29:ℚ) := by
  have h : parseQ "29.0" = some (⟨290, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_3_0 : Run.parseRat "3.0" = some (3:ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_3_2 : Run.parseRat "3.2" = some ((16:ℚ)/5) := by
  have h : parseQ "3.2" = some (⟨32, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_3_5 : Run.parseRat "3.5" = some ((7:ℚ)/2) := by
  have h : parseQ "3.5" = some (⟨35, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_3_6 : Run.parseRat "3.6" = some ((18:ℚ)/5) := by
  have h : parseQ "3.6" = some (⟨36, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_30_0 : Run.parseRat "30.0" = some (30:ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_32_0 : Run.parseRat "32.0" = some (32:ℚ) := by
  have h : parseQ "32.0" = some (⟨320, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_33_0 : Run.parseRat "33.0" = some (33:ℚ) := by
  have h : parseQ "33.0" = some (⟨330, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_34_0 : Run.parseRat "34.0" = some (34:ℚ) := by
  have h : parseQ "34.0" = some (⟨340, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_35_0 : Run.parseRat "35.0" = some (35:ℚ) := by
  have h : parseQ "35.0" = some (⟨350, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_36_0 : Run.parseRat "36.0" = some (36:ℚ) := by
  have h : parseQ "36.0" = some (⟨360, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_4_0 : Run.parseRat "4.0" = some (4:ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_4_4 : Run.parseRat "4.4" = some ((22:ℚ)/5) := by
  have h : parseQ "4.4" = some (⟨44, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_40_0 : Run.parseRat "40.0" = some (40:ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_5_0 : Run.parseRat "5.0" = some (5:ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_5_5 : Run.parseRat "5.5" = some ((11:ℚ)/2) := by
  have h : parseQ "5.5" = some (⟨55, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_50_0 : Run.parseRat "50.0" = some (50:ℚ) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_6_0 : Run.parseRat "6.0" = some (6:ℚ) := by
  have h : parseQ "6.0" = some (⟨60, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_6_5 : Run.parseRat "6.5" = some ((13:ℚ)/2) := by
  have h : parseQ "6.5" = some (⟨65, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_60_0 : Run.parseRat "60.0" = some (60:ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_7_45 : Run.parseRat "7.45" = some ((149:ℚ)/20) := by
  have h : parseQ "7.45" = some (⟨745, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_8 : Run.parseRat "8" = some (8:ℚ) := by
  have h : parseQ "8" = some (⟨8, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_8_0 : Run.parseRat "8.0" = some (8:ℚ) := by
  have h : parseQ "8.0" = some (⟨80, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_8_45 : Run.parseRat "8.45" = some ((169:ℚ)/20) := by
  have h : parseQ "8.45" = some (⟨845, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_80_0 : Run.parseRat "80.0" = some (80:ℚ) := by
  have h : parseQ "80.0" = some (⟨800, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_9_0 : Run.parseRat "9.0" = some (9:ℚ) := by
  have h : parseQ "9.0" = some (⟨90, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_9_524 : Run.parseRat "9.524" = some ((2381:ℚ)/250) := by
  have h : parseQ "9.524" = some (⟨9524, 1000⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_90_0 : Run.parseRat "90.0" = some (90:ℚ) := by
  have h : parseQ "90.0" = some (⟨900, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

theorem gp_99_0 : Run.parseRat "99.0" = some (99:ℚ) := by
  have h : parseQ "99.0" = some (⟨990, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
  try norm_num

end GPins
end RelCertifier
