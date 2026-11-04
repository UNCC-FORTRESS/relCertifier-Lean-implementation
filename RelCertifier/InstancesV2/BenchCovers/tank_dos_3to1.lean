/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tank_dos_3to1` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, reposition certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py tank_dos_3to1`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `tank_dos_3to1` (emitted, suite_v2, implied mode-fact candidates on). -/
def tank_dos_3to1_coverV2 : CoverEmitE :=
  ⟨"tank_dos_3to1", [], [
    ⟨"P2", (1 : ℚ) / 1, 3, [⟨"P2", true, false, false⟩, ⟨"P3", true, false, false⟩, ⟨"P4", true, false, false⟩, ⟨"P5", false, false, false⟩], ["P2"], [⟨"P2", [2, 3, 0, 1], [], [], 1, 1⟩, ⟨"P3", [2, 3, 0, 1], [], [], 1, 1⟩, ⟨"P4", [2, 3, 0, 1], [], [], 1, 1⟩, ⟨"P5", [2, 3, 0], [], [], 1, 1⟩]⟩,
    ⟨"P3", (1 : ℚ) / 1, 3, [⟨"P2", false, false, false⟩, ⟨"P3", true, false, false⟩, ⟨"P4", true, false, false⟩, ⟨"P5", true, false, false⟩], ["P3"], [⟨"P2", [2, 3, 1], [], [], 1, 1⟩, ⟨"P3", [2, 3, 0, 1], [], [], 1, 1⟩, ⟨"P4", [2, 3, 0, 1], [], [], 1, 1⟩, ⟨"P5", [2, 3, 0, 1], [], [], 1, 1⟩]⟩,
    ⟨"P4", (1 : ℚ) / 1, 3, [⟨"P2", false, false, false⟩, ⟨"P3", false, false, false⟩, ⟨"P4", true, false, false⟩, ⟨"P5", true, false, false⟩], ["P4"], [⟨"P2", [2, 3, 1], [], [], 1, 1⟩, ⟨"P3", [2, 3, 1], [], [], 1, 1⟩, ⟨"P4", [2, 3, 0, 1], [], [], 1, 1⟩, ⟨"P5", [1, 2, 3, 0], [], [], 1, 1⟩]⟩,
    ⟨"P5", (1 : ℚ) / 1, 3, [⟨"P2", false, false, false⟩, ⟨"P3", false, false, false⟩, ⟨"P4", false, false, false⟩, ⟨"P5", true, false, false⟩], ["P5"], [⟨"P2", [2, 3, 1], [], [], 1, 1⟩, ⟨"P3", [2, 3, 1], [], [], 1, 1⟩, ⟨"P4", [1, 2, 3], [], [], 1, 1⟩, ⟨"P5", [1, 2, 3, 0], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
