/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `engine_start_highidle` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py engine_start_highidle`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `engine_start_highidle` (emitted, suite_v2, widened cut channel on). -/
def engine_start_highidle_coverV2 : CoverEmitE :=
  ⟨"engine_start_highidle", [], [
    ⟨"STARTER", (1 : ℚ) / 1, 1, [⟨"STARTER", true, false, false⟩, ⟨"STARTER_LOW", false, false, false⟩, ⟨"LIGHTOFF", true, true, true⟩, ⟨"SELF", true, true, true⟩, ⟨"IDLE", true, false, false⟩, ⟨"ABORT", false, false, false⟩], ["STARTER", "LIGHTOFF", "SELF", "IDLE"], [⟨"STARTER", [0, 1, 2, 3], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"STARTER_LOW", [1, 2, 3], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"LIGHTOFF", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"SELF", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"IDLE", [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"ABORT", [1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩]⟩,
    ⟨"STARTER_LOW", (1 : ℚ) / 1, 1, [⟨"STARTER", true, true, false⟩, ⟨"STARTER_LOW", true, false, false⟩, ⟨"LIGHTOFF", true, true, true⟩, ⟨"SELF", true, true, true⟩, ⟨"IDLE", true, false, false⟩, ⟨"ABORT", false, false, false⟩], ["STARTER_LOW", "LIGHTOFF", "SELF", "IDLE"], [⟨"STARTER", [0, 1, 2, 3], [0, 2, 3, 1], [0, 2, 3], 1, 1⟩, ⟨"STARTER_LOW", [0, 1, 2, 3], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"LIGHTOFF", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"SELF", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"IDLE", [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"ABORT", [1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩]⟩,
    ⟨"LIGHTOFF", (1 : ℚ) / 1, 1, [⟨"STARTER", false, true, true⟩, ⟨"STARTER_LOW", false, true, true⟩, ⟨"LIGHTOFF", true, true, true⟩, ⟨"SELF", true, true, true⟩, ⟨"IDLE", true, false, false⟩, ⟨"ABORT", false, false, false⟩], ["LIGHTOFF", "SELF", "IDLE"], [⟨"STARTER", [], [0], [0], 1, 1⟩, ⟨"STARTER_LOW", [], [0], [0], 1, 1⟩, ⟨"LIGHTOFF", [0], [0], [0], 1, 1⟩, ⟨"SELF", [0], [0], [0], 1, 1⟩, ⟨"IDLE", [0], [], [], 1, 1⟩, ⟨"ABORT", [], [0], [0], 1, 1⟩]⟩,
    ⟨"SELF", (1 : ℚ) / 1, 1, [⟨"STARTER", true, true, true⟩, ⟨"STARTER_LOW", true, true, true⟩, ⟨"LIGHTOFF", false, true, true⟩, ⟨"SELF", true, true, true⟩, ⟨"IDLE", true, false, false⟩, ⟨"ABORT", true, false, false⟩], ["LIGHTOFF", "SELF", "IDLE"], [⟨"STARTER", [0], [0], [0], 1, 1⟩, ⟨"STARTER_LOW", [0], [0], [0], 1, 1⟩, ⟨"LIGHTOFF", [], [0], [0], 1, 1⟩, ⟨"SELF", [0], [0], [0], 1, 1⟩, ⟨"IDLE", [0], [], [], 1, 1⟩, ⟨"ABORT", [0], [0], [0], 1, 1⟩]⟩,
    ⟨"IDLE", (1 : ℚ) / 1, 1, [⟨"STARTER", true, true, true⟩, ⟨"STARTER_LOW", true, true, true⟩, ⟨"LIGHTOFF", true, true, true⟩, ⟨"SELF", false, true, true⟩, ⟨"IDLE", true, false, false⟩, ⟨"ABORT", true, false, false⟩], ["SELF", "IDLE"], [⟨"STARTER", [0], [0], [0], 1, 1⟩, ⟨"STARTER_LOW", [0], [0], [0], 1, 1⟩, ⟨"LIGHTOFF", [0], [0], [0], 1, 1⟩, ⟨"SELF", [], [0], [0], 1, 1⟩, ⟨"IDLE", [0], [], [], 1, 1⟩, ⟨"ABORT", [0], [0], [0], 1, 1⟩]⟩,
    ⟨"ABORT", (1 : ℚ) / 1, 1, [⟨"STARTER", true, true, true⟩, ⟨"STARTER_LOW", true, true, true⟩, ⟨"LIGHTOFF", true, true, true⟩, ⟨"SELF", true, true, true⟩, ⟨"IDLE", true, false, false⟩, ⟨"ABORT", true, false, false⟩], ["STARTER", "STARTER_LOW", "LIGHTOFF", "SELF", "IDLE", "ABORT"], [⟨"STARTER", [0], [0], [0], 1, 1⟩, ⟨"STARTER_LOW", [0], [0], [0], 1, 1⟩, ⟨"LIGHTOFF", [0], [0], [0], 1, 1⟩, ⟨"SELF", [0], [0], [0], 1, 1⟩, ⟨"IDLE", [0], [], [], 1, 1⟩, ⟨"ABORT", [0], [0], [0], 1, 1⟩]⟩]⟩

end RelCertifier
