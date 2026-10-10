/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_rate` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py match_multi_rate`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `match_multi_rate` (emitted, suite_v2, widened cut channel on). -/
def match_multi_rate_coverV2 : CoverEmitE :=
  ⟨"match_multi_rate", [("DRIVE", "STALL")], [
    ⟨"FAST", (3 : ℚ) / 1, 3, [⟨"DRIVE", true, true, true⟩, ⟨"STALL", false, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0], [0], [0]⟩, ⟨"STALL", [], [], []⟩]⟩,
    ⟨"MEDIUM", (2 : ℚ) / 1, 2, [⟨"DRIVE", true, true, true⟩, ⟨"STALL", true, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0], [0], [0]⟩, ⟨"STALL", [0], [], []⟩]⟩,
    ⟨"SLOW", (1 : ℚ) / 1, 1, [⟨"DRIVE", true, true, true⟩, ⟨"STALL", true, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0], [0], [0]⟩, ⟨"STALL", [0], [], []⟩]⟩,
    ⟨"RESET", (1 : ℚ) / 1, 1, [⟨"DRIVE", true, true, true⟩, ⟨"STALL", false, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0], [0], [0]⟩, ⟨"STALL", [], [], []⟩]⟩]⟩

end RelCertifier
