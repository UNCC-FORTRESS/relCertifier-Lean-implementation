/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `autoclave_liquid_steambank` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py autoclave_liquid_steambank`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `autoclave_liquid_steambank` (emitted, suite_v2, widened cut channel on). -/
def autoclave_liquid_steambank_coverV2 : CoverEmitE :=
  ⟨"autoclave_liquid_steambank", [], [
    ⟨"HEAT", (3 : ℚ) / 4, 1, [⟨"HEAT", true, false, false⟩, ⟨"EQUIL", false, true, false⟩, ⟨"EXPOSE", false, true, false⟩, ⟨"EXHAUST", false, false, false⟩], ["HEAT"], [⟨"HEAT", [0, 1, 2, 3, 6, 7, 4, 5], [0, 2, 3], [0, 2, 3], 3, 4⟩, ⟨"EQUIL", [1, 2, 3, 6, 7, 5], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3], 3, 4⟩, ⟨"EXPOSE", [1, 2, 6, 7, 5], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2], 3, 4⟩, ⟨"EXHAUST", [2, 3, 6], [2, 3, 4, 5, 6, 7, 0, 1], [2, 3], 3, 4⟩]⟩,
    ⟨"EQUIL", (1 : ℚ) / 1, 1, [⟨"HEAT", false, false, false⟩, ⟨"EQUIL", true, false, false⟩, ⟨"EXPOSE", false, false, false⟩, ⟨"EXHAUST", false, false, false⟩], ["EQUIL"], [⟨"HEAT", [0, 2, 3, 4, 6, 7], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"EQUIL", [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"EXPOSE", [0, 1, 2, 4, 5, 6, 7], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"EXHAUST", [1, 2, 3, 5, 6], [2, 3, 4, 5, 6, 7, 0, 1], [2, 3], 1, 1⟩]⟩,
    ⟨"EXPOSE", (1 : ℚ) / 1, 1, [⟨"HEAT", false, false, false⟩, ⟨"EQUIL", false, true, false⟩, ⟨"EXPOSE", true, false, false⟩, ⟨"EXHAUST", false, false, false⟩], ["EQUIL", "EXPOSE"], [⟨"HEAT", [0, 3], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"EQUIL", [0, 1, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"EXPOSE", [0, 1, 2, 3], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"EXHAUST", [1, 3], [2, 3, 0, 1], [2, 3], 1, 1⟩]⟩,
    ⟨"EXHAUST", (1 : ℚ) / 1, 1, [⟨"HEAT", false, false, false⟩, ⟨"EQUIL", false, true, true⟩, ⟨"EXPOSE", false, false, false⟩, ⟨"EXHAUST", true, false, false⟩], ["EXHAUST"], [⟨"HEAT", [2, 3], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"EQUIL", [0, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"EXPOSE", [0, 2], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"EXHAUST", [0, 1, 2, 3], [2, 3], [2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
