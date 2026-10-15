/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_twospeed` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1 RELCERT_PROGRESS=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py watertank_twospeed`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `watertank_twospeed` (emitted, suite_v2, widened cut channel on). -/
def watertank_twospeed_coverV2 : CoverEmitE :=
  ⟨"watertank_twospeed", [], [
    ⟨"Low", (31 : ℚ) / 10, 4, [⟨"Fast", true, false, false⟩, ⟨"Slow", true, false, false⟩], ["Fast", "Slow"], [⟨"Fast", [0, 1], [0], [0], 1, 1⟩, ⟨"Slow", [0, 1], [], [], 31, 10⟩]⟩]⟩

end RelCertifier
