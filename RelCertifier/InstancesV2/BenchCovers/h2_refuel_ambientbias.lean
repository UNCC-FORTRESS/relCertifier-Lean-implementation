/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `h2_refuel_ambientbias` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py h2_refuel_ambientbias`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `h2_refuel_ambientbias` (emitted, suite_v2, widened cut channel on). -/
def h2_refuel_ambientbias_coverV2 : CoverEmitE :=
  ⟨"h2_refuel_ambientbias", [], [
    ⟨"STAGE1", (1 : ℚ) / 1, 1, [⟨"STAGE1", true, true, true⟩, ⟨"STAGE2", true, true, true⟩, ⟨"STAGE3", true, true, true⟩, ⟨"TOPOFF", true, true, true⟩, ⟨"COMPLETE", true, false, false⟩], ["STAGE1", "STAGE2", "STAGE3", "TOPOFF", "COMPLETE"], [⟨"STAGE1", [0], [0], [0], 1, 1⟩, ⟨"STAGE2", [0], [0], [0], 1, 1⟩, ⟨"STAGE3", [0], [0], [0], 1, 1⟩, ⟨"TOPOFF", [0], [0], [0], 1, 1⟩, ⟨"COMPLETE", [0], [0], [0], 1, 1⟩]⟩,
    ⟨"STAGE2", (1 : ℚ) / 1, 1, [⟨"STAGE1", false, true, true⟩, ⟨"STAGE2", true, true, true⟩, ⟨"STAGE3", true, true, true⟩, ⟨"TOPOFF", true, true, true⟩, ⟨"COMPLETE", true, false, false⟩], ["STAGE2", "STAGE3", "TOPOFF", "COMPLETE"], [⟨"STAGE1", [], [0], [0], 1, 1⟩, ⟨"STAGE2", [0], [0], [0], 1, 1⟩, ⟨"STAGE3", [0], [0], [0], 1, 1⟩, ⟨"TOPOFF", [0], [0], [0], 1, 1⟩, ⟨"COMPLETE", [0], [0], [0], 1, 1⟩]⟩,
    ⟨"STAGE3", (1 : ℚ) / 1, 1, [⟨"STAGE1", true, true, true⟩, ⟨"STAGE2", false, true, true⟩, ⟨"STAGE3", true, true, true⟩, ⟨"TOPOFF", true, true, true⟩, ⟨"COMPLETE", true, false, false⟩], ["STAGE3", "TOPOFF", "COMPLETE"], [⟨"STAGE1", [0], [0], [0], 1, 1⟩, ⟨"STAGE2", [], [0], [0], 1, 1⟩, ⟨"STAGE3", [0], [0], [0], 1, 1⟩, ⟨"TOPOFF", [0], [0], [0], 1, 1⟩, ⟨"COMPLETE", [0], [0], [0], 1, 1⟩]⟩,
    ⟨"TOPOFF", (1 : ℚ) / 1, 1, [⟨"STAGE1", true, true, true⟩, ⟨"STAGE2", true, true, true⟩, ⟨"STAGE3", false, true, true⟩, ⟨"TOPOFF", true, true, true⟩, ⟨"COMPLETE", true, false, false⟩], ["STAGE3", "TOPOFF", "COMPLETE"], [⟨"STAGE1", [0], [0], [0], 1, 1⟩, ⟨"STAGE2", [0], [0], [0], 1, 1⟩, ⟨"STAGE3", [], [0], [0], 1, 1⟩, ⟨"TOPOFF", [0], [0], [0], 1, 1⟩, ⟨"COMPLETE", [0], [0], [0], 1, 1⟩]⟩,
    ⟨"COMPLETE", (1 : ℚ) / 1, 1, [⟨"STAGE1", true, true, true⟩, ⟨"STAGE2", true, true, true⟩, ⟨"STAGE3", true, true, true⟩, ⟨"TOPOFF", true, true, true⟩, ⟨"COMPLETE", true, false, false⟩], ["TOPOFF", "COMPLETE"], [⟨"STAGE1", [0], [0], [0], 1, 1⟩, ⟨"STAGE2", [0], [0], [0], 1, 1⟩, ⟨"STAGE3", [0], [0], [0], 1, 1⟩, ⟨"TOPOFF", [0], [0], [0], 1, 1⟩, ⟨"COMPLETE", [0], [0], [0], 1, 1⟩]⟩]⟩

end RelCertifier
