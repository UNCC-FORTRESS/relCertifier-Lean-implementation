/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `molding_pack_checkring` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py molding_pack_checkring`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `molding_pack_checkring` (emitted, suite_v2, widened cut channel on). -/
def molding_pack_checkring_coverV2 : CoverEmitE :=
  ⟨"molding_pack_checkring", [], [
    ⟨"HOLD", (1 : ℚ) / 1, 1, [⟨"HOLD", true, false, false⟩, ⟨"COOL", false, false, false⟩], ["HOLD"], [⟨"HOLD", [0, 1, 2, 4, 6, 3, 5], [0], [0], 1, 1⟩, ⟨"COOL", [0, 1, 6, 3], [0, 3, 5, 6], [0, 3, 5, 6], 1, 1⟩]⟩,
    ⟨"COOL", (1 : ℚ) / 1, 1, [⟨"HOLD", false, false, false⟩, ⟨"COOL", true, false, false⟩], ["COOL"], [⟨"HOLD", [0, 1, 4], [0], [0], 1, 1⟩, ⟨"COOL", [0, 1, 2, 3, 4], [0, 3, 4], [0, 3, 4], 1, 1⟩]⟩]⟩

end RelCertifier
