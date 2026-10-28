/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_nahs25_salt_tank` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_nahs25_salt_tank`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `lit_nahs25_salt_tank` (emitted, suite_v2, widened cut channel on). -/
def lit_nahs25_salt_tank_coverV2 : CoverEmitE :=
  ⟨"lit_nahs25_salt_tank", [], [
    ⟨"On", (1 : ℚ) / 1, 1, [⟨"On", true, false, false⟩, ⟨"Off", true, true, true⟩], ["On"], [⟨"On", [0, 1, 2, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"Off", [1, 2, 3, 0], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩]⟩,
    ⟨"Off", (1 : ℚ) / 1, 1, [⟨"On", true, false, false⟩, ⟨"Off", true, true, true⟩], ["On"], [⟨"On", [0, 1, 2, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"Off", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
