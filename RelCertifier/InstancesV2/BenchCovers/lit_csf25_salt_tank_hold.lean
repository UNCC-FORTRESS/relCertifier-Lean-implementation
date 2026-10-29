/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_csf25_salt_tank_hold` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_csf25_salt_tank_hold`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `lit_csf25_salt_tank_hold` (emitted, suite_v2, widened cut channel on). -/
def lit_csf25_salt_tank_hold_coverV2 : CoverEmitE :=
  ⟨"lit_csf25_salt_tank_hold", [], [
    ⟨"HoldInc", (1 : ℚ) / 3, 1, [⟨"Inc", true, false, false⟩, ⟨"Dec", false, false, false⟩], ["Inc"], [⟨"Inc", [0, 2, 1], [1, 2], [1, 2], 1, 3⟩, ⟨"Dec", [0], [0], [0], 1, 3⟩]⟩,
    ⟨"HoldDec", (1 : ℚ) / 3, 1, [⟨"Inc", false, false, false⟩, ⟨"Dec", true, false, false⟩], ["Dec"], [⟨"Inc", [0], [0], [0], 1, 3⟩, ⟨"Dec", [0, 2, 1], [1, 2], [1, 2], 1, 3⟩]⟩]⟩

end RelCertifier
