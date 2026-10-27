/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hydro_rejection_gatecal` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py hydro_rejection_gatecal`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `hydro_rejection_gatecal` (emitted, suite_v2, widened cut channel on). -/
def hydro_rejection_gatecal_coverV2 : CoverEmitE :=
  ⟨"hydro_rejection_gatecal", [], [
    ⟨"ONGRID", (1 : ℚ) / 1, 1, [⟨"ONGRID", true, false, false⟩, ⟨"REJECT", false, false, false⟩], ["ONGRID"], [⟨"ONGRID", [0, 1, 2, 3, 4, 5], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"REJECT", [0, 1, 4], [0], [0], 1, 1⟩]⟩,
    ⟨"REJECT", (1 : ℚ) / 1, 1, [⟨"ONGRID", false, false, false⟩, ⟨"REJECT", true, false, false⟩], ["REJECT"], [⟨"ONGRID", [0, 1, 5], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"REJECT", [0, 1, 4, 5, 2, 3], [0], [0], 1, 1⟩]⟩]⟩

end RelCertifier
