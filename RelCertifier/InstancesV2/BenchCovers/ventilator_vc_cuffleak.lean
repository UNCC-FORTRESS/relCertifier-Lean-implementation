/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `ventilator_vc_cuffleak` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py ventilator_vc_cuffleak`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `ventilator_vc_cuffleak` (emitted, suite_v2, widened cut channel on). -/
def ventilator_vc_cuffleak_coverV2 : CoverEmitE :=
  ⟨"ventilator_vc_cuffleak", [], [
    ⟨"INSP", (1 : ℚ) / 1, 1, [⟨"INSP", true, false, false⟩, ⟨"EXP", false, false, false⟩], ["INSP"], [⟨"INSP", [0, 1, 2, 3], [0, 2], [0, 2], 1, 1⟩, ⟨"EXP", [0, 1], [0], [0], 1, 1⟩]⟩,
    ⟨"EXP", (1 : ℚ) / 1, 1, [⟨"INSP", false, false, false⟩, ⟨"EXP", true, false, false⟩], ["EXP"], [⟨"INSP", [0, 1], [0, 2], [0, 2], 1, 1⟩, ⟨"EXP", [0, 1, 2, 3], [0], [0], 1, 1⟩]⟩]⟩

end RelCertifier
