/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hold_reposition_strict` (prelanding_demo) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_prelanding_demo.py`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `hold_reposition_strict` (emitted, suite_v2, widened cut channel on). -/
def hold_reposition_strict_coverV2 : CoverEmitE :=
  ⟨"hold_reposition_strict", [], [
    ⟨"Hold", (1 : ℚ) / 1, 1, [⟨"Up", false, false, false⟩, ⟨"Hold", true, false, false⟩], ["Up", "Hold"], [⟨"Up", [0], [], [], 1, 1⟩, ⟨"Hold", [0, 1], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
