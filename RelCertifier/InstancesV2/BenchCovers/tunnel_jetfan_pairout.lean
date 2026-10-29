/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tunnel_jetfan_pairout` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py tunnel_jetfan_pairout`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `tunnel_jetfan_pairout` (emitted, suite_v2, widened cut channel on). -/
def tunnel_jetfan_pairout_coverV2 : CoverEmitE :=
  ⟨"tunnel_jetfan_pairout", [], [
    ⟨"NORMAL", (1 : ℚ) / 1, 1, [⟨"NORMAL", true, false, false⟩, ⟨"FIRE", false, false, false⟩], ["NORMAL"], [⟨"NORMAL", [0, 1, 2, 4, 6, 3, 5], [0, 6], [0, 6], 1, 1⟩, ⟨"FIRE", [0, 1, 2, 5, 6], [0, 6], [0, 6], 1, 1⟩]⟩,
    ⟨"FIRE", (1 : ℚ) / 1, 1, [⟨"NORMAL", false, false, false⟩, ⟨"FIRE", true, false, false⟩], ["FIRE"], [⟨"NORMAL", [0, 1, 3, 4], [0, 4], [0, 4], 1, 1⟩, ⟨"FIRE", [0, 1, 2, 4, 3], [0, 4], [0, 4], 1, 1⟩]⟩]⟩

end RelCertifier
