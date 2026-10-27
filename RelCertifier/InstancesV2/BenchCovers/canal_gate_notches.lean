/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `canal_gate_notches` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py canal_gate_notches`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `canal_gate_notches` (emitted, suite_v2, widened cut channel on). -/
def canal_gate_notches_coverV2 : CoverEmitE :=
  ⟨"canal_gate_notches", [], [
    ⟨"RAISE", (1 : ℚ) / 1, 1, [⟨"N100", true, false, false⟩, ⟨"N75", false, false, false⟩, ⟨"N50", false, false, false⟩, ⟨"N25", false, false, false⟩], ["N100", "N75", "N50"], [⟨"N100", [0, 1], [0], [0], 1, 1⟩, ⟨"N75", [1], [], [], 1, 1⟩, ⟨"N50", [1], [], [], 1, 1⟩, ⟨"N25", [1], [1], [1], 1, 1⟩]⟩,
    ⟨"HOLD", (1 : ℚ) / 1, 1, [⟨"N100", false, false, false⟩, ⟨"N75", true, false, false⟩, ⟨"N50", true, false, false⟩, ⟨"N25", false, false, false⟩], ["N100", "N75", "N50", "N25"], [⟨"N100", [0], [0], [0], 1, 1⟩, ⟨"N75", [0, 1], [], [], 1, 1⟩, ⟨"N50", [0, 1], [], [], 1, 1⟩, ⟨"N25", [1], [1], [1], 1, 1⟩]⟩,
    ⟨"LOWER", (1 : ℚ) / 1, 1, [⟨"N100", false, false, false⟩, ⟨"N75", false, false, false⟩, ⟨"N50", false, false, false⟩, ⟨"N25", true, false, false⟩], ["N75", "N50", "N25"], [⟨"N100", [0], [0], [0], 1, 1⟩, ⟨"N75", [0], [], [], 1, 1⟩, ⟨"N50", [0], [], [], 1, 1⟩, ⟨"N25", [0, 1], [1], [1], 1, 1⟩]⟩]⟩

end RelCertifier
