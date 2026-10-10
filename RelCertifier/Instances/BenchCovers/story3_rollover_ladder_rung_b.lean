/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_ladder_rung_b` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `story3_rollover_ladder_rung_b` (emitted). -/
def story3_rollover_ladder_rung_b_cover : CoverEmitE :=
  ⟨"story3_rollover_ladder_rung_b", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2], [], []⟩, ⟨"MODER", [0, 1, 2], [], []⟩, ⟨"FLAT", [0, 1, 2], [], []⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [], []⟩, ⟨"MODER", [0, 1], [], []⟩, ⟨"FLAT", [0, 1], [], []⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [], []⟩, ⟨"MODER", [0, 1], [], []⟩, ⟨"FLAT", [0, 1], [], []⟩]⟩]⟩

end RelCertifier
