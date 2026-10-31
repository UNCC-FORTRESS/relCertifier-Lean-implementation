/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_accel_copy` (choice) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf)

Regenerate with `scripts/gen_v2_data.py --choice`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

def vehicle_accel_copy_coverV2 : CoverEmitE :=
  ⟨"vehicle_accel_copy", [], [
    ⟨"Accel", (1 : ℚ) / 1, 1, [⟨"Accel", true, false, false⟩, ⟨"Coast", false, false, false⟩, ⟨"Brake", false, false, false⟩], ["Accel", "Coast", "Brake"], [⟨"Accel", [0, 1], [], [], 1, 1⟩, ⟨"Coast", [1], [], [], 1, 1⟩, ⟨"Brake", [1], [], [], 1, 1⟩]⟩,
    ⟨"Coast", (1 : ℚ) / 1, 1, [⟨"Accel", true, false, false⟩, ⟨"Coast", true, false, false⟩, ⟨"Brake", true, false, false⟩], ["Accel", "Coast", "Brake"], [⟨"Accel", [0, 1], [], [], 0, 1⟩, ⟨"Coast", [0, 1], [], [], 0, 1⟩, ⟨"Brake", [0, 1], [], [], 0, 1⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"Accel", false, false, false⟩, ⟨"Coast", false, false, false⟩, ⟨"Brake", true, false, false⟩], ["Accel", "Coast", "Brake"], [⟨"Accel", [0], [], [], 1, 1⟩, ⟨"Coast", [0], [], [], 1, 1⟩, ⟨"Brake", [0, 1], [], [], 1, 1⟩]⟩]⟩


end RelCertifier
