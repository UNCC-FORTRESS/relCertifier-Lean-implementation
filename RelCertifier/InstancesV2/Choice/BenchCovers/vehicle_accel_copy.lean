/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_accel_copy` (choice) — emitted cover, `RELCERT_IMPLIED_CUT=1 RELCERT_CHOICE=1`, progress certificates by default (GENERATED leaf)
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

def vehicle_accel_copy_coverV2 : CoverEmitE :=
  ⟨"vehicle_accel_copy", [], [
    ⟨"Accel", (1 : ℚ) / 1, 1, [⟨"Accel", true, false, false⟩, ⟨"Coast", false, true, true⟩, ⟨"Brake", false, false, false⟩], ["Accel", "Coast", "Brake"], [⟨"Accel", [0, 1], [0], [0], 1, 1⟩, ⟨"Coast", [1], [0, 1], [0, 1], 1, 1⟩, ⟨"Brake", [1], [1], [1], 1, 1⟩]⟩,
    ⟨"Coast", (1 : ℚ) / 1, 1, [⟨"Accel", false, false, false⟩, ⟨"Coast", true, true, true⟩, ⟨"Brake", false, false, false⟩], ["Accel", "Coast", "Brake"], [⟨"Accel", [0], [0], [0], 1, 1⟩, ⟨"Coast", [0, 1], [0, 1], [0, 1], 1, 1⟩, ⟨"Brake", [1], [1], [1], 1, 1⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"Accel", false, false, false⟩, ⟨"Coast", false, true, true⟩, ⟨"Brake", true, false, false⟩], ["Accel", "Coast", "Brake"], [⟨"Accel", [0], [0], [0], 1, 1⟩, ⟨"Coast", [0], [0, 1], [0, 1], 1, 1⟩, ⟨"Brake", [0, 1], [1], [1], 1, 1⟩]⟩]⟩


end RelCertifier
