/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_accel_copy` (choice) — emitted reposition certificates (GENERATED leaf)

Regenerate with `scripts/gen_v2_data.py --choice`.
-/
import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def vehicle_accel_copy_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"vehicle_accel_copy", [
    ⟨"Accel", "Accel", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Coast", "Brake"]⟩,
    ⟨"Accel", "Accel", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Coast", "Brake"]⟩,
    ⟨"Accel", "Coast", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Accel", "Coast", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Accel", "Brake", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Coast"]⟩,
    ⟨"Accel", "Brake", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Coast"]⟩,
    ⟨"Coast", "Accel", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Coast", "Brake"]⟩,
    ⟨"Coast", "Accel", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Coast", "Brake"]⟩,
    ⟨"Coast", "Coast", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Coast", "Coast", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Coast", "Brake", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Coast"]⟩,
    ⟨"Coast", "Brake", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Coast"]⟩,
    ⟨"Brake", "Accel", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Coast", "Brake"]⟩,
    ⟨"Brake", "Accel", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Coast", "Brake"]⟩,
    ⟨"Brake", "Coast", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Brake", "Coast", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Brake", "Brake", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Coast"]⟩,
    ⟨"Brake", "Brake", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Coast"]⟩]⟩

end RelCertifier.Progress
