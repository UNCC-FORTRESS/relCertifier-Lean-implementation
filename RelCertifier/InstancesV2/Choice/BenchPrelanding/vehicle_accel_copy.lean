/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_accel_copy` (choice) — emitted pre-landing record (GENERATED leaf)

Regenerate with `scripts/gen_v2_data.py --choice`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def vehicle_accel_copy_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"vehicle_accel_copy", [
    ⟨"Accel", "Accel", true, [0, 1]⟩,
    ⟨"Accel", "Accel", false, [0, 1]⟩,
    ⟨"Accel", "Coast", true, [0, 1]⟩,
    ⟨"Accel", "Coast", false, [0, 1]⟩,
    ⟨"Accel", "Brake", true, [0, 1]⟩,
    ⟨"Accel", "Brake", false, [0, 1]⟩,
    ⟨"Coast", "Accel", true, [0, 1]⟩,
    ⟨"Coast", "Accel", false, [0, 1]⟩,
    ⟨"Coast", "Coast", true, [0, 1]⟩,
    ⟨"Coast", "Coast", false, [0, 1]⟩,
    ⟨"Coast", "Brake", true, [0, 1]⟩,
    ⟨"Coast", "Brake", false, [0, 1]⟩,
    ⟨"Brake", "Accel", true, [0, 1]⟩,
    ⟨"Brake", "Accel", false, [0, 1]⟩,
    ⟨"Brake", "Coast", true, [0, 1]⟩,
    ⟨"Brake", "Coast", false, [0, 1]⟩,
    ⟨"Brake", "Brake", true, [0, 1]⟩,
    ⟨"Brake", "Brake", false, [0, 1]⟩]⟩

end RelCertifier.Preland
