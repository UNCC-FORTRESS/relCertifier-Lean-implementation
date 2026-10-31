/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `elevator_start_discbrake` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py elevator_start_discbrake`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def elevator_start_discbrake_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"elevator_start_discbrake", [
    ⟨"LIFT", "UP", true, [0, 2, 4, 1, 3]⟩,
    ⟨"LIFT", "APP", true, [0, 1, 2, 3, 4]⟩,
    ⟨"LIFT", "APP", false, [0, 1, 2, 3, 4]⟩,
    ⟨"UP", "LIFT", true, [0, 1, 2, 3]⟩,
    ⟨"UP", "LIFT", false, [0, 1, 2, 3]⟩,
    ⟨"UP", "APP", true, [0, 1, 2, 3]⟩,
    ⟨"APP", "LIFT", true, [0, 1, 2, 3]⟩,
    ⟨"APP", "LIFT", false, [0, 1, 2, 3]⟩,
    ⟨"APP", "UP", true, [0, 1, 2, 3]⟩,
    ⟨"APP", "UP", false, [0, 1, 2, 3]⟩,
    ⟨"STOP", "LIFT", true, [0, 1, 2, 3]⟩,
    ⟨"STOP", "LIFT", false, [0, 1, 2, 3]⟩,
    ⟨"STOP", "UP", true, [0, 1, 2, 3]⟩,
    ⟨"STOP", "UP", false, [0, 1, 2, 3]⟩,
    ⟨"STOP", "APP", true, [0, 1, 2, 3]⟩,
    ⟨"STOP", "APP", false, [0, 1, 2, 3]⟩]⟩

end RelCertifier.Preland
