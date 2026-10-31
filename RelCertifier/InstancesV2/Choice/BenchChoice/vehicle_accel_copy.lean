/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_accel_copy` (choice) — emitted choice record (GENERATED leaf)

Regenerate with `scripts/gen_v2_data.py --choice`.
-/
import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def vehicle_accel_copy_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"vehicle_accel_copy", [
    ⟨"Accel", "Brake", .repo, true, ["Accel"]⟩,
    ⟨"Brake", "Coast", .repo, true, ["Brake"]⟩]⟩

end RelCertifier.Choice
