/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `salt_tank_stutter` (stutter_demo) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_stutter_demo.py`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def salt_tank_stutter_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"salt_tank_stutter", [
    ⟨"On", "Off", true, [0, 1, 2, 3]⟩,
    ⟨"On", "Off", false, [0, 1, 2, 3]⟩,
    ⟨"Off", "Off", true, [0, 1, 2, 3]⟩,
    ⟨"Off", "Off", false, [0, 1, 2, 3]⟩]⟩

end RelCertifier.Preland
