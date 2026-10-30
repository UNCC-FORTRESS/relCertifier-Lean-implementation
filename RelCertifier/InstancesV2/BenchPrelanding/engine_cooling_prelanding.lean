/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `engine_cooling_prelanding` (prelanding_demo) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_prelanding_demo.py`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def engine_cooling_prelanding_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"engine_cooling_prelanding", [
    ⟨"Cool", "Heat", true, [0, 1]⟩,
    ⟨"Heat", "Cool", true, [0, 1]⟩]⟩

end RelCertifier.Preland
