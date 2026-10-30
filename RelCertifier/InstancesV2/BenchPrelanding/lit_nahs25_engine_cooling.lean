/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_nahs25_engine_cooling` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_nahs25_engine_cooling`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def lit_nahs25_engine_cooling_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"lit_nahs25_engine_cooling", [
    ⟨"Cool", "Heat", true, [0, 1]⟩,
    ⟨"Heat", "Cool", true, [0, 1]⟩]⟩

end RelCertifier.Preland
