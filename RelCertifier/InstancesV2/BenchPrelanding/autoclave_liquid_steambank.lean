/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `autoclave_liquid_steambank` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py autoclave_liquid_steambank`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def autoclave_liquid_steambank_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"autoclave_liquid_steambank", [
    ⟨"HEAT", "EQUIL", true, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"HEAT", "EXPOSE", true, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"EQUIL", "HEAT", true, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"EQUIL", "HEAT", false, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"EQUIL", "EXPOSE", true, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"EXPOSE", "HEAT", true, [0, 1, 2, 3]⟩,
    ⟨"EXPOSE", "HEAT", false, [0, 1, 2, 3]⟩,
    ⟨"EXPOSE", "EQUIL", true, [0, 1, 2, 3]⟩,
    ⟨"EXHAUST", "HEAT", true, [0, 1, 2, 3]⟩,
    ⟨"EXHAUST", "HEAT", false, [0, 1, 2, 3]⟩,
    ⟨"EXHAUST", "EQUIL", true, [0, 1, 2, 3]⟩,
    ⟨"EXHAUST", "EQUIL", false, [0, 1, 2, 3]⟩,
    ⟨"EXHAUST", "EXPOSE", true, [0, 1, 2, 3]⟩,
    ⟨"EXHAUST", "EXPOSE", false, [0, 1, 2, 3]⟩]⟩

end RelCertifier.Preland
