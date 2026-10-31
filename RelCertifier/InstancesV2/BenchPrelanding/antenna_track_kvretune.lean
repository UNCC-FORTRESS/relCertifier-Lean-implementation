/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `antenna_track_kvretune` (suite_v2) — emitted pre-landing record (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py antenna_track_kvretune`.
-/
import RelCertifier.Trusted.PrelandEmit

namespace RelCertifier.Preland

def antenna_track_kvretune_coverV2_prelanding : RelCertifier.Preland.PrelandEmitE :=
  ⟨"antenna_track_kvretune", [
    ⟨"TRACK", "STOW", true, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"STOW", "TRACK", true, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"STOW", "TRACK", false, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"STOWED", "TRACK", true, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"STOWED", "TRACK", false, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"STOWED", "STOW", true, [0, 1, 2, 3, 4, 5, 6, 7]⟩,
    ⟨"STOWED", "STOW", false, [0, 1, 2, 3, 4, 5, 6, 7]⟩]⟩

end RelCertifier.Preland
