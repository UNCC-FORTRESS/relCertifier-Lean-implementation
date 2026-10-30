/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_nahs25_engine_cooling` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_nahs25_engine_cooling`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.lit_nahs25_engine_cooling

namespace RelCertifier.Oracle

open RelCertifier.Parse

def lit_nahs25_engine_cooling_cutsV2 : EvolStrengthening :=
  { L := [
      ("Cool", []),
      ("Heat", [])
    ]
    R := [
      ("Cool", []),
      ("Heat", [])
    ] }

def lit_nahs25_engine_cooling_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("Cool", []),
      ("Heat", [])
    ]
    R := [
      ("Cool", []),
      ("Heat", [])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem lit_nahs25_engine_cooling_cutsV2_wf : evolStrengtheningWF lit_nahs25_engine_cooling_IRv2 lit_nahs25_engine_cooling_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem lit_nahs25_engine_cooling_cutsV2X_wf : evolStrengtheningWFX lit_nahs25_engine_cooling_IRv2 lit_nahs25_engine_cooling_cutsV2X = true := rfl

end RelCertifier.Oracle
