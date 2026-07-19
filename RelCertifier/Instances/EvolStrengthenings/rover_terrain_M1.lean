/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_M1` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.rover_terrain_M1

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_terrain_M1_cuts : EvolStrengthening :=
  { L := [
      ("ROUGH", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "v") (.num "0.6")), CutRoute.shape)]),
      ("SMOOTH", [((.cmp ">=" (.var "v") (.num "1.0")), CutRoute.shape)])
    ]
    R := [
      ("ROUGH", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "v") (.num "0.6")), CutRoute.shape)]),
      ("SMOOTH", [((.cmp ">=" (.var "v") (.num "1.0")), CutRoute.shape)])
    ] }

example : evolStrengtheningWF rover_terrain_M1_IR rover_terrain_M1_cuts = true := rfl

end RelCertifier.Oracle
