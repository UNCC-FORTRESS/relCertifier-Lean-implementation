/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung1` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.rover_dof_terrain_rung1

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_dof_terrain_rung1_cuts : EvolStrengthening :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

example : evolStrengtheningWF rover_dof_terrain_rung1_IR rover_dof_terrain_rung1_cuts = true := rfl

end RelCertifier.Oracle
