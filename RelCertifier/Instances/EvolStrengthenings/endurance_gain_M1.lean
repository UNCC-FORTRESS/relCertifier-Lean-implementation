/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `endurance_gain_M1` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.endurance_gain_M1

namespace RelCertifier.Oracle

open RelCertifier.Parse

def endurance_gain_M1_cuts : EvolStrengthening :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "v") (.num "0.40")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "v") (.num "0.575")), CutRoute.shape)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "v") (.num "0.40")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "v") (.num "0.575")), CutRoute.shape)])
    ] }

example : evolStrengtheningWF endurance_gain_M1_IR endurance_gain_M1_cuts = true := rfl

end RelCertifier.Oracle
