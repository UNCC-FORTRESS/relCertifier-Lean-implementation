/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `robot_braking` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.robot_braking

namespace RelCertifier.Oracle

open RelCertifier.Parse

def robot_braking_cuts : EvolStrengthening :=
  { L := [
      ("CRUISE", [((.cmp ">=" (.var "v") (.num "0.8")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.2")), CutRoute.shape)])
    ]
    R := [
      ("FAST", []),
      ("MID", [((.cmp "<=" (.var "v") (.num "3.5")), CutRoute.shape)]),
      ("SLOW", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.5")), CutRoute.shape)])
    ] }

example : evolStrengtheningWF robot_braking_IR robot_braking_cuts = true := rfl

end RelCertifier.Oracle
