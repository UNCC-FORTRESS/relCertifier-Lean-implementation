/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_4d_box` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.rover_4d_box

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_4d_box_cuts : EvolStrengthening :=
  { L := [
      ("HOLD", [((.cmp ">=" (.var "px") (.num "9.0")), CutRoute.frozen), ((.cmp "<=" (.var "px") (.num "11.0")), CutRoute.frozen)])
    ]
    R := [
      ("APPROACH", [((.cmp "<=" (.var "vx") (.num "1.5")), CutRoute.shape)]),
      ("SETTLE", [((.cmp ">=" (.var "vx") (.num "0.5")), CutRoute.frozen), ((.cmp "<=" (.var "vx") (.num "0.7")), CutRoute.frozen)])
    ] }

example : evolStrengtheningWF rover_4d_box_IR rover_4d_box_cuts = true := rfl

end RelCertifier.Oracle
