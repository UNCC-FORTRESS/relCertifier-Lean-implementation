/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_drag` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.rover_drag

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_drag_cuts : EvolStrengthening :=
  { L := [
      ("Cruise", [((.cmp ">=" (.var "vx") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "vx") (.num "1.21")), CutRoute.diStrict)])
    ]
    R := [
      ("Track", [((.cmp ">=" (.var "vx") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "vx") (.num "1.21")), CutRoute.diStrict)])
    ] }

example : evolStrengtheningWF rover_drag_IR rover_drag_cuts = true := rfl

end RelCertifier.Oracle
