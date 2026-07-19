/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_chain_rung1` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.arm_chain_rung1

namespace RelCertifier.Oracle

open RelCertifier.Parse

def arm_chain_rung1_cuts : EvolStrengthening :=
  { L := [
      ("ApproachFast", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachSlow", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("Return", [])
    ]
    R := [
      ("Approach", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("Return", [])
    ] }

example : evolStrengtheningWF arm_chain_rung1_IR arm_chain_rung1_cuts = true := rfl

end RelCertifier.Oracle
