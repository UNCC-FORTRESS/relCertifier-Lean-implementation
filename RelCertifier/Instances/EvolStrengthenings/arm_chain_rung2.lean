/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_chain_rung2` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.arm_chain_rung2

namespace RelCertifier.Oracle

open RelCertifier.Parse

def arm_chain_rung2_cuts : EvolStrengthening :=
  { L := [
      ("ApproachA", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachB", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("ApproachC", [((.cmp ">=" (.var "theta") (.num "0.5")), CutRoute.diStrict)]),
      ("Hold", [((.cmp ">=" (.var "theta") (.num "0.6")), CutRoute.frozen)])
    ]
    R := [
      ("ApproachFast", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachSlow", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("Return", [])
    ] }

example : evolStrengtheningWF arm_chain_rung2_IR arm_chain_rung2_cuts = true := rfl

end RelCertifier.Oracle
