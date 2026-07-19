/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `endurance_orderlift_2to3` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.endurance_orderlift_2to3

namespace RelCertifier.Oracle

open RelCertifier.Parse

def endurance_orderlift_2to3_cuts : EvolStrengthening :=
  { L := [
      ("STEEP", []),
      ("MODER", []),
      ("FLAT", [])
    ]
    R := [
      ("STEEP", []),
      ("MODER", []),
      ("FLAT", [])
    ] }

example : evolStrengtheningWF endurance_orderlift_2to3_IR endurance_orderlift_2to3_cuts = true := rfl

end RelCertifier.Oracle
