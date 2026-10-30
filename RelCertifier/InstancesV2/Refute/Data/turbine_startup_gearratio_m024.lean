/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `turbine_startup_gearratio_m024`: a mutant of `turbine_startup_gearratio` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(>= R_w 11.979) [>=-><=]` of `benchmarks/suite_v2/turbine_startup_gearratio`; file `benchmarks/refute_mutants/turbine_startup_gearratio_m024/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/turbine_startup_gearratio_m024/input.txt` (do not edit). -/
def turbine_startup_gearratio_m024_IRm : PProblem :=
  {
    name := "turbine_startup_gearratio"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["w", "G", "t"]
      epsilon := "1.0"
      modes := [
        {
          name := "SPINUP"
          odes := [("w", (.bin "*" (.num "0.03") (.bin "-" (.num "9") (.var "w")))),
            ("G", (.num "0.0")),
            ("t", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "w") (.num "2.1")) (.cmp "<" (.var "w") (.num "5.25")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.9755"))) (.cmp ">=" (.var "G") (.num "0.0"))) (.cmp "<=" (.var "G") (.num "5.03"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["SPINUP", "RAMP"] },
        {
          name := "RAMP"
          odes := [("w", (.bin "*" (.num "0.0380952") (.bin "-" (.num "7.875") (.var "w")))),
            ("G", (.num "0.0")),
            ("t", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "w") (.num "5.25")) (.cmp "<" (.var "w") (.num "7.245")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.9755"))) (.cmp ">=" (.var "G") (.num "0.0"))) (.cmp "<=" (.var "G") (.num "5.03"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["RAMP", "GEN"] },
        {
          name := "GEN"
          odes := [("w", (.bin "*" (.num "0.047619") (.bin "-" (.num "12.705") (.var "w")))),
            ("G", (.num "0.0")),
            ("t", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "w") (.num "7.245")) (.cmp "<" (.var "w") (.num "12.57795")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.9755"))) (.cmp ">=" (.var "G") (.num "0.0"))) (.cmp "<=" (.var "G") (.num "5.03"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["GEN", "REG"] },
        {
          name := "REG"
          odes := [("w", (.bin "*" (.num "1.25") (.bin "-" (.num "12.705") (.var "w")))),
            ("G", (.num "0.0")),
            ("t", (.num "0.0"))]
          guard := (.cmp ">=" (.var "w") (.num "12.57795"))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.9755"))) (.cmp ">=" (.var "G") (.num "0.0"))) (.cmp "<=" (.var "G") (.num "5.03"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["REG", "GUST"] },
        {
          name := "GUST"
          odes := [("w", (.bin "+" (.bin "*" (.num "1.25") (.bin "-" (.num "12.705") (.var "w"))) (.bin "*" (.num "0.24") (.var "G")))),
            ("G", (.num "0.0")),
            ("t", (.num "1.0"))]
          guard := (.cmp ">=" (.var "w") (.num "12.57795"))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.9755"))) (.cmp ">=" (.var "G") (.num "0.0"))) (.cmp "<=" (.var "G") (.num "5.03"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["GUST", "REG"] } ] }
    R := {
      stateVars := ["w", "G", "t"]
      epsilon := "1.0"
      modes := [
        {
          name := "SPINUP"
          odes := [("w", (.bin "*" (.num "0.03") (.bin "-" (.num "9") (.var "w")))),
            ("G", (.num "0.0")),
            ("t", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "w") (.num "2")) (.cmp "<" (.var "w") (.num "5")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.31"))) (.cmp ">=" (.var "G") (.num "0.0"))) (.cmp "<=" (.var "G") (.num "5.03"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["SPINUP", "RAMP"] },
        {
          name := "RAMP"
          odes := [("w", (.bin "*" (.num "0.04") (.bin "-" (.num "7.5") (.var "w")))),
            ("G", (.num "0.0")),
            ("t", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "w") (.num "5")) (.cmp "<" (.var "w") (.num "6.9")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.31"))) (.cmp ">=" (.var "G") (.num "0.0"))) (.cmp "<=" (.var "G") (.num "5.03"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["RAMP", "GEN"] },
        {
          name := "GEN"
          odes := [("w", (.bin "*" (.num "0.05") (.bin "-" (.num "12.1") (.var "w")))),
            ("G", (.num "0.0")),
            ("t", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "w") (.num "6.9")) (.cmp "<" (.var "w") (.num "11.979")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.31"))) (.cmp ">=" (.var "G") (.num "0.0"))) (.cmp "<=" (.var "G") (.num "5.03"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["GEN", "REG"] },
        {
          name := "REG"
          odes := [("w", (.bin "*" (.num "1.3125") (.bin "-" (.num "12.1") (.var "w")))),
            ("G", (.num "0.0")),
            ("t", (.num "0.0"))]
          guard := (.cmp ">=" (.var "w") (.num "11.979"))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.31"))) (.cmp ">=" (.var "G") (.num "0.0"))) (.cmp "<=" (.var "G") (.num "5.03"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["REG", "GUST"] },
        {
          name := "GUST"
          odes := [("w", (.bin "+" (.bin "*" (.num "1.3125") (.bin "-" (.num "12.1") (.var "w"))) (.bin "*" (.num "0.24") (.var "G")))),
            ("G", (.num "0.0")),
            ("t", (.num "1.0"))]
          guard := (.cmp ">=" (.var "w") (.num "11.979"))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "w") (.num "0.0")) (.cmp "<=" (.var "w") (.num "13.31"))) (.cmp ">=" (.var "G") (.num "0.0"))) (.cmp "<=" (.var "G") (.num "5.03"))) (.cmp ">=" (.var "t") (.num "0.0")))
          next := ["GUST", "REG"] } ] }
    invariants := [
      ("SPINUP", (.and (.and (.and (.and (.cmp "<=" (.var "L_w") (.bin "*" (.num "1.05") (.var "R_w"))) (.cmp "<=" (.var "L_G") (.var "R_G"))) (.cmp "<=" (.var "R_G") (.var "L_G"))) (.cmp "<=" (.var "L_t") (.var "R_t"))) (.cmp "<=" (.var "R_t") (.var "L_t")))),
      ("RAMP", (.and (.and (.and (.and (.cmp "<=" (.var "L_w") (.bin "*" (.num "1.05") (.var "R_w"))) (.cmp "<=" (.var "L_G") (.var "R_G"))) (.cmp "<=" (.var "R_G") (.var "L_G"))) (.cmp "<=" (.var "L_t") (.var "R_t"))) (.cmp "<=" (.var "R_t") (.var "L_t")))),
      ("GEN", (.and (.and (.and (.and (.cmp "<=" (.var "L_w") (.bin "*" (.num "1.05") (.var "R_w"))) (.cmp "<=" (.var "L_G") (.var "R_G"))) (.cmp "<=" (.var "R_G") (.var "L_G"))) (.cmp "<=" (.var "L_t") (.var "R_t"))) (.cmp "<=" (.var "R_t") (.var "L_t")))),
      ("REG", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_w") (.bin "+" (.bin "*" (.num "1.05") (.var "R_w")) (.num "0.0605"))) (.cmp "<=" (.var "L_G") (.var "R_G"))) (.cmp "<=" (.var "R_G") (.var "L_G"))) (.cmp "<=" (.var "L_t") (.var "R_t"))) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "R_w") (.num "11.979")))),
      ("GUST", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_w") (.bin "+" (.bin "*" (.num "1.05") (.var "R_w")) (.num "0.0605"))) (.cmp "<=" (.var "L_G") (.var "R_G"))) (.cmp "<=" (.var "R_G") (.var "L_G"))) (.cmp "<=" (.var "L_t") (.var "R_t"))) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "R_w") (.num "11.979"))))] }

/-- The finder's witness (kind C). -/
def turbine_startup_gearratio_m024_wit : RefWitE :=
  { kind := "C", u := 2, m := 3, q0 := 3, k := 0,
    wL := [(262769/20000 : ℚ), (0 : ℚ), (0 : ℚ)],
    wR := [(262769/21000 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
