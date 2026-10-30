/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_2to4_m015`: a mutant of `rover_terrain_2to4` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(<= L_w (+ L_v 0.25)) [L_w->R_w]` of `benchmarks/suite_v2/rover_terrain_2to4`; file `benchmarks/refute_mutants/rover_terrain_2to4_m015/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/rover_terrain_2to4_m015/input.txt` (do not edit). -/
def rover_terrain_2to4_m015_IRm : PProblem :=
  {
    name := "rover_terrain_2to4"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["v", "s", "w", "zs"]
      epsilon := "1.0"
      modes := [
        {
          name := "MUD"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "2.5") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.4") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.num "0.25") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.1") (.var "zs"))))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "5.0"))) (.cmp "<=" (.var "w") (.num "0.25")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.05"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12")))
          next := ["GRAVEL", "MUD"] },
        {
          name := "GRAVEL"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "4.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.15") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.num "0.45") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.03") (.var "zs"))))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "5.0")) (.cmp "<" (.var "s") (.num "12.0"))) (.cmp "<=" (.var "w") (.num "0.45")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.05"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12")))
          next := ["PAVED", "GRAVEL"] },
        {
          name := "PAVED"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "8.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.05") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.num "0.7") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.0") (.var "zs"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "12.0")) (.cmp "<=" (.var "w") (.num "0.7")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.05"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12")))
          next := ["PAVED"] } ] }
    R := {
      stateVars := ["v", "s", "w", "zs"]
      epsilon := "1.0"
      modes := [
        {
          name := "MUD"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.25") (.var "v")))),
            ("s", (.var "v")),
            ("w", (.num "0")),
            ("zs", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "5.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.05"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12")))
          next := ["GRAVEL", "MUD"] },
        {
          name := "GRAVEL"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.45") (.var "v")))),
            ("s", (.var "v")),
            ("w", (.num "0")),
            ("zs", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "5.0")) (.cmp "<" (.var "s") (.num "12.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.05"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12")))
          next := ["PAVED", "GRAVEL"] },
        {
          name := "PAVED"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.7") (.var "v")))),
            ("s", (.var "v")),
            ("w", (.num "0")),
            ("zs", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "12.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.05"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12")))
          next := ["PAVED"] } ] }
    invariants := [
      ("MUD", (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_v") (.var "L_w"))) (.cmp "<=" (.var "R_w") (.bin "+" (.var "L_v") (.num "0.25")))) (.cmp "<=" (.var "L_w") (.var "R_v")))),
      ("GRAVEL", (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_v") (.var "L_w"))) (.cmp "<=" (.var "R_w") (.bin "+" (.var "L_v") (.num "0.25")))) (.cmp "<=" (.var "L_w") (.var "R_v")))),
      ("PAVED", (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_v") (.var "L_w"))) (.cmp "<=" (.var "R_w") (.bin "+" (.var "L_v") (.num "0.25")))) (.cmp "<=" (.var "L_w") (.var "R_v"))))] }

/-- The finder's witness (kind B). -/
def rover_terrain_2to4_m015_wit : RefWitE :=
  { kind := "B", u := 0, m := 0, q0 := 0, k := 3,
    wL := [(7/145 : ℚ), (3/100 : ℚ), (2/25 : ℚ), (9/100 : ℚ)],
    wR := [(2/25 : ℚ), (3/100 : ℚ), (173/580 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
