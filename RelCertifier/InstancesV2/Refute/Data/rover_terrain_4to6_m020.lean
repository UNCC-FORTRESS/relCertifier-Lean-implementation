/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_4to6_m020`: a mutant of `rover_terrain_4to6` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_w L_u) [<=->>=]` of `benchmarks/suite_v2/rover_terrain_4to6`; file `benchmarks/refute_mutants/rover_terrain_4to6_m020/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/rover_terrain_4to6_m020/input.txt` (do not edit). -/
def rover_terrain_4to6_m020_IRm : PProblem :=
  {
    name := "rover_terrain_4to6"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["v", "s", "w", "zs", "u", "zh"]
      epsilon := "1.0"
      modes := [
        {
          name := "MUD"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "2.5") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.4") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.var "u") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.1") (.var "zs")))),
            ("u", (.bin "*" (.num "4") (.bin "-" (.num "0.25") (.var "u")))),
            ("zh", (.bin "-" (.bin "*" (.num "0.5") (.var "v")) (.var "zh")))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "5.0"))) (.cmp "<=" (.var "u") (.num "0.25")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5")))
          next := ["GRAVEL", "MUD"] },
        {
          name := "GRAVEL"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "4.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.15") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.var "u") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.03") (.var "zs")))),
            ("u", (.bin "*" (.num "4") (.bin "-" (.num "0.45") (.var "u")))),
            ("zh", (.bin "-" (.bin "*" (.num "0.2") (.var "v")) (.var "zh")))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "5.0")) (.cmp "<" (.var "s") (.num "12.0"))) (.cmp "<=" (.var "u") (.num "0.45")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5")))
          next := ["PAVED", "GRAVEL"] },
        {
          name := "PAVED"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "8.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.05") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.var "u") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.0") (.var "zs")))),
            ("u", (.bin "*" (.num "4") (.bin "-" (.num "0.7") (.var "u")))),
            ("zh", (.bin "-" (.bin "*" (.num "0.05") (.var "v")) (.var "zh")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "12.0")) (.cmp "<=" (.var "u") (.num "0.7")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5")))
          next := ["PAVED"] } ] }
    R := {
      stateVars := ["v", "s", "w", "zs", "u", "zh"]
      epsilon := "1.0"
      modes := [
        {
          name := "MUD"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "2.5") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.4") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.num "0.25") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.1") (.var "zs")))),
            ("u", (.num "0")),
            ("zh", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "5.0"))) (.cmp "<=" (.var "w") (.num "0.25")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5")))
          next := ["GRAVEL", "MUD"] },
        {
          name := "GRAVEL"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "4.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.15") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.num "0.45") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.03") (.var "zs")))),
            ("u", (.num "0")),
            ("zh", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "5.0")) (.cmp "<" (.var "s") (.num "12.0"))) (.cmp "<=" (.var "w") (.num "0.45")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5")))
          next := ["PAVED", "GRAVEL"] },
        {
          name := "PAVED"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "8.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.05") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.num "0.7") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.0") (.var "zs")))),
            ("u", (.num "0")),
            ("zh", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "12.0")) (.cmp "<=" (.var "w") (.num "0.7")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5")))
          next := ["PAVED"] } ] }
    invariants := [
      ("MUD", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_zs") (.var "L_zs"))) (.cmp "<=" (.var "L_v") (.var "L_w"))) (.cmp ">=" (.var "L_w") (.var "L_u"))) (.cmp "<=" (.var "L_w") (.bin "+" (.var "L_v") (.num "0.25")))) (.cmp "<=" (.var "L_zh") (.num "0.15")))),
      ("GRAVEL", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_zs") (.var "L_zs"))) (.cmp "<=" (.var "L_v") (.var "L_w"))) (.cmp ">=" (.var "L_w") (.var "L_u"))) (.cmp "<=" (.var "L_w") (.bin "+" (.var "L_v") (.num "0.25")))) (.cmp "<=" (.var "L_zh") (.num "0.15")))),
      ("PAVED", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_zs") (.var "L_zs"))) (.cmp "<=" (.var "L_v") (.var "L_w"))) (.cmp ">=" (.var "L_w") (.var "L_u"))) (.cmp "<=" (.var "L_w") (.bin "+" (.var "L_v") (.num "0.25")))) (.cmp "<=" (.var "L_zh") (.num "0.15"))))] }

/-- The finder's witness (kind B). -/
def rover_terrain_4to6_m020_wit : RefWitE :=
  { kind := "B", u := 0, m := 0, q0 := 0, k := 4,
    wL := [(1/4 : ℚ), (1/25 : ℚ), (1/4 : ℚ), (1/25 : ℚ), (19/100 : ℚ), (1/25 : ℚ)],
    wR := [(1/4 : ℚ), (1/25 : ℚ), (1/4 : ℚ), (0 : ℚ), (3/20 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
