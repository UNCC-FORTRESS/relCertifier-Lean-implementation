/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_girard08_robot_m016`: a mutant of `lit_girard08_robot` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= (+ (* L_ex L_ex) (* L_ey L_ey) (* 100.0 (+ (* L_zx L_zx) (* L_zy L_zy)))) 0.16) [<=->>=]` of `benchmarks/suite_v2/lit_girard08_robot`; file `benchmarks/refute_mutants/lit_girard08_robot_m016/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/lit_girard08_robot_m016/input.txt` (do not edit). -/
def lit_girard08_robot_m016_IRm : PProblem :=
  {
    name := "lit_girard08_robot"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["ex", "ey", "zx", "zy", "wx", "wy"]
      epsilon := "1.0"
      modes := [
        {
          name := "M1"
          odes := [("ex", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zx") (.var "ex"))) (.num "0.2"))),
            ("ey", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zy") (.var "ey"))) (.num "0.0"))),
            ("zx", (.bin "-" (.bin "*" (.num "-0.5") (.var "zx")) (.bin "*" (.num "0.005") (.var "ex")))),
            ("zy", (.bin "-" (.bin "*" (.num "-0.5") (.var "zy")) (.bin "*" (.num "0.005") (.var "ey")))),
            ("wx", (.num "0.2")),
            ("wy", (.num "0.0"))]
          guard := (.and (.and (.cmp ">=" (.bin "+" (.var "wx") (.var "ex")) (.num "0.0")) (.cmp "<=" (.bin "+" (.var "wx") (.var "ex")) (.num "3.0"))) (.cmp ">=" (.bin "+" (.var "wy") (.var "ey")) (.num "0.0")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M1", "M2"] },
        {
          name := "M2"
          odes := [("ex", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zx") (.var "ex"))) (.num "0.1414213"))),
            ("ey", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zy") (.var "ey"))) (.bin "-" (.num "0.0") (.num "0.1414213")))),
            ("zx", (.bin "-" (.bin "*" (.num "-0.5") (.var "zx")) (.bin "*" (.num "0.005") (.var "ex")))),
            ("zy", (.bin "-" (.bin "*" (.num "-0.5") (.var "zy")) (.bin "*" (.num "0.005") (.var "ey")))),
            ("wx", (.num "0.1414213")),
            ("wy", (.bin "-" (.num "0.0") (.num "0.1414213")))]
          guard := (.and (.cmp ">=" (.bin "+" (.var "wx") (.var "ex")) (.num "3.0")) (.cmp ">=" (.bin "+" (.var "wy") (.var "ey")) (.num "0.0")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M2", "M3"] },
        {
          name := "M3"
          odes := [("ex", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zx") (.var "ex"))) (.bin "-" (.num "0.0") (.num "0.1414213")))),
            ("ey", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zy") (.var "ey"))) (.bin "-" (.num "0.0") (.num "0.1414213")))),
            ("zx", (.bin "-" (.bin "*" (.num "-0.5") (.var "zx")) (.bin "*" (.num "0.005") (.var "ex")))),
            ("zy", (.bin "-" (.bin "*" (.num "-0.5") (.var "zy")) (.bin "*" (.num "0.005") (.var "ey")))),
            ("wx", (.bin "-" (.num "0.0") (.num "0.1414213"))),
            ("wy", (.bin "-" (.num "0.0") (.num "0.1414213")))]
          guard := (.and (.cmp ">=" (.bin "+" (.var "wx") (.var "ex")) (.num "0.0")) (.cmp "<=" (.bin "+" (.var "wy") (.var "ey")) (.num "0.0")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M3", "M4"] },
        {
          name := "M4"
          odes := [("ex", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zx") (.var "ex"))) (.bin "-" (.num "0.0") (.num "0.2")))),
            ("ey", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zy") (.var "ey"))) (.num "0.0"))),
            ("zx", (.bin "-" (.bin "*" (.num "-0.5") (.var "zx")) (.bin "*" (.num "0.005") (.var "ex")))),
            ("zy", (.bin "-" (.bin "*" (.num "-0.5") (.var "zy")) (.bin "*" (.num "0.005") (.var "ey")))),
            ("wx", (.bin "-" (.num "0.0") (.num "0.2"))),
            ("wy", (.num "0.0"))]
          guard := (.and (.and (.cmp ">=" (.bin "+" (.var "wx") (.var "ex")) (.bin "-" (.num "0.0") (.num "3.0"))) (.cmp "<=" (.bin "+" (.var "wx") (.var "ex")) (.num "0.0"))) (.cmp "<=" (.bin "+" (.var "wy") (.var "ey")) (.num "0.0")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M4", "M5"] },
        {
          name := "M5"
          odes := [("ex", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zx") (.var "ex"))) (.bin "-" (.num "0.0") (.num "0.1414213")))),
            ("ey", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zy") (.var "ey"))) (.num "0.1414213"))),
            ("zx", (.bin "-" (.bin "*" (.num "-0.5") (.var "zx")) (.bin "*" (.num "0.005") (.var "ex")))),
            ("zy", (.bin "-" (.bin "*" (.num "-0.5") (.var "zy")) (.bin "*" (.num "0.005") (.var "ey")))),
            ("wx", (.bin "-" (.num "0.0") (.num "0.1414213"))),
            ("wy", (.num "0.1414213"))]
          guard := (.and (.cmp "<=" (.bin "+" (.var "wx") (.var "ex")) (.bin "-" (.num "0.0") (.num "3.0"))) (.cmp "<=" (.bin "+" (.var "wy") (.var "ey")) (.num "0.0")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M5", "M6"] },
        {
          name := "M6"
          odes := [("ex", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zx") (.var "ex"))) (.num "0.1414213"))),
            ("ey", (.bin "-" (.bin "*" (.num "0.5") (.bin "-" (.var "zy") (.var "ey"))) (.num "0.1414213"))),
            ("zx", (.bin "-" (.bin "*" (.num "-0.5") (.var "zx")) (.bin "*" (.num "0.005") (.var "ex")))),
            ("zy", (.bin "-" (.bin "*" (.num "-0.5") (.var "zy")) (.bin "*" (.num "0.005") (.var "ey")))),
            ("wx", (.num "0.1414213")),
            ("wy", (.num "0.1414213"))]
          guard := (.and (.cmp "<=" (.bin "+" (.var "wx") (.var "ex")) (.num "0.0")) (.cmp ">=" (.bin "+" (.var "wy") (.var "ey")) (.num "0.0")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M6", "M1"] } ] }
    R := {
      stateVars := ["wx", "wy"]
      epsilon := "1.0"
      modes := [
        {
          name := "M1"
          odes := [("wx", (.num "0.2")),
            ("wy", (.num "0.0"))]
          guard := (.and (.and (.cmp ">=" (.var "wx") (.num "-0.4")) (.cmp "<=" (.var "wx") (.num "3.4"))) (.cmp ">=" (.var "wy") (.num "-0.4")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M1", "M2", "M3", "M4", "M6"] },
        {
          name := "M2"
          odes := [("wx", (.num "0.1414213")),
            ("wy", (.bin "-" (.num "0.0") (.num "0.1414213")))]
          guard := (.and (.cmp ">=" (.var "wx") (.num "2.6")) (.cmp ">=" (.var "wy") (.num "-0.4")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M1", "M2", "M3"] },
        {
          name := "M3"
          odes := [("wx", (.bin "-" (.num "0.0") (.num "0.1414213"))),
            ("wy", (.bin "-" (.num "0.0") (.num "0.1414213")))]
          guard := (.and (.cmp ">=" (.var "wx") (.num "-0.4")) (.cmp "<=" (.var "wy") (.num "0.4")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M1", "M2", "M3", "M4", "M6"] },
        {
          name := "M4"
          odes := [("wx", (.bin "-" (.num "0.0") (.num "0.2"))),
            ("wy", (.num "0.0"))]
          guard := (.and (.and (.cmp ">=" (.var "wx") (.num "-3.4")) (.cmp "<=" (.var "wx") (.num "0.4"))) (.cmp "<=" (.var "wy") (.num "0.4")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M1", "M3", "M4", "M5", "M6"] },
        {
          name := "M5"
          odes := [("wx", (.bin "-" (.num "0.0") (.num "0.1414213"))),
            ("wy", (.num "0.1414213"))]
          guard := (.and (.cmp "<=" (.var "wx") (.num "-2.6")) (.cmp "<=" (.var "wy") (.num "0.4")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M4", "M5", "M6"] },
        {
          name := "M6"
          odes := [("wx", (.num "0.1414213")),
            ("wy", (.num "0.1414213"))]
          guard := (.and (.cmp "<=" (.var "wx") (.num "0.4")) (.cmp ">=" (.var "wy") (.num "-0.4")))
          evolve := (.cmp "<=" (.num "0.0") (.num "1.0"))
          next := ["M1", "M3", "M4", "M5", "M6"] } ] }
    invariants := [
      ("M1", (.and (.and (.and (.and (.cmp "<=" (.var "L_wx") (.var "R_wx")) (.cmp "<=" (.var "R_wx") (.var "L_wx"))) (.cmp "<=" (.var "L_wy") (.var "R_wy"))) (.cmp "<=" (.var "R_wy") (.var "L_wy"))) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.var "L_ex") (.var "L_ex")) (.bin "*" (.var "L_ey") (.var "L_ey"))) (.bin "*" (.num "100.0") (.bin "+" (.bin "*" (.var "L_zx") (.var "L_zx")) (.bin "*" (.var "L_zy") (.var "L_zy"))))) (.num "0.16")))),
      ("M2", (.and (.and (.and (.and (.cmp "<=" (.var "L_wx") (.var "R_wx")) (.cmp "<=" (.var "R_wx") (.var "L_wx"))) (.cmp "<=" (.var "L_wy") (.var "R_wy"))) (.cmp "<=" (.var "R_wy") (.var "L_wy"))) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.var "L_ex") (.var "L_ex")) (.bin "*" (.var "L_ey") (.var "L_ey"))) (.bin "*" (.num "100.0") (.bin "+" (.bin "*" (.var "L_zx") (.var "L_zx")) (.bin "*" (.var "L_zy") (.var "L_zy"))))) (.num "0.16")))),
      ("M3", (.and (.and (.and (.and (.cmp "<=" (.var "L_wx") (.var "R_wx")) (.cmp "<=" (.var "R_wx") (.var "L_wx"))) (.cmp "<=" (.var "L_wy") (.var "R_wy"))) (.cmp "<=" (.var "R_wy") (.var "L_wy"))) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.var "L_ex") (.var "L_ex")) (.bin "*" (.var "L_ey") (.var "L_ey"))) (.bin "*" (.num "100.0") (.bin "+" (.bin "*" (.var "L_zx") (.var "L_zx")) (.bin "*" (.var "L_zy") (.var "L_zy"))))) (.num "0.16")))),
      ("M4", (.and (.and (.and (.and (.cmp "<=" (.var "L_wx") (.var "R_wx")) (.cmp "<=" (.var "R_wx") (.var "L_wx"))) (.cmp "<=" (.var "L_wy") (.var "R_wy"))) (.cmp "<=" (.var "R_wy") (.var "L_wy"))) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.var "L_ex") (.var "L_ex")) (.bin "*" (.var "L_ey") (.var "L_ey"))) (.bin "*" (.num "100.0") (.bin "+" (.bin "*" (.var "L_zx") (.var "L_zx")) (.bin "*" (.var "L_zy") (.var "L_zy"))))) (.num "0.16")))),
      ("M5", (.and (.and (.and (.and (.cmp "<=" (.var "L_wx") (.var "R_wx")) (.cmp "<=" (.var "R_wx") (.var "L_wx"))) (.cmp "<=" (.var "L_wy") (.var "R_wy"))) (.cmp "<=" (.var "R_wy") (.var "L_wy"))) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.var "L_ex") (.var "L_ex")) (.bin "*" (.var "L_ey") (.var "L_ey"))) (.bin "*" (.num "100.0") (.bin "+" (.bin "*" (.var "L_zx") (.var "L_zx")) (.bin "*" (.var "L_zy") (.var "L_zy"))))) (.num "0.16")))),
      ("M6", (.and (.and (.and (.and (.cmp "<=" (.var "L_wx") (.var "R_wx")) (.cmp "<=" (.var "R_wx") (.var "L_wx"))) (.cmp "<=" (.var "L_wy") (.var "R_wy"))) (.cmp "<=" (.var "R_wy") (.var "L_wy"))) (.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.var "L_ex") (.var "L_ex")) (.bin "*" (.var "L_ey") (.var "L_ey"))) (.bin "*" (.num "100.0") (.bin "+" (.bin "*" (.var "L_zx") (.var "L_zx")) (.bin "*" (.var "L_zy") (.var "L_zy"))))) (.num "0.16"))))] }

/-- The finder's witness (kind B). -/
def lit_girard08_robot_m016_wit : RefWitE :=
  { kind := "B", u := 0, m := 0, q0 := 0, k := 4,
    wL := [(0 : ℚ), (0 : ℚ), (-1/25 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
    wR := [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
