/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `drl_lane_control` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py drl_lane_control`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/drl_lane_control/input.txt` (do not edit). -/
def drl_lane_control_IRv2 : PProblem :=
  {
    name := "drl_lane_control"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["d", "vf", "vl"]
      epsilon := "1.0"
      modes := [
        {
          name := "AccelLAccel"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.num "1.0")),
            ("vl", (.num "1.0"))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "9.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "9.0"))) (.cmp ">=" (.var "d") (.bin "+" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "0.5") (.var "vf")) (.var "vf")) (.bin "*" (.bin "*" (.num "-0.5") (.var "vl")) (.var "vl"))) (.bin "*" (.num "2.0") (.var "vf"))) (.num "1.0"))))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] },
        {
          name := "AccelLBrake"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.num "1.0")),
            ("vl", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "9.0"))) (.cmp ">=" (.var "vl") (.num "1.0"))) (.cmp "<=" (.var "vl") (.num "10.0"))) (.cmp ">=" (.var "d") (.bin "+" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "0.5") (.var "vf")) (.var "vf")) (.bin "*" (.bin "*" (.num "-0.5") (.var "vl")) (.var "vl"))) (.bin "*" (.num "2.0") (.var "vf"))) (.num "1.0"))))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] },
        {
          name := "CoastLAccel"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.num "0.0")),
            ("vl", (.num "1.0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "9.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] },
        {
          name := "CoastLBrake"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.num "0.0")),
            ("vl", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "1.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] },
        {
          name := "BrakeLAccel"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.bin "-" (.num "0.0") (.num "1.0"))),
            ("vl", (.num "1.0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "1.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "9.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] },
        {
          name := "BrakeLBrake"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.bin "-" (.num "0.0") (.num "1.0"))),
            ("vl", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "1.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "1.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] } ] }
    R := {
      stateVars := ["d", "vf", "vl"]
      epsilon := "1.0"
      modes := [
        {
          name := "AccelLAccel"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.num "1.0")),
            ("vl", (.num "1.0"))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "9.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "9.0"))) (.cmp ">=" (.var "d") (.bin "+" (.bin "*" (.bin "*" (.num "0.5") (.var "vf")) (.var "vf")) (.bin "*" (.bin "*" (.num "-0.5") (.var "vl")) (.var "vl")))))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] },
        {
          name := "AccelLBrake"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.num "1.0")),
            ("vl", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "9.0"))) (.cmp ">=" (.var "vl") (.num "1.0"))) (.cmp "<=" (.var "vl") (.num "10.0"))) (.cmp ">=" (.var "d") (.bin "+" (.bin "*" (.bin "*" (.num "0.5") (.var "vf")) (.var "vf")) (.bin "*" (.bin "*" (.num "-0.5") (.var "vl")) (.var "vl")))))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] },
        {
          name := "CoastLAccel"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.num "0.0")),
            ("vl", (.num "1.0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "9.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] },
        {
          name := "CoastLBrake"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.num "0.0")),
            ("vl", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "1.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] },
        {
          name := "BrakeLAccel"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.bin "-" (.num "0.0") (.num "1.0"))),
            ("vl", (.num "1.0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "1.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "9.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] },
        {
          name := "BrakeLBrake"
          odes := [("d", (.bin "-" (.var "vl") (.var "vf"))),
            ("vf", (.bin "-" (.num "0.0") (.num "1.0"))),
            ("vl", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "1.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "1.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vf") (.num "0.0")) (.cmp "<=" (.var "vf") (.num "10.0"))) (.cmp ">=" (.var "vl") (.num "0.0"))) (.cmp "<=" (.var "vl") (.num "10.0")))
          next := ["AccelLAccel", "AccelLBrake", "CoastLAccel", "CoastLBrake", "BrakeLAccel", "BrakeLBrake"] } ] }
    invariants := [
      ("AccelLAccel", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_vf") (.var "R_vf"))) (.cmp "<=" (.var "R_vf") (.var "L_vf"))) (.cmp "<=" (.var "L_vl") (.var "R_vl"))) (.cmp "<=" (.var "R_vl") (.var "L_vl")))),
      ("AccelLBrake", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_vf") (.var "R_vf"))) (.cmp "<=" (.var "R_vf") (.var "L_vf"))) (.cmp "<=" (.var "L_vl") (.var "R_vl"))) (.cmp "<=" (.var "R_vl") (.var "L_vl")))),
      ("CoastLAccel", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_vf") (.var "R_vf"))) (.cmp "<=" (.var "R_vf") (.var "L_vf"))) (.cmp "<=" (.var "L_vl") (.var "R_vl"))) (.cmp "<=" (.var "R_vl") (.var "L_vl")))),
      ("CoastLBrake", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_vf") (.var "R_vf"))) (.cmp "<=" (.var "R_vf") (.var "L_vf"))) (.cmp "<=" (.var "L_vl") (.var "R_vl"))) (.cmp "<=" (.var "R_vl") (.var "L_vl")))),
      ("BrakeLAccel", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_vf") (.var "R_vf"))) (.cmp "<=" (.var "R_vf") (.var "L_vf"))) (.cmp "<=" (.var "L_vl") (.var "R_vl"))) (.cmp "<=" (.var "R_vl") (.var "L_vl")))),
      ("BrakeLBrake", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_vf") (.var "R_vf"))) (.cmp "<=" (.var "R_vf") (.var "L_vf"))) (.cmp "<=" (.var "L_vl") (.var "R_vl"))) (.cmp "<=" (.var "R_vl") (.var "L_vl"))))] }

end RelCertifier.Parse
