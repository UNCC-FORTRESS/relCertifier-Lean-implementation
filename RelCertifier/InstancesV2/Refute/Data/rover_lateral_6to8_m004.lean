/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_lateral_6to8_m004`: a mutant of `rover_lateral_6to8` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_y (+ R_y 0.5)) [<=->>=]` of `benchmarks/suite_v2/rover_lateral_6to8`; file `benchmarks/refute_mutants/rover_lateral_6to8_m004/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/rover_lateral_6to8_m004/input.txt` (do not edit). -/
def rover_lateral_6to8_m004_IRm : PProblem :=
  {
    name := "rover_lateral_6to8"
    lambdaMin := "1.0"
    lambdaMax := "8.0"
    L := {
      stateVars := ["v", "s", "psi", "theta_p", "y", "z", "phi_r", "w"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.var "w")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("w", (.bin "-" (.bin "*" (.num "-1") (.var "y")) (.bin "*" (.num "2") (.var "w"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.bin "+" (.var "y") (.var "w")) (.num "-0.5"))) (.cmp "<=" (.bin "+" (.var "y") (.var "w")) (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.var "w")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("w", (.bin "-" (.bin "*" (.num "-1") (.var "y")) (.bin "*" (.num "2") (.var "w"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.bin "+" (.var "y") (.var "w")) (.num "-0.5"))) (.cmp "<=" (.bin "+" (.var "y") (.var "w")) (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.var "w")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("w", (.bin "-" (.bin "*" (.num "-1") (.var "y")) (.bin "*" (.num "2") (.var "w"))))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.bin "+" (.var "y") (.var "w")) (.num "-0.5"))) (.cmp "<=" (.bin "+" (.var "y") (.var "w")) (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "theta_p", "y", "z", "phi_r", "w"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("w", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.bin "+" (.var "y") (.var "w")) (.num "-0.5"))) (.cmp "<=" (.bin "+" (.var "y") (.var "w")) (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("w", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.bin "+" (.var "y") (.var "w")) (.num "-0.5"))) (.cmp "<=" (.bin "+" (.var "y") (.var "w")) (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("w", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.bin "+" (.var "y") (.var "w")) (.num "-0.5"))) (.cmp "<=" (.bin "+" (.var "y") (.var "w")) (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp ">=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.5")))) (.cmp "<=" (.bin "+" (.var "L_y") (.var "L_w")) (.bin "+" (.var "R_y") (.num "0.5")))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p")))),
      ("MODER", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp ">=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.5")))) (.cmp "<=" (.bin "+" (.var "L_y") (.var "L_w")) (.bin "+" (.var "R_y") (.num "0.5")))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p")))),
      ("FLAT", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp ">=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.5")))) (.cmp "<=" (.bin "+" (.var "L_y") (.var "L_w")) (.bin "+" (.var "R_y") (.num "0.5")))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p"))))] }

/-- The finder's witness (kind B). -/
def rover_lateral_6to8_m004_wit : RefWitE :=
  { kind := "B", u := 0, m := 0, q0 := 0, k := 1,
    wL := [(3/20 : ℚ), (3/20 : ℚ), (0 : ℚ), (0 : ℚ), (7/20 : ℚ), (0 : ℚ), (0 : ℚ), (-3/20 : ℚ), (0 : ℚ)],
    wR := [(3/20 : ℚ), (3/20 : ℚ), (0 : ℚ), (0 : ℚ), (-3/20 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
