/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_6to8_m009`: a mutant of `rover_ladder_6to8` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(and (and (<= L_theta_p 0.25) (<= (- 0 0.25) L_theta_p)) (and (<= L_omega_theta 0.25) (<= (- 0 0.25) L_omega_theta))) [L_omega_theta->R_omega_theta]` of `benchmarks/suite_v2/rover_ladder_6to8`; file `benchmarks/refute_mutants/rover_ladder_6to8_m009/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/rover_ladder_6to8_m009/input.txt` (do not edit). -/
def rover_ladder_6to8_m009_IRm : PProblem :=
  {
    name := "rover_ladder_6to8"
    lambdaMin := "1.0"
    lambdaMax := "1.25"
    L := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "3.0") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "*" (.num "-1") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "omega_theta")) (.num "0.15")) (.bin "*" (.num "0.5") (.var "z")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.num "0.1")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))))))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "60.0"))) (.cmp "<=" (.var "v") (.num "3.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "5.0") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "*" (.num "-1") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "omega_theta")) (.num "0.05")) (.bin "*" (.num "0.5") (.var "z")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.num "0.05")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))))))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "60.0")) (.cmp "<" (.var "s") (.num "140.0"))) (.cmp "<=" (.var "v") (.num "5.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "6.5") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "*" (.num "-1") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "+" (.bin "*" (.num "-1") (.var "omega_theta")) (.bin "*" (.num "0.5") (.var "z")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "140.0")) (.cmp "<=" (.var "v") (.num "6.5")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "3.0") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.num "0.15")) (.bin "*" (.num "0.5") (.var "z")))),
            ("omega_theta", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.num "0.1")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "*" (.num "-1") (.var "psi"))))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "60.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "5.0") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.num "0.05")) (.bin "*" (.num "0.5") (.var "z")))),
            ("omega_theta", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.num "0.05")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "*" (.num "-1") (.var "psi"))))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "60.0")) (.cmp "<" (.var "s") (.num "140.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "6.5") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "0.5") (.var "z")))),
            ("omega_theta", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "*" (.num "-1") (.var "psi"))))))]
          guard := (.cmp ">=" (.var "s") (.num "140.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.and (.and (.cmp "<=" (.var "L_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "L_psi"))) (.and (.cmp "<=" (.var "L_omega_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "L_omega_psi"))))) (.and (.and (.cmp "<=" (.var "L_theta_p") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "L_theta_p"))) (.and (.cmp "<=" (.var "R_omega_theta") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "R_omega_theta"))))) (.and (.cmp "<=" (.var "L_phi_r") (.num "0.2")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.2")) (.var "L_phi_r")))) (.and (.cmp "<=" (.bin "+" (.bin "*" (.num "0.101937") (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.var "L_phi_r")) (.num "0.8")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.8")) (.bin "+" (.bin "*" (.num "0.101937") (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.var "L_phi_r"))))) (.and (.and (.and (.cmp "<=" (.var "R_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "R_psi"))) (.and (.cmp "<=" (.var "R_theta_p") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "R_theta_p")))) (.and (.cmp "<=" (.var "R_phi_r") (.num "0.2")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.2")) (.var "R_phi_r")))))),
      ("MODER", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.and (.and (.cmp "<=" (.var "L_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "L_psi"))) (.and (.cmp "<=" (.var "L_omega_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "L_omega_psi"))))) (.and (.and (.cmp "<=" (.var "L_theta_p") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "L_theta_p"))) (.and (.cmp "<=" (.var "R_omega_theta") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "R_omega_theta"))))) (.and (.cmp "<=" (.var "L_phi_r") (.num "0.2")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.2")) (.var "L_phi_r")))) (.and (.cmp "<=" (.bin "+" (.bin "*" (.num "0.101937") (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.var "L_phi_r")) (.num "0.8")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.8")) (.bin "+" (.bin "*" (.num "0.101937") (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.var "L_phi_r"))))) (.and (.and (.and (.cmp "<=" (.var "R_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "R_psi"))) (.and (.cmp "<=" (.var "R_theta_p") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "R_theta_p")))) (.and (.cmp "<=" (.var "R_phi_r") (.num "0.2")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.2")) (.var "R_phi_r")))))),
      ("FLAT", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.and (.and (.cmp "<=" (.var "L_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "L_psi"))) (.and (.cmp "<=" (.var "L_omega_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "L_omega_psi"))))) (.and (.and (.cmp "<=" (.var "L_theta_p") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "L_theta_p"))) (.and (.cmp "<=" (.var "R_omega_theta") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "R_omega_theta"))))) (.and (.cmp "<=" (.var "L_phi_r") (.num "0.2")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.2")) (.var "L_phi_r")))) (.and (.cmp "<=" (.bin "+" (.bin "*" (.num "0.101937") (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.var "L_phi_r")) (.num "0.8")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.8")) (.bin "+" (.bin "*" (.num "0.101937") (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.var "L_phi_r"))))) (.and (.and (.and (.cmp "<=" (.var "R_psi") (.num "0.35")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.35")) (.var "R_psi"))) (.and (.cmp "<=" (.var "R_theta_p") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "R_theta_p")))) (.and (.cmp "<=" (.var "R_phi_r") (.num "0.2")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.2")) (.var "R_phi_r"))))))] }

/-- The finder's witness (kind B). -/
def rover_ladder_6to8_m009_wit : RefWitE :=
  { kind := "B", u := 0, m := 0, q0 := 0, k := 6,
    wL := [(1 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (1/4 : ℚ), (1/2 : ℚ), (0 : ℚ), (0 : ℚ)],
    wR := [(2 : ℚ), (2 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
