/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_drag_m061`: a mutant of `stopline_drag` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= (- 0.0 0.35) L_omega_psi) [<=->>=]` of `benchmarks/suite_v2/stopline_drag`; file `benchmarks/refute_mutants/stopline_drag_m061/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/stopline_drag_m061/input.txt` (do not edit). -/
def stopline_drag_m061_IRm : PProblem :=
  {
    name := "stopline_drag"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["p", "s", "v", "b", "c", "psi", "omega_psi", "theta_p", "omega_theta", "z", "omega_z", "phi_r", "omega_phi", "y", "omega_y"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("p", (.var "v")),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("v", (.num "0.0")),
            ("b", (.bin "*" (.num "20.0") (.bin "-" (.var "c") (.var "b")))),
            ("c", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "0.0") (.var "c")))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "-" (.num "0.0") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "+" (.bin "+" (.bin "-" (.num "0.0") (.var "omega_theta")) (.bin "*" (.num "0.5") (.var "z"))) (.bin "*" (.num "0.02") (.var "b")))),
            ("z", (.bin "-" (.var "omega_z") (.var "z"))),
            ("omega_z", (.bin "-" (.num "0.0") (.var "omega_z"))),
            ("phi_r", (.bin "-" (.var "omega_phi") (.var "phi_r"))),
            ("omega_phi", (.bin "+" (.bin "-" (.num "0.0") (.var "omega_phi")) (.bin "*" (.num "0.015") (.bin "+" (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))) (.bin "+" (.bin "-" (.var "y") (.bin "*" (.num "2.0") (.var "omega_y"))) (.bin "*" (.num "0.03") (.bin "+" (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))) (.bin "*" (.num "9.81") (.var "phi_r"))))))))),
            ("y", (.bin "-" (.var "omega_y") (.var "y"))),
            ("omega_y", (.bin "+" (.bin "-" (.num "0.0") (.var "omega_y")) (.bin "*" (.num "0.03") (.bin "+" (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))) (.bin "*" (.num "9.81") (.var "phi_r"))))))]
          guard := (.and (.cmp "<" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "omega_z") (.num "-0.15"))) (.cmp "<=" (.var "omega_z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.5")))
          next := ["CRUISE", "BRAKE"] },
        {
          name := "BRAKE"
          odes := [("p", (.var "v")),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("v", (.bin "-" (.bin "-" (.bin "-" (.num "0.0") (.var "b")) (.bin "*" (.num "0.003") (.bin "*" (.var "v") (.var "v")))) (.num "0.2"))),
            ("b", (.bin "*" (.num "20.0") (.bin "-" (.var "c") (.var "b")))),
            ("c", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "2.7") (.var "c")))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "-" (.num "0.0") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "+" (.bin "+" (.bin "-" (.num "0.0") (.var "omega_theta")) (.bin "*" (.num "0.5") (.var "z"))) (.bin "*" (.num "0.02") (.var "b")))),
            ("z", (.bin "-" (.var "omega_z") (.var "z"))),
            ("omega_z", (.bin "-" (.num "0.0") (.var "omega_z"))),
            ("phi_r", (.bin "-" (.var "omega_phi") (.var "phi_r"))),
            ("omega_phi", (.bin "+" (.bin "-" (.num "0.0") (.var "omega_phi")) (.bin "*" (.num "0.015") (.bin "+" (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))) (.bin "+" (.bin "-" (.var "y") (.bin "*" (.num "2.0") (.var "omega_y"))) (.bin "*" (.num "0.03") (.bin "+" (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))) (.bin "*" (.num "9.81") (.var "phi_r"))))))))),
            ("y", (.bin "-" (.var "omega_y") (.var "y"))),
            ("omega_y", (.bin "+" (.bin "-" (.num "0.0") (.var "omega_y")) (.bin "*" (.num "0.03") (.bin "+" (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))) (.bin "*" (.num "9.81") (.var "phi_r"))))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "omega_z") (.num "-0.15"))) (.cmp "<=" (.var "omega_z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.5")))
          next := ["BRAKE", "STOP"] },
        {
          name := "STOP"
          odes := [("p", (.num "0.0")),
            ("s", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.num "0.0")),
            ("c", (.num "0.0")),
            ("psi", (.num "0.0")),
            ("omega_psi", (.num "0.0")),
            ("theta_p", (.num "0.0")),
            ("omega_theta", (.num "0.0")),
            ("z", (.num "0.0")),
            ("omega_z", (.num "0.0")),
            ("phi_r", (.num "0.0")),
            ("omega_phi", (.num "0.0")),
            ("y", (.num "0.0")),
            ("omega_y", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp "<=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "omega_z") (.num "-0.15"))) (.cmp "<=" (.var "omega_z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.5")))
          next := ["STOP"] } ] }
    R := {
      stateVars := ["p", "s", "v", "b", "c", "psi", "omega_psi", "theta_p", "omega_theta", "z", "omega_z", "phi_r", "omega_phi", "y", "omega_y"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("p", (.var "v")),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("v", (.num "0.0")),
            ("b", (.bin "*" (.num "20.0") (.bin "-" (.var "c") (.var "b")))),
            ("c", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "0.0") (.var "c")))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "-" (.num "0.0") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "+" (.bin "+" (.bin "-" (.num "0.0") (.var "omega_theta")) (.bin "*" (.num "0.5") (.var "z"))) (.bin "*" (.num "0.02") (.var "b")))),
            ("z", (.bin "-" (.num "0.0") (.var "z"))),
            ("omega_z", (.num "0.0")),
            ("phi_r", (.bin "+" (.bin "-" (.num "0.0") (.var "phi_r")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi")))))),
            ("omega_phi", (.num "0.0")),
            ("y", (.num "0.0")),
            ("omega_y", (.num "0.0"))]
          guard := (.and (.cmp "<" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "omega_z") (.num "-0.15"))) (.cmp "<=" (.var "omega_z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.5")))
          next := ["CRUISE", "BRAKE"] },
        {
          name := "BRAKE"
          odes := [("p", (.var "v")),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("v", (.bin "-" (.num "0.0") (.var "b"))),
            ("b", (.bin "*" (.num "20.0") (.bin "-" (.var "c") (.var "b")))),
            ("c", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "2.7") (.var "c")))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "-" (.num "0.0") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "+" (.bin "+" (.bin "-" (.num "0.0") (.var "omega_theta")) (.bin "*" (.num "0.5") (.var "z"))) (.bin "*" (.num "0.02") (.var "b")))),
            ("z", (.bin "-" (.num "0.0") (.var "z"))),
            ("omega_z", (.num "0.0")),
            ("phi_r", (.bin "+" (.bin "-" (.num "0.0") (.var "phi_r")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi")))))),
            ("omega_phi", (.num "0.0")),
            ("y", (.num "0.0")),
            ("omega_y", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "omega_z") (.num "-0.15"))) (.cmp "<=" (.var "omega_z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.5")))
          next := ["BRAKE", "STOP"] },
        {
          name := "STOP"
          odes := [("p", (.num "0.0")),
            ("s", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.num "0.0")),
            ("c", (.num "0.0")),
            ("psi", (.num "0.0")),
            ("omega_psi", (.num "0.0")),
            ("theta_p", (.num "0.0")),
            ("omega_theta", (.num "0.0")),
            ("z", (.num "0.0")),
            ("omega_z", (.num "0.0")),
            ("phi_r", (.num "0.0")),
            ("omega_phi", (.num "0.0")),
            ("y", (.num "0.0")),
            ("omega_y", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp "<=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "c") (.num "0.0"))) (.cmp "<=" (.var "c") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "omega_z") (.num "-0.15"))) (.cmp "<=" (.var "omega_z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.5")))
          next := ["STOP"] } ] }
    invariants := [
      ("CRUISE", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_p") (.var "R_p")) (.cmp "<=" (.var "R_p") (.var "L_p"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.var "L_b") (.num "0.0"))) (.cmp "<=" (.var "L_c") (.num "0.0"))) (.cmp "<=" (.var "R_b") (.num "0.0"))) (.cmp "<=" (.var "R_c") (.num "0.0"))) (.cmp ">=" (.var "L_b") (.num "0.0"))) (.cmp ">=" (.var "L_c") (.num "0.0"))) (.cmp ">=" (.var "R_b") (.num "0.0"))) (.cmp ">=" (.var "R_c") (.num "0.0"))) (.cmp "<=" (.var "L_psi") (.num "0.35"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_theta_p"))) (.cmp "<=" (.var "L_phi_r") (.num "0.2"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.2")) (.var "L_phi_r"))) (.cmp "<=" (.var "L_omega_psi") (.num "0.35"))) (.cmp ">=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_omega_psi"))) (.cmp "<=" (.var "L_omega_theta") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_omega_theta"))) (.cmp "<=" (.var "L_omega_phi") (.num "0.2"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.2")) (.var "L_omega_phi"))) (.cmp "<=" (.var "L_y") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_y"))) (.cmp "<=" (.var "L_omega_y") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_omega_y"))) (.cmp "<=" (.bin "+" (.bin "*" (.bin "/" (.num "1.0") (.num "9.81")) (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "+" (.bin "-" (.var "L_y") (.bin "*" (.num "2.0") (.var "L_omega_y"))) (.bin "*" (.num "0.03") (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "*" (.num "9.81") (.var "L_phi_r"))))))) (.var "L_phi_r")) (.num "0.8"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.8")) (.bin "+" (.bin "*" (.bin "/" (.num "1.0") (.num "9.81")) (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "+" (.bin "-" (.var "L_y") (.bin "*" (.num "2.0") (.var "L_omega_y"))) (.bin "*" (.num "0.03") (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "*" (.num "9.81") (.var "L_phi_r"))))))) (.var "L_phi_r")))) (.cmp "<=" (.var "L_s") (.var "L_p")))),
      ("BRAKE", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "R_p") (.num "100.0")) (.cmp "<=" (.bin "+" (.bin "-" (.bin "+" (.bin "*" (.num "5.4") (.var "L_p")) (.bin "*" (.num "1.89") (.var "L_v"))) (.bin "*" (.num "0.081") (.var "L_b"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.bin "-" (.var "L_v") (.bin "*" (.num "0.05") (.var "L_b"))) (.bin "*" (.num "0.3") (.var "L_c"))) (.bin "-" (.bin "-" (.var "L_v") (.bin "*" (.num "0.05") (.var "L_b"))) (.bin "*" (.num "0.3") (.var "L_c")))))) (.bin "+" (.bin "+" (.bin "-" (.bin "+" (.bin "*" (.num "5.4") (.var "R_p")) (.bin "*" (.num "1.89") (.var "R_v"))) (.bin "*" (.num "0.081") (.var "R_b"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.bin "-" (.var "R_v") (.bin "*" (.num "0.05") (.var "R_b"))) (.bin "*" (.num "0.3") (.var "R_c"))) (.bin "-" (.bin "-" (.var "R_v") (.bin "*" (.num "0.05") (.var "R_b"))) (.bin "*" (.num "0.3") (.var "R_c")))))) (.num "0.0")))) (.cmp "<=" (.var "L_b") (.num "2.7"))) (.cmp "<=" (.var "L_c") (.num "2.7"))) (.cmp "<=" (.var "L_psi") (.num "0.35"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_theta_p"))) (.cmp "<=" (.var "L_phi_r") (.num "0.2"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.2")) (.var "L_phi_r"))) (.cmp "<=" (.var "L_omega_psi") (.num "0.35"))) (.cmp ">=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_omega_psi"))) (.cmp "<=" (.var "L_omega_theta") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_omega_theta"))) (.cmp "<=" (.var "L_omega_phi") (.num "0.2"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.2")) (.var "L_omega_phi"))) (.cmp "<=" (.var "L_y") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_y"))) (.cmp "<=" (.var "L_omega_y") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_omega_y"))) (.cmp "<=" (.bin "+" (.bin "*" (.bin "/" (.num "1.0") (.num "9.81")) (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "+" (.bin "-" (.var "L_y") (.bin "*" (.num "2.0") (.var "L_omega_y"))) (.bin "*" (.num "0.03") (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "*" (.num "9.81") (.var "L_phi_r"))))))) (.var "L_phi_r")) (.num "0.8"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.8")) (.bin "+" (.bin "*" (.bin "/" (.num "1.0") (.num "9.81")) (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "+" (.bin "-" (.var "L_y") (.bin "*" (.num "2.0") (.var "L_omega_y"))) (.bin "*" (.num "0.03") (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "*" (.num "9.81") (.var "L_phi_r"))))))) (.var "L_phi_r")))) (.cmp "<=" (.var "L_s") (.var "L_p")))),
      ("STOP", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "R_p") (.num "100.0")) (.cmp "<=" (.bin "+" (.bin "-" (.bin "+" (.bin "*" (.num "5.4") (.var "L_p")) (.bin "*" (.num "1.89") (.var "L_v"))) (.bin "*" (.num "0.081") (.var "L_b"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.bin "-" (.var "L_v") (.bin "*" (.num "0.05") (.var "L_b"))) (.bin "*" (.num "0.3") (.var "L_c"))) (.bin "-" (.bin "-" (.var "L_v") (.bin "*" (.num "0.05") (.var "L_b"))) (.bin "*" (.num "0.3") (.var "L_c")))))) (.bin "+" (.bin "+" (.bin "-" (.bin "+" (.bin "*" (.num "5.4") (.var "R_p")) (.bin "*" (.num "1.89") (.var "R_v"))) (.bin "*" (.num "0.081") (.var "R_b"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.bin "-" (.var "R_v") (.bin "*" (.num "0.05") (.var "R_b"))) (.bin "*" (.num "0.3") (.var "R_c"))) (.bin "-" (.bin "-" (.var "R_v") (.bin "*" (.num "0.05") (.var "R_b"))) (.bin "*" (.num "0.3") (.var "R_c")))))) (.num "0.0")))) (.cmp "<=" (.var "L_psi") (.num "0.35"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_theta_p"))) (.cmp "<=" (.var "L_phi_r") (.num "0.2"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.2")) (.var "L_phi_r"))) (.cmp "<=" (.var "L_omega_psi") (.num "0.35"))) (.cmp ">=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_omega_psi"))) (.cmp "<=" (.var "L_omega_theta") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_omega_theta"))) (.cmp "<=" (.var "L_omega_phi") (.num "0.2"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.2")) (.var "L_omega_phi"))) (.cmp "<=" (.var "L_y") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_y"))) (.cmp "<=" (.var "L_omega_y") (.num "0.25"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_omega_y"))) (.cmp "<=" (.bin "+" (.bin "*" (.bin "/" (.num "1.0") (.num "9.81")) (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "+" (.bin "-" (.var "L_y") (.bin "*" (.num "2.0") (.var "L_omega_y"))) (.bin "*" (.num "0.03") (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "*" (.num "9.81") (.var "L_phi_r"))))))) (.var "L_phi_r")) (.num "0.8"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.8")) (.bin "+" (.bin "*" (.bin "/" (.num "1.0") (.num "9.81")) (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "+" (.bin "-" (.var "L_y") (.bin "*" (.num "2.0") (.var "L_omega_y"))) (.bin "*" (.num "0.03") (.bin "+" (.bin "*" (.var "L_v") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "*" (.num "9.81") (.var "L_phi_r"))))))) (.var "L_phi_r")))) (.cmp "<=" (.var "L_s") (.var "L_p"))))] }

/-- The finder's witness (kind B). -/
def stopline_drag_m061_wit : RefWitE :=
  { kind := "B", u := 1, m := 1, q0 := 1, k := 5,
    wL := [(101 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (-7/20 : ℚ), (-1/2 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
    wR := [(102 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
