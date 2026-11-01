/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_friction_m037`: a mutant of `stopline_friction` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= (- 0.0 0.25) L_theta_p) [<=->>=]` of `benchmarks/suite_v2/stopline_friction`; file `benchmarks/refute_mutants/stopline_friction_m037/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/stopline_friction_m037/input.txt` (do not edit). -/
def stopline_friction_m037_IRm : PProblem :=
  {
    name := "stopline_friction"
    lambdaMin := "0.9"
    lambdaMax := "1.0"
    L := {
      stateVars := ["p", "s", "v", "b", "psi", "theta_p", "z", "phi_r"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("p", (.var "v")),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("v", (.num "0.0")),
            ("b", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "0.0") (.var "b")))),
            ("psi", (.bin "-" (.num "0.0") (.var "psi"))),
            ("theta_p", (.bin "+" (.bin "+" (.bin "-" (.num "0.0") (.var "theta_p")) (.bin "*" (.num "0.5") (.var "z"))) (.bin "*" (.num "0.02") (.var "b")))),
            ("z", (.bin "-" (.num "0.0") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "-" (.num "0.0") (.var "phi_r")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "-" (.num "0.0") (.var "psi"))))))]
          guard := (.and (.cmp "<" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["CRUISE", "BRAKE"] },
        {
          name := "BRAKE"
          odes := [("p", (.var "v")),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("v", (.bin "-" (.num "0.0") (.var "b"))),
            ("b", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "2.7") (.var "b")))),
            ("psi", (.bin "-" (.num "0.0") (.var "psi"))),
            ("theta_p", (.bin "+" (.bin "+" (.bin "-" (.num "0.0") (.var "theta_p")) (.bin "*" (.num "0.5") (.var "z"))) (.bin "*" (.num "0.02") (.var "b")))),
            ("z", (.bin "-" (.num "0.0") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "-" (.num "0.0") (.var "phi_r")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "-" (.num "0.0") (.var "psi"))))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["BRAKE", "STOP"] },
        {
          name := "STOP"
          odes := [("p", (.num "0.0")),
            ("s", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.num "0.0")),
            ("psi", (.num "0.0")),
            ("theta_p", (.num "0.0")),
            ("z", (.num "0.0")),
            ("phi_r", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp "<=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["STOP"] } ] }
    R := {
      stateVars := ["p", "s", "v", "b", "psi", "theta_p", "z", "phi_r"]
      epsilon := "0.1"
      modes := [
        {
          name := "CRUISE"
          odes := [("p", (.var "v")),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("v", (.num "0.0")),
            ("b", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "0.0") (.var "b")))),
            ("psi", (.bin "-" (.num "0.0") (.var "psi"))),
            ("theta_p", (.num "0.0")),
            ("z", (.num "0.0")),
            ("phi_r", (.num "0.0"))]
          guard := (.and (.cmp "<" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["CRUISE", "BRAKE"] },
        {
          name := "BRAKE"
          odes := [("p", (.var "v")),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("v", (.bin "-" (.num "0.0") (.var "b"))),
            ("b", (.bin "*" (.bin "/" (.num "1.0") (.num "0.3")) (.bin "-" (.num "3.0") (.var "b")))),
            ("psi", (.bin "-" (.num "0.0") (.var "psi"))),
            ("theta_p", (.num "0.0")),
            ("z", (.num "0.0")),
            ("phi_r", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp ">=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["BRAKE", "STOP"] },
        {
          name := "STOP"
          odes := [("p", (.num "0.0")),
            ("s", (.num "0.0")),
            ("v", (.num "0.0")),
            ("b", (.num "0.0")),
            ("psi", (.num "0.0")),
            ("theta_p", (.num "0.0")),
            ("z", (.num "0.0")),
            ("phi_r", (.num "0.0"))]
          guard := (.and (.cmp ">=" (.var "p") (.num "100.0")) (.cmp "<=" (.var "v") (.num "0.35")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "3.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["STOP"] } ] }
    invariants := [
      ("CRUISE", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_p") (.var "R_p")) (.cmp "<=" (.var "R_p") (.var "L_p"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.var "L_b") (.num "0.0"))) (.cmp "<=" (.var "R_b") (.num "0.0"))) (.cmp ">=" (.var "L_b") (.num "0.0"))) (.cmp ">=" (.var "R_b") (.num "0.0"))) (.cmp "<=" (.var "L_psi") (.num "0.35"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.num "0.25"))) (.cmp ">=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_theta_p"))) (.cmp "<=" (.var "L_phi_r") (.num "0.2"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.2")) (.var "L_phi_r"))) (.cmp "<=" (.var "L_s") (.var "L_p")))),
      ("BRAKE", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "R_p") (.num "100.0")) (.cmp "<=" (.bin "*" (.num "5.0") (.bin "+" (.bin "+" (.bin "*" (.num "5.4") (.var "L_p")) (.bin "*" (.num "1.62") (.var "L_v"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b"))) (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b"))))))) (.bin "+" (.bin "*" (.num "4.5") (.bin "+" (.bin "+" (.bin "*" (.num "6.0") (.var "R_p")) (.bin "*" (.num "1.8") (.var "R_v"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.var "R_v") (.bin "*" (.num "0.3") (.var "R_b"))) (.bin "-" (.var "R_v") (.bin "*" (.num "0.3") (.var "R_b"))))))) (.num "32.0")))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp ">=" (.var "L_b") (.bin "*" (.num "0.9") (.var "R_b")))) (.cmp "<=" (.var "L_psi") (.num "0.35"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.num "0.25"))) (.cmp ">=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_theta_p"))) (.cmp "<=" (.var "L_phi_r") (.num "0.2"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.2")) (.var "L_phi_r"))) (.cmp "<=" (.var "L_s") (.var "L_p")))),
      ("STOP", (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "R_p") (.num "100.0")) (.cmp "<=" (.bin "*" (.num "5.0") (.bin "+" (.bin "+" (.bin "*" (.num "5.4") (.var "L_p")) (.bin "*" (.num "1.62") (.var "L_v"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b"))) (.bin "-" (.var "L_v") (.bin "*" (.num "0.3") (.var "L_b"))))))) (.bin "+" (.bin "*" (.num "4.5") (.bin "+" (.bin "+" (.bin "*" (.num "6.0") (.var "R_p")) (.bin "*" (.num "1.8") (.var "R_v"))) (.bin "*" (.num "1") (.bin "*" (.bin "-" (.var "R_v") (.bin "*" (.num "0.3") (.var "R_b"))) (.bin "-" (.var "R_v") (.bin "*" (.num "0.3") (.var "R_b"))))))) (.num "32.0")))) (.cmp "<=" (.var "L_psi") (.num "0.35"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.35")) (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.num "0.25"))) (.cmp ">=" (.bin "-" (.num "0.0") (.num "0.25")) (.var "L_theta_p"))) (.cmp "<=" (.var "L_phi_r") (.num "0.2"))) (.cmp "<=" (.bin "-" (.num "0.0") (.num "0.2")) (.var "L_phi_r"))) (.cmp "<=" (.var "L_s") (.var "L_p"))))] }

/-- The finder's witness (kind B). -/
def stopline_friction_m037_wit : RefWitE :=
  { kind := "B", u := 1, m := 1, q0 := 1, k := 7,
    wL := [(101 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (0 : ℚ), (-1/4 : ℚ), (0 : ℚ), (0 : ℚ)],
    wR := [(101 : ℚ), (0 : ℚ), (2 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
