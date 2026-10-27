/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `ventilator_vc_cuffleak` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py ventilator_vc_cuffleak`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/ventilator_vc_cuffleak/input.txt` (do not edit). -/
def ventilator_vc_cuffleak_IRv2 : PProblem :=
  {
    name := "ventilator_vc_cuffleak"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["t", "V"]
      epsilon := "0.01"
      modes := [
        {
          name := "INSP"
          odes := [("t", (.num "1.0")),
            ("V", (.bin "-" (.num "0.376238") (.bin "*" (.num "0.049505") (.var "V"))))]
          guard := (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "1.0")) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "V") (.num "-0.4"))) (.cmp "<=" (.var "V") (.num "0.404"))) (.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "V") (.num "-0.4"))) (.cmp "<=" (.var "V") (.num "0.404"))) (.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")))
          next := ["INSP", "EXP"] },
        {
          name := "EXP"
          odes := [("t", (.num "1.0")),
            ("V", (.bin "-" (.bin "*" (.neg (.num "1.941896")) (.var "V")) (.num "0.012232")))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "1.0")) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "V") (.num "-0.4"))) (.cmp "<=" (.var "V") (.num "0.404"))) (.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "V") (.num "-0.4"))) (.cmp "<=" (.var "V") (.num "0.404"))) (.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")))
          next := ["EXP"] } ] }
    R := {
      stateVars := ["t", "V"]
      epsilon := "0.01"
      modes := [
        {
          name := "INSP"
          odes := [("t", (.num "1.0")),
            ("V", (.num "0.4"))]
          guard := (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "1.0")) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "V") (.num "-0.4"))) (.cmp "<=" (.var "V") (.num "0.404"))) (.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "V") (.num "-0.4"))) (.cmp "<=" (.var "V") (.num "0.404"))) (.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")))
          next := ["INSP", "EXP"] },
        {
          name := "EXP"
          odes := [("t", (.num "1.0")),
            ("V", (.bin "*" (.neg (.num "1.923077")) (.var "V")))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "1.0")) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "V") (.num "-0.4"))) (.cmp "<=" (.var "V") (.num "0.404"))) (.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "V") (.num "-0.4"))) (.cmp "<=" (.var "V") (.num "0.404"))) (.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")))
          next := ["EXP"] } ] }
    invariants := [
      ("INSP", (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_V") (.bin "+" (.bin "+" (.var "R_V") (.num "0.004")) (.bin "*" (.num "0.15") (.var "R_V"))))) (.cmp "<=" (.var "R_V") (.bin "+" (.bin "+" (.var "L_V") (.num "0.004")) (.bin "*" (.num "0.15") (.var "R_V")))))),
      ("EXP", (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_V") (.bin "+" (.var "R_V") (.num "0.08")))) (.cmp "<=" (.var "R_V") (.bin "+" (.var "L_V") (.num "0.08")))))] }

end RelCertifier.Parse
