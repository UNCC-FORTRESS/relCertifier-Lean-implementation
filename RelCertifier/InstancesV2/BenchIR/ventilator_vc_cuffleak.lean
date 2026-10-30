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
      stateVars := ["s", "V"]
      epsilon := "0.01"
      modes := [
        {
          name := "INSP"
          odes := [("s", (.num "-1.0")),
            ("V", (.bin "-" (.num "0.376238") (.bin "*" (.num "0.049505") (.var "V"))))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.01")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "V") (.num "-0.4")))
          evolve := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "V") (.num "-0.4")))
          next := ["INSP", "EXP"] },
        {
          name := "EXP"
          odes := [("s", (.num "0.0")),
            ("V", (.bin "-" (.bin "*" (.neg (.num "1.941896")) (.var "V")) (.num "0.012232")))]
          guard := (.and (.and (.cmp "<" (.var "s") (.num "0.01")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "V") (.num "-0.4")))
          evolve := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "V") (.num "-0.4")))
          next := ["EXP"] } ] }
    R := {
      stateVars := ["s", "V"]
      epsilon := "0.01"
      modes := [
        {
          name := "INSP"
          odes := [("s", (.num "-1.0")),
            ("V", (.num "0.4"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.01")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "V") (.num "-0.4")))
          evolve := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "V") (.num "-0.4")))
          next := ["INSP", "EXP"] },
        {
          name := "EXP"
          odes := [("s", (.num "0.0")),
            ("V", (.bin "*" (.neg (.num "1.923077")) (.var "V")))]
          guard := (.and (.and (.cmp "<" (.var "s") (.num "0.01")) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "V") (.num "-0.4")))
          evolve := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "V") (.num "-0.4")))
          next := ["EXP"] } ] }
    invariants := [
      ("INSP", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_s") (.var "R_s")) (.cmp "<=" (.var "R_s") (.var "L_s"))) (.cmp "<=" (.var "L_V") (.bin "+" (.bin "+" (.var "R_V") (.num "0.004")) (.bin "*" (.num "0.15") (.var "R_V"))))) (.cmp "<=" (.var "R_V") (.bin "+" (.bin "+" (.var "L_V") (.num "0.004")) (.bin "*" (.num "0.15") (.var "R_V"))))) (.cmp "<=" (.var "L_V") (.bin "-" (.num "0.4") (.bin "*" (.num "0.4") (.var "L_s"))))) (.cmp "<=" (.var "R_V") (.bin "-" (.num "0.4") (.bin "*" (.num "0.4") (.var "R_s")))))),
      ("EXP", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_s") (.var "R_s")) (.cmp "<=" (.var "R_s") (.var "L_s"))) (.cmp "<=" (.var "L_V") (.bin "+" (.var "R_V") (.num "0.08")))) (.cmp "<=" (.var "R_V") (.bin "+" (.var "L_V") (.num "0.08")))) (.cmp "<=" (.var "L_V") (.bin "-" (.num "0.4") (.bin "*" (.num "0.4") (.var "L_s"))))) (.cmp "<=" (.var "R_V") (.bin "-" (.num "0.4") (.bin "*" (.num "0.4") (.var "R_s"))))))] }

end RelCertifier.Parse
