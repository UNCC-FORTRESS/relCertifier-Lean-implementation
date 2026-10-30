/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `ventilator_vc_cuffleak_m028`: a mutant of `ventilator_vc_cuffleak` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= R_V (+ L_V 0.08)) [<=->>=]` of `benchmarks/suite_v2/ventilator_vc_cuffleak`; file `benchmarks/refute_mutants/ventilator_vc_cuffleak_m028/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/ventilator_vc_cuffleak_m028/input.txt` (do not edit). -/
def ventilator_vc_cuffleak_m028_IRm : PProblem :=
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
      ("EXP", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_s") (.var "R_s")) (.cmp "<=" (.var "R_s") (.var "L_s"))) (.cmp "<=" (.var "L_V") (.bin "+" (.var "R_V") (.num "0.08")))) (.cmp ">=" (.var "R_V") (.bin "+" (.var "L_V") (.num "0.08")))) (.cmp "<=" (.var "L_V") (.bin "-" (.num "0.4") (.bin "*" (.num "0.4") (.var "L_s"))))) (.cmp "<=" (.var "R_V") (.bin "-" (.num "0.4") (.bin "*" (.num "0.4") (.var "R_s"))))))] }

/-- The finder's witness (kind C). -/
def ventilator_vc_cuffleak_m028_wit : RefWitE :=
  { kind := "C", u := 0, m := 1, q0 := 1, k := 0,
    wL := [(1/200 : ℚ), (13/40 : ℚ), (0 : ℚ)],
    wR := [(1/200 : ℚ), (329/850 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
