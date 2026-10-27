/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hydro_rejection_gatecal_m024`: a mutant of `hydro_rejection_gatecal` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= R_w (+ L_w 0.09)) [<=->>=]` of `benchmarks/suite_v2/hydro_rejection_gatecal`; file `benchmarks/refute_mutants/hydro_rejection_gatecal_m024/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/hydro_rejection_gatecal_m024/input.txt` (do not edit). -/
def hydro_rejection_gatecal_m024_IRm : PProblem :=
  {
    name := "hydro_rejection_gatecal"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["t", "g", "w"]
      epsilon := "0.1"
      modes := [
        {
          name := "ONGRID"
          odes := [("t", (.num "1.0")),
            ("g", (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.num "0.87") (.var "g")) (.bin "*" (.num "20.0") (.var "w"))))),
            ("w", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "20.0")) (.cmp ">=" (.var "w") (.num "-0.004"))) (.cmp "<=" (.var "w") (.num "0.004"))) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "g") (.num "0.0"))) (.cmp "<=" (.var "g") (.num "1.0"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "g") (.num "0.0"))) (.cmp "<=" (.var "g") (.num "1.0"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0")))
          next := ["ONGRID", "REJECT"] },
        {
          name := "REJECT"
          odes := [("t", (.num "1.0")),
            ("g", (.bin "*" (.num "0.25") (.bin "-" (.num "0.12") (.var "g")))),
            ("w", (.bin "*" (.num "0.125") (.bin "-" (.bin "-" (.var "g") (.num "0.1")) (.var "w"))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "20.0")) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "g") (.num "0.0"))) (.cmp "<=" (.var "g") (.num "1.0"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "g") (.num "0.0"))) (.cmp "<=" (.var "g") (.num "1.0"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0")))
          next := ["REJECT"] } ] }
    R := {
      stateVars := ["t", "g", "w"]
      epsilon := "0.1"
      modes := [
        {
          name := "ONGRID"
          odes := [("t", (.num "1.0")),
            ("g", (.bin "*" (.num "0.25") (.bin "-" (.bin "-" (.num "0.85") (.var "g")) (.bin "*" (.num "20.0") (.var "w"))))),
            ("w", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "20.0")) (.cmp ">=" (.var "w") (.num "-0.004"))) (.cmp "<=" (.var "w") (.num "0.004"))) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "g") (.num "0.0"))) (.cmp "<=" (.var "g") (.num "1.0"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "g") (.num "0.0"))) (.cmp "<=" (.var "g") (.num "1.0"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0")))
          next := ["ONGRID", "REJECT"] },
        {
          name := "REJECT"
          odes := [("t", (.num "1.0")),
            ("g", (.bin "*" (.num "0.25") (.bin "-" (.num "0.1") (.var "g")))),
            ("w", (.bin "*" (.num "0.125") (.bin "-" (.bin "-" (.var "g") (.num "0.1")) (.var "w"))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "20.0")) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "g") (.num "0.0"))) (.cmp "<=" (.var "g") (.num "1.0"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "g") (.num "0.0"))) (.cmp "<=" (.var "g") (.num "1.0"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "1.0")))
          next := ["REJECT"] } ] }
    invariants := [
      ("ONGRID", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_w") (.var "L_w"))) (.cmp "<=" (.var "R_g") (.bin "+" (.var "L_g") (.num "0.027")))) (.cmp "<=" (.var "L_g") (.bin "+" (.var "R_g") (.num "0.027"))))),
      ("REJECT", (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp ">=" (.var "R_w") (.bin "+" (.var "L_w") (.num "0.09")))) (.cmp "<=" (.var "L_w") (.bin "+" (.var "R_w") (.num "0.09")))) (.cmp "<=" (.var "R_g") (.bin "+" (.var "L_g") (.num "0.027")))) (.cmp "<=" (.var "L_g") (.bin "+" (.var "R_g") (.num "0.027")))))] }

/-- The finder's witness (kind C). -/
def hydro_rejection_gatecal_m024_wit : RefWitE :=
  { kind := "C", u := 0, m := 1, q0 := 1, k := 0,
    wL := [(20 : ℚ), (0 : ℚ), (191/200 : ℚ)],
    wR := [(20 : ℚ), (0 : ℚ), (191/200 : ℚ)] }

end RelCertifier.Refute
