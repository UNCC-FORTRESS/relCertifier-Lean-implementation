/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tunnel_jetfan_pairout_m027`: a mutant of `tunnel_jetfan_pairout` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= R_u (+ L_u 1.42)) [<=->>=]` of `benchmarks/suite_v2/tunnel_jetfan_pairout`; file `benchmarks/refute_mutants/tunnel_jetfan_pairout_m027/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/tunnel_jetfan_pairout_m027/input.txt` (do not edit). -/
def tunnel_jetfan_pairout_m027_IRm : PProblem :=
  {
    name := "tunnel_jetfan_pairout"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["t", "u", "c"]
      epsilon := "1"
      modes := [
        {
          name := "NORMAL"
          odes := [("t", (.num "1.0")),
            ("u", (.bin "-" (.num "0.018") (.bin "*" (.num "0.00171875") (.bin "*" (.var "u") (.var "u"))))),
            ("c", (.bin "-" (.num "0.1583") (.bin "*" (.num "0.000625") (.bin "*" (.var "u") (.var "c")))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "600")) (.cmp "<=" (.var "c") (.num "100"))) (.cmp ">=" (.var "t") (.num "0"))) (.cmp ">=" (.var "u") (.num "2.6"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "900")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0")) (.cmp ">=" (.var "u") (.num "2.6"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "900")))
          next := ["NORMAL", "FIRE"] },
        {
          name := "FIRE"
          odes := [("t", (.num "1.0")),
            ("u", (.bin "-" (.num "0.072") (.bin "*" (.num "0.00171875") (.bin "*" (.var "u") (.var "u"))))),
            ("c", (.bin "-" (.num "1.2583") (.bin "*" (.num "0.000625") (.bin "*" (.var "u") (.var "c")))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "600")) (.cmp ">=" (.var "t") (.num "0"))) (.cmp ">=" (.var "u") (.num "2.6"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "900")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0")) (.cmp ">=" (.var "u") (.num "2.6"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "900")))
          next := ["FIRE"] } ] }
    R := {
      stateVars := ["t", "u", "c"]
      epsilon := "1"
      modes := [
        {
          name := "NORMAL"
          odes := [("t", (.num "1.0")),
            ("u", (.bin "-" (.num "0.0225") (.bin "*" (.num "0.00171875") (.bin "*" (.var "u") (.var "u"))))),
            ("c", (.bin "-" (.num "0.1583") (.bin "*" (.num "0.000625") (.bin "*" (.var "u") (.var "c")))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "600")) (.cmp "<=" (.var "c") (.num "100"))) (.cmp ">=" (.var "t") (.num "0"))) (.cmp ">=" (.var "u") (.num "2.6"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "900")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0")) (.cmp ">=" (.var "u") (.num "2.6"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "900")))
          next := ["NORMAL", "FIRE"] },
        {
          name := "FIRE"
          odes := [("t", (.num "1.0")),
            ("u", (.bin "-" (.num "0.09") (.bin "*" (.num "0.00171875") (.bin "*" (.var "u") (.var "u"))))),
            ("c", (.bin "-" (.num "1.2583") (.bin "*" (.num "0.000625") (.bin "*" (.var "u") (.var "c")))))]
          guard := (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "600")) (.cmp ">=" (.var "t") (.num "0"))) (.cmp ">=" (.var "u") (.num "2.6"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "900")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0")) (.cmp ">=" (.var "u") (.num "2.6"))) (.cmp "<=" (.var "u") (.num "7.3"))) (.cmp ">=" (.var "c") (.num "0"))) (.cmp "<=" (.var "c") (.num "900")))
          next := ["FIRE"] } ] }
    invariants := [
      ("NORMAL", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_u") (.var "R_u"))) (.cmp "<=" (.var "R_u") (.bin "+" (.var "L_u") (.num "0.41")))) (.cmp "<=" (.var "R_c") (.bin "+" (.var "L_c") (.num "0.0")))) (.cmp "<=" (.var "L_c") (.bin "+" (.var "R_c") (.num "30.0")))) (.cmp ">=" (.var "L_u") (.num "3.0")))),
      ("FIRE", (.and (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_u") (.var "R_u"))) (.cmp ">=" (.var "R_u") (.bin "+" (.var "L_u") (.num "1.42")))) (.cmp ">=" (.var "L_u") (.num "3.0"))))] }

/-- The finder's witness (kind C). -/
def tunnel_jetfan_pairout_m027_wit : RefWitE :=
  { kind := "C", u := 0, m := 1, q0 := 1, k := 0,
    wL := [(600 : ℚ), (172/25 : ℚ), (0 : ℚ)],
    wR := [(600 : ℚ), (172/25 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute
