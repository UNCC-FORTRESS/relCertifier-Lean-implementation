/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `antenna_track_kvretune_m036`: a mutant of `antenna_track_kvretune` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= R_x (+ L_x 0.25)) [<=->>=]` of `benchmarks/suite_v2/antenna_track_kvretune`; file `benchmarks/refute_mutants/antenna_track_kvretune_m036/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/antenna_track_kvretune_m036/input.txt` (do not edit). -/
def antenna_track_kvretune_m036_IRm : PProblem :=
  {
    name := "antenna_track_kvretune"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["t", "c", "x"]
      epsilon := "0.05"
      modes := [
        {
          name := "TRACK"
          odes := [("t", (.num "1.0")),
            ("c", (.num "-0.7")),
            ("x", (.bin "*" (.num "20") (.bin "-" (.var "c") (.var "x"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "60.0")) (.cmp ">=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "46.95"))) (.cmp "<=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "47.05"))) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          next := ["TRACK", "STOW", "STOWED"] },
        {
          name := "STOW"
          odes := [("t", (.num "1.0")),
            ("c", (.num "5.0")),
            ("x", (.bin "*" (.num "20") (.bin "-" (.var "c") (.var "x"))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "60.0")) (.cmp "<" (.var "c") (.num "90.0"))) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          next := ["STOW", "STOWED"] },
        {
          name := "STOWED"
          odes := [("t", (.num "1.0")),
            ("c", (.num "0.0")),
            ("x", (.bin "*" (.num "20") (.bin "-" (.var "c") (.var "x"))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "60.0")) (.cmp ">=" (.var "c") (.num "90.0"))) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          next := ["STOWED"] } ] }
    R := {
      stateVars := ["t", "c", "x"]
      epsilon := "0.05"
      modes := [
        {
          name := "TRACK"
          odes := [("t", (.num "1.0")),
            ("c", (.num "-0.7")),
            ("x", (.bin "*" (.num "30") (.bin "-" (.var "c") (.var "x"))))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "t") (.num "60.0")) (.cmp ">=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "46.95"))) (.cmp "<=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "47.05"))) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          next := ["TRACK", "STOW", "STOWED"] },
        {
          name := "STOW"
          odes := [("t", (.num "1.0")),
            ("c", (.num "5.0")),
            ("x", (.bin "*" (.num "30") (.bin "-" (.var "c") (.var "x"))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "60.0")) (.cmp "<" (.var "c") (.num "90.0"))) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          next := ["STOW", "STOWED"] },
        {
          name := "STOWED"
          odes := [("t", (.num "1.0")),
            ("c", (.num "0.0")),
            ("x", (.bin "*" (.num "30") (.bin "-" (.var "c") (.var "x"))))]
          guard := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "60.0")) (.cmp ">=" (.var "c") (.num "90.0"))) (.cmp ">=" (.var "t") (.num "0.0"))) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "t") (.num "0.0")) (.cmp ">=" (.var "c") (.num "-2.0"))) (.cmp "<=" (.var "c") (.num "92.0"))) (.cmp ">=" (.var "x") (.num "-2.0"))) (.cmp "<=" (.var "x") (.num "92.0")))
          next := ["STOWED"] } ] }
    invariants := [
      ("TRACK", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_c") (.var "R_c"))) (.cmp "<=" (.var "R_c") (.var "L_c"))) (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "0.035")))) (.cmp "<=" (.var "R_x") (.bin "+" (.var "L_x") (.num "0.035")))) (.cmp "<=" (.bin "-" (.var "R_x") (.var "R_c")) (.num "0.025"))) (.cmp "<=" (.bin "-" (.var "R_c") (.var "R_x")) (.num "0.0")))),
      ("STOW", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_c") (.var "R_c"))) (.cmp "<=" (.var "R_c") (.var "L_c"))) (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "0.25")))) (.cmp ">=" (.var "R_x") (.bin "+" (.var "L_x") (.num "0.25")))) (.cmp "<=" (.bin "-" (.var "R_x") (.var "R_c")) (.num "0.025"))) (.cmp "<=" (.bin "-" (.var "R_c") (.var "R_x")) (.num "0.17")))),
      ("STOWED", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_t") (.var "R_t")) (.cmp "<=" (.var "R_t") (.var "L_t"))) (.cmp "<=" (.var "L_c") (.var "R_c"))) (.cmp "<=" (.var "R_c") (.var "L_c"))) (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "0.25")))) (.cmp ">=" (.var "R_x") (.bin "+" (.var "L_x") (.num "0.25")))) (.cmp "<=" (.bin "-" (.var "R_x") (.var "R_c")) (.num "0.025"))) (.cmp "<=" (.bin "-" (.var "R_c") (.var "R_x")) (.num "0.17"))))] }

/-- The finder's witness (kind C). -/
def antenna_track_kvretune_m036_wit : RefWitE :=
  { kind := "C", u := 0, m := 1, q0 := 1, k := 0,
    wL := [(60 : ℚ), (89 : ℚ), (4453/50 : ℚ)],
    wR := [(60 : ℚ), (89 : ℚ), (3561/40 : ℚ)] }

end RelCertifier.Refute
