/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `csf21_vehicle_bus` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py csf21_vehicle_bus`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/csf21_vehicle_bus/input.txt` (do not edit). -/
def csf21_vehicle_bus_IRv2 : PProblem :=
  {
    name := "csf21_vehicle_bus"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["d", "v", "temp"]
      epsilon := "1.0"
      modes := [
        {
          name := "AccCool"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "1.0")),
            ("temp", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "39.0"))) (.cmp ">" (.bin "*" (.num "2.0") (.var "d")) (.bin "+" (.bin "+" (.bin "*" (.var "v") (.var "v")) (.bin "*" (.num "4.0") (.var "v"))) (.num "2.0"))))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccCool", "CoastCool", "BrkCool", "AccHeat"] },
        {
          name := "AccHeat"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "1.0")),
            ("temp", (.num "1.0"))]
          guard := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "39.0"))) (.cmp ">" (.bin "*" (.num "2.0") (.var "d")) (.bin "+" (.bin "+" (.bin "*" (.var "v") (.var "v")) (.bin "*" (.num "4.0") (.var "v"))) (.num "2.0"))))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccHeat", "CoastHeat", "BrkHeat", "AccCool"] },
        {
          name := "CoastCool"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "0.0")),
            ("temp", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccCool", "CoastCool", "BrkCool", "CoastHeat"] },
        {
          name := "CoastHeat"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "0.0")),
            ("temp", (.num "1.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccHeat", "CoastHeat", "BrkHeat", "CoastCool"] },
        {
          name := "BrkCool"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.bin "-" (.num "0.0") (.num "1.0"))),
            ("temp", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.cmp ">=" (.var "v") (.num "1.0"))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccCool", "CoastCool", "BrkCool", "BrkHeat"] },
        {
          name := "BrkHeat"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.bin "-" (.num "0.0") (.num "1.0"))),
            ("temp", (.num "1.0"))]
          guard := (.cmp ">=" (.var "v") (.num "1.0"))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccHeat", "CoastHeat", "BrkHeat", "BrkCool"] } ] }
    R := {
      stateVars := ["d", "v", "temp"]
      epsilon := "1.0"
      modes := [
        {
          name := "AccCoolA"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "1.0")),
            ("temp", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "39.0"))) (.cmp ">" (.bin "*" (.num "2.0") (.var "d")) (.bin "+" (.bin "+" (.bin "*" (.var "v") (.var "v")) (.bin "*" (.num "4.0") (.var "v"))) (.num "2.0"))))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccCoolA", "CoastCoolA", "BrkCoolA", "AccCoolT", "AccHeatT"] },
        {
          name := "AccCoolT"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "1.0")),
            ("temp", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "39.0"))) (.cmp ">" (.bin "*" (.num "2.0") (.var "d")) (.bin "+" (.bin "+" (.bin "*" (.var "v") (.var "v")) (.bin "*" (.num "4.0") (.var "v"))) (.num "2.0")))) (.cmp ">=" (.var "temp") (.num "20.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccCoolA", "CoastCoolA", "BrkCoolA", "AccCoolT", "AccHeatT"] },
        {
          name := "AccHeatA"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "1.0")),
            ("temp", (.num "1.0"))]
          guard := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "39.0"))) (.cmp ">" (.bin "*" (.num "2.0") (.var "d")) (.bin "+" (.bin "+" (.bin "*" (.var "v") (.var "v")) (.bin "*" (.num "4.0") (.var "v"))) (.num "2.0"))))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccHeatA", "CoastHeatA", "BrkHeatA", "AccCoolT", "AccHeatT"] },
        {
          name := "AccHeatT"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "1.0")),
            ("temp", (.num "1.0"))]
          guard := (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "39.0"))) (.cmp ">" (.bin "*" (.num "2.0") (.var "d")) (.bin "+" (.bin "+" (.bin "*" (.var "v") (.var "v")) (.bin "*" (.num "4.0") (.var "v"))) (.num "2.0")))) (.cmp "<=" (.var "temp") (.num "20.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccHeatA", "CoastHeatA", "BrkHeatA", "AccCoolT", "AccHeatT"] },
        {
          name := "CoastCoolA"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "0.0")),
            ("temp", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccCoolA", "CoastCoolA", "BrkCoolA", "CoastCoolT", "CoastHeatT"] },
        {
          name := "CoastCoolT"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "0.0")),
            ("temp", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.0"))) (.cmp ">=" (.var "temp") (.num "20.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccCoolA", "CoastCoolA", "BrkCoolA", "CoastCoolT", "CoastHeatT"] },
        {
          name := "CoastHeatA"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "0.0")),
            ("temp", (.num "1.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccHeatA", "CoastHeatA", "BrkHeatA", "CoastCoolT", "CoastHeatT"] },
        {
          name := "CoastHeatT"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.num "0.0")),
            ("temp", (.num "1.0"))]
          guard := (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.0"))) (.cmp "<=" (.var "temp") (.num "20.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccHeatA", "CoastHeatA", "BrkHeatA", "CoastCoolT", "CoastHeatT"] },
        {
          name := "BrkCoolA"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.bin "-" (.num "0.0") (.num "1.0"))),
            ("temp", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.cmp ">=" (.var "v") (.num "1.0"))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccCoolA", "CoastCoolA", "BrkCoolA", "BrkCoolT", "BrkHeatT"] },
        {
          name := "BrkCoolT"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.bin "-" (.num "0.0") (.num "1.0"))),
            ("temp", (.bin "-" (.num "0.0") (.num "1.0")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp ">=" (.var "temp") (.num "20.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccCoolA", "CoastCoolA", "BrkCoolA", "BrkCoolT", "BrkHeatT"] },
        {
          name := "BrkHeatA"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.bin "-" (.num "0.0") (.num "1.0"))),
            ("temp", (.num "1.0"))]
          guard := (.cmp ">=" (.var "v") (.num "1.0"))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccHeatA", "CoastHeatA", "BrkHeatA", "BrkCoolT", "BrkHeatT"] },
        {
          name := "BrkHeatT"
          odes := [("d", (.bin "-" (.num "0.0") (.var "v"))),
            ("v", (.bin "-" (.num "0.0") (.num "1.0"))),
            ("temp", (.num "1.0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<=" (.var "temp") (.num "20.0")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "40.0")))
          next := ["AccHeatA", "CoastHeatA", "BrkHeatA", "BrkCoolT", "BrkHeatT"] } ] }
    invariants := [
      ("AccCool", (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("AccHeat", (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("CoastCool", (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("CoastHeat", (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("BrkCool", (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v")))),
      ("BrkHeat", (.and (.and (.and (.cmp "<=" (.var "L_d") (.var "R_d")) (.cmp "<=" (.var "R_d") (.var "L_d"))) (.cmp "<=" (.var "L_v") (.var "R_v"))) (.cmp "<=" (.var "R_v") (.var "L_v"))))] }

end RelCertifier.Parse
