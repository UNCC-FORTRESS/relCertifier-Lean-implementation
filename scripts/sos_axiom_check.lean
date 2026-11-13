/-
The axiom audit of an instance at `anyOracle` (`docs/SOS-ORACLE.md`): the statement
`scripts/gen_bridge.py` emits for a benchmark whose cover leaf carries the SOS marker, written
here for `watertank` next to its committed Z3-only instance, so the two axiom lines can be
compared on one benchmark. Run: `lake env lean scripts/sos_axiom_check.lean`.

Expected: `watertank_bridge` and `watertank_bridge_run` at `[propext, Classical.choice,
Quot.sound, z3_unsat_sound]`; `watertank_bridge_any` and `watertank_bridge_run_any` at the same
plus `sos_unsat_sound`.
-/
import RelCertifier.InstancesV2.Bridge.Watertank

open RelCertifier RelCertifier.Emitted RelCertifier.Bridge.Watertank

/-- `watertank_bridge` at `anyOracle`: the flow verdicts by Z3 or the exact SOS checker. -/
theorem watertank_bridge_any (hv : Verdicts IR 3 cX covM prog ce anyOracle) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : windowClaim IR 3 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records_pl_O pl_ok struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

/-- The same from a green tagged run (`relcert-bridge-verdicts` with `RELCERT_SOS_SECS` set). -/
theorem watertank_bridge_run_any {k : Option ℕ} {gP gF gQ : List (List (IForm 3))}
    (hP : bridgeGroupsPre IR 3 cX covM = some gP) (hokP : GroupsOK gP)
    (hF : bridgeGroupsFlow IR 3 cX covM prog k = some gF) (hokF : GroupsOKT gF)
    (hQ : bridgeGroupsPost IR 3 cX covM prog ce = some gQ) (hokQ : GroupsOK gQ) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : windowClaim IR 3 cX cov reg 0 1 2 dt :=
  watertank_bridge_any (verdicts_of_tagged hP hokP hF hokF hQ hokQ) dt hdt

#print axioms watertank_bridge
#print axioms watertank_bridge_run
#print axioms watertank_bridge_any
#print axioms watertank_bridge_run_any
