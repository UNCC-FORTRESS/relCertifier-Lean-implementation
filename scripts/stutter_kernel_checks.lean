/- Stutter kernel checks (docs/STUTTER-SOUNDNESS.md, 2026-10-30). Run:
`lake env lean scripts/stutter_kernel_checks.lean` (after
`lake build RelCertifier.InstancesV2.Bridge.SaltTankStutter`).
* the axioms of Theorem 3 of both stutter benchmarks and of three random others: expected
  `[propext, Classical.choice, Quot.sound, RelCertifier.z3_unsat_sound]` each;
* kernel negatives: the same IR with the key off (`stutter := false`) and the same cover
  (stretch-0 pairings) FAILS the structural gate `structOK` (`timeOK`), so no bridge instance of a
  file without the key can accept a stretch-0 pairing. A green run prints only the six axiom lines. -/
import RelCertifier.InstancesV2.Bridge.SaltTankStutter
import RelCertifier.InstancesV2.Bridge.LitNahs25SaltTank
import RelCertifier.InstancesV2.Bridge.RoverLadder6to8
import RelCertifier.InstancesV2.Bridge.Watertank
import RelCertifier.InstancesV2.Bridge.TurbineStartupGearratio
#print axioms RelCertifier.Bridge.SaltTankStutter.salt_tank_stutter_bridge
#print axioms RelCertifier.Bridge.SaltTankStutter.salt_tank_stutter_bridge_run
#print axioms RelCertifier.Bridge.LitNahs25SaltTank.lit_nahs25_salt_tank_bridge
#print axioms RelCertifier.Bridge.RoverLadder6to8.rover_ladder_6to8_bridge
#print axioms RelCertifier.Bridge.Watertank.watertank_bridge
#print axioms RelCertifier.Bridge.TurbineStartupGearratio.turbine_startup_gearratio_bridge
-- kernel negative: the demo's cover with the key off must fail the structural gate
open RelCertifier RelCertifier.Emitted in
example : structOK { RelCertifier.Bridge.SaltTankStutter.IR with stutter := false } 4
    RelCertifier.Bridge.SaltTankStutter.cov RelCertifier.Bridge.SaltTankStutter.cX = false := by
  decide +kernel
open RelCertifier RelCertifier.Emitted in
example : structOK { RelCertifier.Bridge.LitNahs25SaltTank.IR with stutter := false } 4
    RelCertifier.Bridge.LitNahs25SaltTank.cov RelCertifier.Bridge.LitNahs25SaltTank.cX = false := by
  decide +kernel
