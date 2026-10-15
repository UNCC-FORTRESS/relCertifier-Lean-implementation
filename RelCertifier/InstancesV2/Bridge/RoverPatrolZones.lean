/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_zones` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py rover_patrol_zones`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.WellFormed.RoverPatrolZones
import RelCertifier.InstancesV2.BenchCovers.rover_patrol_zones
import RelCertifier.InstancesV2.BenchProgress.rover_patrol_zones

namespace RelCertifier.Bridge.RoverPatrolZones

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.rover_patrol_zones_IRv2
abbrev cX := Oracle.rover_patrol_zones_cutsV2X
abbrev cov := rover_patrol_zones_coverV2
abbrev prog := Progress.rover_patrol_zones_coverV2_progress
abbrev ce := Choice.ChoiceEmitE.empty "rover_patrol_zones"

theorem struct_ok : structOK IR 3 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 3 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 3 cov ce = true := by decide +kernel
theorem nR_eq : nR IR = V2RoverPatrolZonesGuarded.GrG.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR V2RoverPatrolZonesGuarded.GrG = true := by decide +kernel
theorem src_ok : edgesSrcOK IR V2RoverPatrolZonesGuarded.GrG = true := by decide +kernel

/-- The same modes in the generic automaton. -/
theorem modes_eq : ∀ q m', (grOf IR 3 (prunedOf cov)).modeAt q = some m' →
    ∃ m, V2RoverPatrolZonesGuarded.GrG.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, V2RoverPatrolZonesGuarded.GrG_modeAt q hq, rfl, rfl⟩

/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 3) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 3 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `V2RoverPatrolZonesGuarded.rover_patrol_zones_wellFormedR`. -/
theorem wellFormedR : WellFormedRIn (grOf IR 3 (prunedOf cov)) (guardR IR 3) reg (epsR IR) :=
  wellFormedR_transport (V2RoverPatrolZonesGuarded.rover_patrol_zones_wellFormedR) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

/-- **Theorem 3 of `rover_patrol_zones`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem rover_patrol_zones_bridge (hv : Verdicts IR 3 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR 3 cX cov reg 0 1 2 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR 0 1 2
    (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.RoverPatrolZones
