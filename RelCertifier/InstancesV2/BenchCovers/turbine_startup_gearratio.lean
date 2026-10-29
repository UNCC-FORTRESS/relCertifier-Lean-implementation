/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `turbine_startup_gearratio` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py turbine_startup_gearratio`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `turbine_startup_gearratio` (emitted, suite_v2, widened cut channel on). -/
def turbine_startup_gearratio_coverV2 : CoverEmitE :=
  ⟨"turbine_startup_gearratio", [("SPINUP", "STOP"), ("RAMP", "STOP")], [
    ⟨"SPINUP", (1 : ℚ) / 1, 1, [⟨"SPINUP", true, true, true⟩, ⟨"RAMP", false, true, true⟩, ⟨"GEN", true, false, false⟩, ⟨"STOP", false, false, false⟩], ["SPINUP", "RAMP", "GEN"], [⟨"SPINUP", [0], [0], [0], 1, 1⟩, ⟨"RAMP", [], [0], [0], 1, 1⟩, ⟨"GEN", [0], [], [], 1, 1⟩, ⟨"STOP", [], [], [], 1, 1⟩]⟩,
    ⟨"RAMP", (1 : ℚ) / 1, 1, [⟨"SPINUP", true, true, true⟩, ⟨"RAMP", true, true, true⟩, ⟨"GEN", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["RAMP", "GEN"], [⟨"SPINUP", [0], [0], [0], 1, 1⟩, ⟨"RAMP", [0], [0], [0], 1, 1⟩, ⟨"GEN", [0], [], [], 1, 1⟩, ⟨"STOP", [0], [], [], 1, 1⟩]⟩,
    ⟨"GEN", (1 : ℚ) / 1, 1, [⟨"SPINUP", false, true, true⟩, ⟨"RAMP", false, true, true⟩, ⟨"GEN", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["RAMP", "GEN"], [⟨"SPINUP", [], [0], [0], 1, 1⟩, ⟨"RAMP", [], [0], [0], 1, 1⟩, ⟨"GEN", [0], [], [], 1, 1⟩, ⟨"STOP", [0], [], [], 1, 1⟩]⟩,
    ⟨"STOP", (1 : ℚ) / 1, 1, [⟨"SPINUP", true, true, true⟩, ⟨"RAMP", true, true, true⟩, ⟨"GEN", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["SPINUP", "RAMP", "GEN", "STOP"], [⟨"SPINUP", [0], [0], [0], 1, 1⟩, ⟨"RAMP", [0], [0], [0], 1, 1⟩, ⟨"GEN", [0], [], [], 1, 1⟩, ⟨"STOP", [0], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
