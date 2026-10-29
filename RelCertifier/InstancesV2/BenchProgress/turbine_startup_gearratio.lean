import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def turbine_startup_gearratio_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"turbine_startup_gearratio", [
    ⟨"SPINUP", "SPINUP", true, [⟨"w", (5 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["RAMP"]⟩,
    ⟨"SPINUP", "SPINUP", false, [⟨"w", (5 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["RAMP"]⟩,
    ⟨"SPINUP", "RAMP", true, [⟨"w", (69 : ℚ) / 10, true, (1 : ℚ) / 64⟩], ["GEN"]⟩,
    ⟨"SPINUP", "RAMP", false, [⟨"w", (69 : ℚ) / 10, true, (1 : ℚ) / 64⟩], ["GEN"]⟩,
    ⟨"RAMP", "SPINUP", true, [⟨"w", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["RAMP"]⟩,
    ⟨"RAMP", "SPINUP", false, [⟨"w", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["RAMP"]⟩,
    ⟨"RAMP", "RAMP", true, [⟨"w", (69 : ℚ) / 10, true, (1 : ℚ) / 64⟩], ["GEN"]⟩,
    ⟨"RAMP", "RAMP", false, [⟨"w", (69 : ℚ) / 10, true, (1 : ℚ) / 64⟩], ["GEN"]⟩,
    ⟨"GEN", "SPINUP", true, [⟨"w", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["RAMP"]⟩,
    ⟨"GEN", "SPINUP", false, [⟨"w", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["RAMP"]⟩,
    ⟨"GEN", "RAMP", true, [⟨"w", (69 : ℚ) / 10, true, (1 : ℚ) / 64⟩], ["GEN"]⟩,
    ⟨"GEN", "RAMP", false, [⟨"w", (69 : ℚ) / 10, true, (1 : ℚ) / 64⟩], ["GEN"]⟩,
    ⟨"STOP", "SPINUP", true, [⟨"w", (5 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["RAMP"]⟩,
    ⟨"STOP", "SPINUP", false, [⟨"w", (5 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["RAMP"]⟩,
    ⟨"STOP", "RAMP", true, [⟨"w", (69 : ℚ) / 10, true, (1 : ℚ) / 64⟩], ["GEN"]⟩,
    ⟨"STOP", "RAMP", false, [⟨"w", (69 : ℚ) / 10, true, (1 : ℚ) / 64⟩], ["GEN"]⟩]⟩

end RelCertifier.Progress
