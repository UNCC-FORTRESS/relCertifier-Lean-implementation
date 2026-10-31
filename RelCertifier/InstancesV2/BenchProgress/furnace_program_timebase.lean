import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def furnace_program_timebase_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"furnace_program_timebase", [
    ⟨"PREHEAT", "HEAT", true, [⟨"s", (860 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["SOAK"]⟩,
    ⟨"HEAT", "PREHEAT", true, [⟨"s", (640 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["HEAT"]⟩,
    ⟨"HEAT", "PREHEAT", false, [⟨"s", (640 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["HEAT"]⟩,
    ⟨"SOAK", "PREHEAT", true, [⟨"s", (640 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["HEAT"]⟩,
    ⟨"SOAK", "PREHEAT", false, [⟨"s", (640 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["HEAT"]⟩,
    ⟨"SOAK", "HEAT", true, [⟨"s", (860 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["SOAK"]⟩,
    ⟨"SOAK", "HEAT", false, [⟨"s", (860 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["SOAK"]⟩]⟩

end RelCertifier.Progress
