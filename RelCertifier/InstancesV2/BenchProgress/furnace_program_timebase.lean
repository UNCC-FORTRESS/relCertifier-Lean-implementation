import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def furnace_program_timebase_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"furnace_program_timebase", [
    ⟨"SOAK", "PREHEAT", true, [⟨"s", (640 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["HEAT"]⟩,
    ⟨"SOAK", "PREHEAT", false, [⟨"s", (640 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["HEAT"]⟩]⟩

end RelCertifier.Progress
