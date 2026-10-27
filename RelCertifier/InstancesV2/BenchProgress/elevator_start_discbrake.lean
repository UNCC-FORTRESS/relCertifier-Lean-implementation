import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def elevator_start_discbrake_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"elevator_start_discbrake", [
    ⟨"UP", "LIFT", true, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 4⟩], ["UP"]⟩,
    ⟨"UP", "LIFT", false, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 4⟩], ["UP"]⟩,
    ⟨"APP", "LIFT", true, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 1⟩], ["UP"]⟩,
    ⟨"APP", "LIFT", false, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 1⟩], ["UP"]⟩,
    ⟨"STOP", "LIFT", true, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 1⟩], ["UP"]⟩,
    ⟨"STOP", "LIFT", false, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 1⟩], ["UP"]⟩]⟩

end RelCertifier.Progress
