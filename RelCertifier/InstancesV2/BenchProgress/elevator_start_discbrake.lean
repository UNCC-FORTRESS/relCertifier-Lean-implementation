import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def elevator_start_discbrake_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"elevator_start_discbrake", [
    ⟨"LIFT", "UP", true, [⟨"z", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["APP"]⟩,
    ⟨"LIFT", "APP", true, [⟨"z", (199 : ℚ) / 10, true, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"LIFT", "APP", false, [⟨"z", (199 : ℚ) / 10, true, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"UP", "LIFT", true, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 4⟩], ["UP"]⟩,
    ⟨"UP", "LIFT", false, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 4⟩], ["UP"]⟩,
    ⟨"UP", "APP", true, [⟨"z", (199 : ℚ) / 10, true, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"APP", "LIFT", true, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 1⟩], ["UP"]⟩,
    ⟨"APP", "LIFT", false, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 1⟩], ["UP"]⟩,
    ⟨"APP", "UP", true, [⟨"z", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["APP"]⟩,
    ⟨"APP", "UP", false, [⟨"z", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["APP"]⟩,
    ⟨"STOP", "LIFT", true, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 1⟩], ["UP"]⟩,
    ⟨"STOP", "LIFT", false, [⟨"b", (19 : ℚ) / 20, true, (1 : ℚ) / 1⟩], ["UP"]⟩,
    ⟨"STOP", "UP", true, [⟨"z", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["APP"]⟩,
    ⟨"STOP", "UP", false, [⟨"z", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["APP"]⟩,
    ⟨"STOP", "APP", true, [⟨"z", (199 : ℚ) / 10, true, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"STOP", "APP", false, [⟨"z", (199 : ℚ) / 10, true, (1 : ℚ) / 1⟩], ["STOP"]⟩]⟩

end RelCertifier.Progress
