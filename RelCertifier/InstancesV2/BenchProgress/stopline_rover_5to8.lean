import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def stopline_rover_5to8_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"stopline_rover_5to8", [
    ⟨"BRAKE", "BRAKE", true, [⟨"b", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"BRAKE", "BRAKE", false, [⟨"b", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"STOP", "BRAKE", true, [⟨"b", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩,
    ⟨"STOP", "BRAKE", false, [⟨"b", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"v", (7 : ℚ) / 20, false, (1 : ℚ) / 1⟩], ["STOP"]⟩]⟩

end RelCertifier.Progress
