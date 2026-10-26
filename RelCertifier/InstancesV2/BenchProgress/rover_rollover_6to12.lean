import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def rover_rollover_6to12_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"rover_rollover_6to12", [
    ⟨"STEEP", "STEEP", true, [⟨"v", (1 : ℚ) / 5, true, (1 : ℚ) / 4⟩, ⟨"s", (3 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["MODER"]⟩,
    ⟨"STEEP", "STEEP", false, [⟨"v", (1 : ℚ) / 5, true, (1 : ℚ) / 4⟩, ⟨"s", (3 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["MODER"]⟩,
    ⟨"STEEP", "MODER", true, [⟨"v", (3 : ℚ) / 10, true, (1 : ℚ) / 2⟩, ⟨"s", (7 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["FLAT"]⟩,
    ⟨"STEEP", "MODER", false, [⟨"v", (3 : ℚ) / 10, true, (1 : ℚ) / 2⟩, ⟨"s", (7 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["FLAT"]⟩,
    ⟨"MODER", "STEEP", true, [⟨"s", (3 : ℚ) / 5, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"MODER", "STEEP", false, [⟨"s", (3 : ℚ) / 5, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"MODER", "MODER", true, [⟨"v", (3 : ℚ) / 10, true, (1 : ℚ) / 2⟩, ⟨"s", (7 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["FLAT"]⟩,
    ⟨"MODER", "MODER", false, [⟨"v", (3 : ℚ) / 10, true, (1 : ℚ) / 2⟩, ⟨"s", (7 : ℚ) / 5, true, (1 : ℚ) / 8⟩], ["FLAT"]⟩,
    ⟨"FLAT", "STEEP", true, [⟨"s", (3 : ℚ) / 5, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"FLAT", "STEEP", false, [⟨"s", (3 : ℚ) / 5, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"FLAT", "MODER", true, [⟨"s", (7 : ℚ) / 5, true, (1 : ℚ) / 1⟩], ["FLAT"]⟩,
    ⟨"FLAT", "MODER", false, [⟨"s", (7 : ℚ) / 5, true, (1 : ℚ) / 1⟩], ["FLAT"]⟩]⟩

end RelCertifier.Progress
