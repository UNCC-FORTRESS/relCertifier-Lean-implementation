import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def rover_ladder_8to12_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"rover_ladder_8to12", [
    ⟨"STEEP", "STEEP", true, [⟨"v", (2 : ℚ) / 1, true, (1 : ℚ) / 2⟩, ⟨"s", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"STEEP", "STEEP", false, [⟨"v", (2 : ℚ) / 1, true, (1 : ℚ) / 2⟩, ⟨"s", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"STEEP", "MODER", true, [⟨"v", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"s", (140 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["FLAT"]⟩,
    ⟨"STEEP", "MODER", false, [⟨"v", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"s", (140 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["FLAT"]⟩,
    ⟨"MODER", "STEEP", true, [⟨"s", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"MODER", "STEEP", false, [⟨"s", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"MODER", "MODER", true, [⟨"v", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"s", (140 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["FLAT"]⟩,
    ⟨"MODER", "MODER", false, [⟨"v", (2 : ℚ) / 1, true, (1 : ℚ) / 1⟩, ⟨"s", (140 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["FLAT"]⟩,
    ⟨"FLAT", "STEEP", true, [⟨"s", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"FLAT", "STEEP", false, [⟨"s", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"FLAT", "MODER", true, [⟨"s", (140 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["FLAT"]⟩,
    ⟨"FLAT", "MODER", false, [⟨"s", (140 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["FLAT"]⟩]⟩

end RelCertifier.Progress
