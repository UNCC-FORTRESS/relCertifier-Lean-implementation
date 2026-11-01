import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def rover_ladder_3to6_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"rover_ladder_3to6", [
    ⟨"MODER", "STEEP", true, [⟨"s", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"MODER", "STEEP", false, [⟨"s", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"FLAT", "STEEP", true, [⟨"s", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"FLAT", "STEEP", false, [⟨"s", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["MODER"]⟩,
    ⟨"FLAT", "MODER", true, [⟨"s", (140 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["FLAT"]⟩,
    ⟨"FLAT", "MODER", false, [⟨"s", (140 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["FLAT"]⟩]⟩

end RelCertifier.Progress
