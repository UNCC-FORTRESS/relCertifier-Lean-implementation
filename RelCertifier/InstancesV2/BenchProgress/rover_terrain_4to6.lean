import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def rover_terrain_4to6_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"rover_terrain_4to6", [
    ⟨"GRAVEL", "MUD", true, [⟨"s", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["GRAVEL"]⟩,
    ⟨"GRAVEL", "MUD", false, [⟨"s", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["GRAVEL"]⟩,
    ⟨"PAVED", "MUD", true, [⟨"s", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["GRAVEL"]⟩,
    ⟨"PAVED", "MUD", false, [⟨"s", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["GRAVEL"]⟩,
    ⟨"PAVED", "GRAVEL", true, [⟨"s", (12 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PAVED"]⟩,
    ⟨"PAVED", "GRAVEL", false, [⟨"s", (12 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PAVED"]⟩]⟩

end RelCertifier.Progress
