import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def rover_terrain_2to4_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"rover_terrain_2to4", [
    ⟨"MUD", "MUD", true, [⟨"v", (1 : ℚ) / 5, true, (1 : ℚ) / 8⟩, ⟨"s", (5 : ℚ) / 1, true, (1 : ℚ) / 8⟩], ["GRAVEL"]⟩,
    ⟨"MUD", "MUD", false, [⟨"v", (1 : ℚ) / 5, true, (1 : ℚ) / 8⟩, ⟨"s", (5 : ℚ) / 1, true, (1 : ℚ) / 8⟩], ["GRAVEL"]⟩,
    ⟨"MUD", "GRAVEL", true, [⟨"v", (3 : ℚ) / 10, true, (1 : ℚ) / 4⟩, ⟨"s", (12 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["PAVED"]⟩,
    ⟨"MUD", "GRAVEL", false, [⟨"v", (3 : ℚ) / 10, true, (1 : ℚ) / 4⟩, ⟨"s", (12 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["PAVED"]⟩,
    ⟨"GRAVEL", "MUD", true, [⟨"s", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["GRAVEL"]⟩,
    ⟨"GRAVEL", "MUD", false, [⟨"s", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["GRAVEL"]⟩,
    ⟨"GRAVEL", "GRAVEL", true, [⟨"v", (3 : ℚ) / 10, true, (1 : ℚ) / 4⟩, ⟨"s", (12 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["PAVED"]⟩,
    ⟨"GRAVEL", "GRAVEL", false, [⟨"v", (3 : ℚ) / 10, true, (1 : ℚ) / 4⟩, ⟨"s", (12 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["PAVED"]⟩,
    ⟨"PAVED", "MUD", true, [⟨"s", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["GRAVEL"]⟩,
    ⟨"PAVED", "MUD", false, [⟨"s", (5 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["GRAVEL"]⟩,
    ⟨"PAVED", "GRAVEL", true, [⟨"s", (12 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PAVED"]⟩,
    ⟨"PAVED", "GRAVEL", false, [⟨"s", (12 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["PAVED"]⟩]⟩

end RelCertifier.Progress
