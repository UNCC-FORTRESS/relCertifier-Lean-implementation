import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def salt_tank_sensor_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"salt_tank_sensor", [
    ⟨"On", "Off", true, [⟨"xp", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["On"]⟩,
    ⟨"On", "Off", false, [⟨"xp", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["On"]⟩,
    ⟨"Off", "Off", true, [⟨"xp", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["On"]⟩,
    ⟨"Off", "Off", false, [⟨"xp", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["On"]⟩]⟩

end RelCertifier.Progress
