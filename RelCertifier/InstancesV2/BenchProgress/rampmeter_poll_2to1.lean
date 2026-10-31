import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def rampmeter_poll_2to1_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"rampmeter_poll_2to1", [
    ⟨"R1800", "R960", true, [⟨"k", (85 : ℚ) / 2, false, (1 : ℚ) / 1⟩], ["R1200", "R720"]⟩,
    ⟨"R1800", "R720", true, [⟨"k", (85 : ℚ) / 2, false, (1 : ℚ) / 1⟩], ["R960", "R480"]⟩,
    ⟨"R1800", "R480", true, [⟨"k", (85 : ℚ) / 2, false, (1 : ℚ) / 1⟩], ["R960", "R720"]⟩,
    ⟨"R1440", "R720", true, [⟨"k", (85 : ℚ) / 2, false, (1 : ℚ) / 1⟩], ["R960", "R480"]⟩,
    ⟨"R1440", "R480", true, [⟨"k", (85 : ℚ) / 2, false, (1 : ℚ) / 1⟩], ["R960", "R720"]⟩,
    ⟨"R1200", "R480", true, [⟨"k", (14 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["R960", "R720"]⟩,
    ⟨"R960", "R1800", true, [⟨"k", (19 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["R1440", "R1200"]⟩,
    ⟨"R720", "R1800", true, [⟨"k", (19 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["R1440", "R1200"]⟩,
    ⟨"R720", "R1440", true, [⟨"k", (24 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["R1200"]⟩,
    ⟨"R480", "R1800", true, [⟨"k", (19 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["R1440", "R1200"]⟩,
    ⟨"R480", "R1440", true, [⟨"k", (24 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["R1200"]⟩,
    ⟨"R480", "R1200", true, [⟨"k", (19 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["R1440", "R960"]⟩]⟩

end RelCertifier.Progress
