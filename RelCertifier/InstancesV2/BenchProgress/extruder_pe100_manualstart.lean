import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def extruder_pe100_manualstart_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"extruder_pe100_manualstart", [
    ⟨"N1", "N3", true, [⟨"T", (206 : ℚ) / 1, false, (1 : ℚ) / 1⟩], ["N2", "N4"]⟩,
    ⟨"N1", "N4", true, [⟨"T", (206 : ℚ) / 1, false, (1 : ℚ) / 1⟩], ["N2", "N3"]⟩,
    ⟨"N2", "N4", true, [⟨"T", (186 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N2", "N3"]⟩,
    ⟨"N3", "N1", true, [⟨"T", (186 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N2", "N3"]⟩,
    ⟨"N4", "N1", true, [⟨"T", (186 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N2", "N3"]⟩,
    ⟨"N4", "N2", true, [⟨"T", (130 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["N1", "N3"]⟩]⟩

end RelCertifier.Progress
