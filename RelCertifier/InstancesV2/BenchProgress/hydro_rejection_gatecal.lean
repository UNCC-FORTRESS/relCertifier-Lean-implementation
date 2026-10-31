import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def hydro_rejection_gatecal_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"hydro_rejection_gatecal", [
    ⟨"REJECT", "ONGRID", true, [⟨"t", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["REJECT"]⟩,
    ⟨"REJECT", "ONGRID", false, [⟨"t", (20 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["REJECT"]⟩]⟩

end RelCertifier.Progress
