import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def bottling_fill_strainer_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"bottling_fill_strainer", [
    ⟨"CLOSE", "FILL", true, [⟨"V", (994 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["CLOSE"]⟩,
    ⟨"CLOSE", "FILL", false, [⟨"V", (994 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["CLOSE"]⟩]⟩

end RelCertifier.Progress
