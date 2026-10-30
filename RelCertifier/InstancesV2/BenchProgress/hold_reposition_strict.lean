import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def hold_reposition_strict_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"hold_reposition_strict", [
    ⟨"Hold", "Up", true, [⟨"y", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Hold"]⟩,
    ⟨"Hold", "Up", false, [⟨"y", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Hold"]⟩]⟩

end RelCertifier.Progress
