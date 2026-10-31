import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def reactor_feed_wireless_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"reactor_feed_wireless", [
    ⟨"F1", "F3", true, [⟨"T", (60 : ℚ) / 1, false, (1 : ℚ) / 1⟩], ["F2", "F4"]⟩,
    ⟨"F1", "F4", true, [⟨"T", (60 : ℚ) / 1, false, (1 : ℚ) / 1⟩], ["F2", "F3"]⟩,
    ⟨"F2", "F4", true, [⟨"T", (25 : ℚ) / 1, true, (1 : ℚ) / 2⟩], ["F2", "F3"]⟩,
    ⟨"F3", "F1", true, [⟨"T", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["F2", "F3"]⟩,
    ⟨"F4", "F1", true, [⟨"T", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["F2", "F3"]⟩,
    ⟨"F4", "F2", true, [⟨"T", (15 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["F1", "F3"]⟩]⟩

end RelCertifier.Progress
