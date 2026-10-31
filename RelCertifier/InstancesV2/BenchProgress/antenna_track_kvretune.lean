import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def antenna_track_kvretune_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"antenna_track_kvretune", [
    ⟨"TRACK", "STOW", true, [⟨"t", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STOWED"]⟩,
    ⟨"STOW", "TRACK", true, [⟨"t", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STOW", "STOWED"]⟩,
    ⟨"STOW", "TRACK", false, [⟨"t", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STOW", "STOWED"]⟩,
    ⟨"STOWED", "TRACK", true, [⟨"t", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STOW", "STOWED"]⟩,
    ⟨"STOWED", "TRACK", false, [⟨"t", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STOW", "STOWED"]⟩,
    ⟨"STOWED", "STOW", true, [⟨"t", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STOWED"]⟩,
    ⟨"STOWED", "STOW", false, [⟨"t", (60 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STOWED"]⟩]⟩

end RelCertifier.Progress
