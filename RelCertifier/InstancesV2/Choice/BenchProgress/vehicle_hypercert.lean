import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def vehicle_hypercert_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"vehicle_hypercert", [
    ⟨"Am4", "A0", true, [⟨"v", (1 : ℚ) / 25, true, (1 : ℚ) / 1⟩], ["Am4", "Am2", "Ap2", "Ap4"]⟩,
    ⟨"Am4", "A0", false, [⟨"v", (3 : ℚ) / 5, false, (1 : ℚ) / 1⟩], ["Am4", "Am2", "Ap2", "Ap4"]⟩,
    ⟨"Am2", "A0", true, [⟨"v", (3 : ℚ) / 5, false, (1 : ℚ) / 1⟩], ["Am4", "Am2", "Ap2", "Ap4"]⟩,
    ⟨"Am2", "A0", false, [⟨"v", (3 : ℚ) / 5, false, (1 : ℚ) / 1⟩], ["Am4", "Am2", "Ap2", "Ap4"]⟩,
    ⟨"A0", "A0", true, [⟨"v", (3 : ℚ) / 5, false, (1 : ℚ) / 1⟩], ["Am4", "Am2", "Ap2", "Ap4"]⟩,
    ⟨"A0", "A0", false, [⟨"v", (3 : ℚ) / 5, false, (1 : ℚ) / 1⟩], ["Am4", "Am2", "Ap2", "Ap4"]⟩,
    ⟨"Ap2", "A0", true, [⟨"v", (3 : ℚ) / 5, false, (1 : ℚ) / 1⟩], ["Am4", "Am2", "Ap2", "Ap4"]⟩,
    ⟨"Ap2", "A0", false, [⟨"v", (3 : ℚ) / 5, false, (1 : ℚ) / 1⟩], ["Am4", "Am2", "Ap2", "Ap4"]⟩,
    ⟨"Ap4", "A0", true, [⟨"v", (3 : ℚ) / 5, false, (1 : ℚ) / 1⟩], ["Am4", "Am2", "Ap2", "Ap4"]⟩,
    ⟨"Ap4", "A0", false, [⟨"v", (3 : ℚ) / 5, false, (1 : ℚ) / 1⟩], ["Am4", "Am2", "Ap2", "Ap4"]⟩]⟩

end RelCertifier.Progress
