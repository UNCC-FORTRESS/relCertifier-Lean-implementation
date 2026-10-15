import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def vehicle_accel_copy_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"vehicle_accel_copy", [
    ⟨"Accel", "Coast", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Accel", "Coast", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Coast", "Coast", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Coast", "Coast", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Brake", "Coast", true, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩,
    ⟨"Brake", "Coast", false, [⟨"v", (0 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["Accel", "Brake"]⟩]⟩

end RelCertifier.Progress
