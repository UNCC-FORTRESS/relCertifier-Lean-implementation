import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def syringe_relay_prearm_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"syringe_relay_prearm", [
    ⟨"RUN1", "TAKEUP2", true, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["RUN2"]⟩,
    ⟨"RUN1", "RUN2", true, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["END"]⟩,
    ⟨"PREARM", "TAKEUP2", true, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["RUN2"]⟩,
    ⟨"PREARM", "RUN2", true, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["END"]⟩,
    ⟨"READY", "TAKEUP2", true, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["RUN2"]⟩,
    ⟨"READY", "RUN2", true, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["END"]⟩,
    ⟨"TAKEUP2", "RUN2", true, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["END"]⟩,
    ⟨"RUN2", "TAKEUP2", true, [⟨"b", (1 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["RUN2"]⟩,
    ⟨"RUN2", "TAKEUP2", false, [⟨"b", (1 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["RUN2"]⟩,
    ⟨"END", "RUN1", true, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["TAKEUP2", "RUN2"]⟩,
    ⟨"END", "RUN1", false, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["TAKEUP2", "RUN2"]⟩,
    ⟨"END", "TAKEUP2", true, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["RUN2"]⟩,
    ⟨"END", "TAKEUP2", false, [⟨"v1", (99 : ℚ) / 2, true, (1 : ℚ) / 1⟩], ["RUN2"]⟩]⟩

end RelCertifier.Progress
