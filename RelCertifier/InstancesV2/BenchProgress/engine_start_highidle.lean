import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def engine_start_highidle_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"engine_start_highidle", [
    ⟨"STARTER", "LIGHTOFF", true, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["SELF"]⟩,
    ⟨"STARTER", "LIGHTOFF", false, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["SELF"]⟩,
    ⟨"STARTER", "SELF", true, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"STARTER", "SELF", false, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"STARTER_LOW", "STARTER", true, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"STARTER_LOW", "LIGHTOFF", true, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["SELF"]⟩,
    ⟨"STARTER_LOW", "LIGHTOFF", false, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["SELF"]⟩,
    ⟨"STARTER_LOW", "SELF", true, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"STARTER_LOW", "SELF", false, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"LIGHTOFF", "STARTER", true, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"LIGHTOFF", "STARTER", false, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"LIGHTOFF", "STARTER_LOW", true, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"LIGHTOFF", "STARTER_LOW", false, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"LIGHTOFF", "LIGHTOFF", true, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["SELF"]⟩,
    ⟨"LIGHTOFF", "LIGHTOFF", false, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["SELF"]⟩,
    ⟨"LIGHTOFF", "SELF", true, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"LIGHTOFF", "SELF", false, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"SELF", "STARTER", true, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"SELF", "STARTER", false, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"SELF", "STARTER_LOW", true, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"SELF", "STARTER_LOW", false, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"SELF", "LIGHTOFF", true, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["SELF"]⟩,
    ⟨"SELF", "LIGHTOFF", false, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["SELF"]⟩,
    ⟨"SELF", "SELF", true, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"SELF", "SELF", false, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"IDLE", "STARTER", true, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"IDLE", "STARTER", false, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"IDLE", "STARTER_LOW", true, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"IDLE", "STARTER_LOW", false, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"IDLE", "LIGHTOFF", true, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["SELF"]⟩,
    ⟨"IDLE", "LIGHTOFF", false, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["SELF"]⟩,
    ⟨"IDLE", "SELF", true, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"IDLE", "SELF", false, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"ABORT", "STARTER", true, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 2⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"ABORT", "STARTER", false, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 2⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"ABORT", "STARTER_LOW", true, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"ABORT", "STARTER_LOW", false, [⟨"n", (25 : ℚ) / 1, true, (1 : ℚ) / 32⟩], ["LIGHTOFF", "ABORT"]⟩,
    ⟨"ABORT", "LIGHTOFF", true, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["SELF"]⟩,
    ⟨"ABORT", "LIGHTOFF", false, [⟨"n", (50 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["SELF"]⟩,
    ⟨"ABORT", "SELF", true, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩,
    ⟨"ABORT", "SELF", false, [⟨"n", (60 : ℚ) / 1, true, (1 : ℚ) / 4⟩], ["IDLE"]⟩]⟩

end RelCertifier.Progress
