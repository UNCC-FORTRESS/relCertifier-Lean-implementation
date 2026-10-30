import RelCertifier.Trusted.ProgressEmit

namespace RelCertifier.Progress

def h2_refuel_ambientbias_coverV2_progress : RelCertifier.Progress.ProgressEmitE :=
  ⟨"h2_refuel_ambientbias", [
    ⟨"STAGE1", "STAGE1", true, [⟨"p", (18 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["STAGE2"]⟩,
    ⟨"STAGE1", "STAGE1", false, [⟨"p", (18 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["STAGE2"]⟩,
    ⟨"STAGE1", "STAGE2", true, [⟨"p", (38 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["STAGE3"]⟩,
    ⟨"STAGE1", "STAGE2", false, [⟨"p", (38 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["STAGE3"]⟩,
    ⟨"STAGE1", "STAGE3", true, [⟨"p", (58 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["TOPOFF"]⟩,
    ⟨"STAGE1", "STAGE3", false, [⟨"p", (58 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["TOPOFF"]⟩,
    ⟨"STAGE1", "TOPOFF", true, [⟨"p", (70 : ℚ) / 1, true, (1 : ℚ) / 64⟩], ["COMPLETE"]⟩,
    ⟨"STAGE1", "TOPOFF", false, [⟨"p", (70 : ℚ) / 1, true, (1 : ℚ) / 64⟩], ["COMPLETE"]⟩,
    ⟨"STAGE2", "STAGE1", true, [⟨"p", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE2"]⟩,
    ⟨"STAGE2", "STAGE1", false, [⟨"p", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE2"]⟩,
    ⟨"STAGE2", "STAGE2", true, [⟨"p", (38 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["STAGE3"]⟩,
    ⟨"STAGE2", "STAGE2", false, [⟨"p", (38 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["STAGE3"]⟩,
    ⟨"STAGE2", "STAGE3", true, [⟨"p", (58 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["TOPOFF"]⟩,
    ⟨"STAGE2", "STAGE3", false, [⟨"p", (58 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["TOPOFF"]⟩,
    ⟨"STAGE2", "TOPOFF", true, [⟨"p", (70 : ℚ) / 1, true, (1 : ℚ) / 64⟩], ["COMPLETE"]⟩,
    ⟨"STAGE2", "TOPOFF", false, [⟨"p", (70 : ℚ) / 1, true, (1 : ℚ) / 64⟩], ["COMPLETE"]⟩,
    ⟨"STAGE3", "STAGE1", true, [⟨"p", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE2"]⟩,
    ⟨"STAGE3", "STAGE1", false, [⟨"p", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE2"]⟩,
    ⟨"STAGE3", "STAGE2", true, [⟨"p", (38 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE3"]⟩,
    ⟨"STAGE3", "STAGE2", false, [⟨"p", (38 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE3"]⟩,
    ⟨"STAGE3", "STAGE3", true, [⟨"p", (58 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["TOPOFF"]⟩,
    ⟨"STAGE3", "STAGE3", false, [⟨"p", (58 : ℚ) / 1, true, (1 : ℚ) / 16⟩], ["TOPOFF"]⟩,
    ⟨"STAGE3", "TOPOFF", true, [⟨"p", (70 : ℚ) / 1, true, (1 : ℚ) / 64⟩], ["COMPLETE"]⟩,
    ⟨"STAGE3", "TOPOFF", false, [⟨"p", (70 : ℚ) / 1, true, (1 : ℚ) / 64⟩], ["COMPLETE"]⟩,
    ⟨"TOPOFF", "STAGE1", true, [⟨"p", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE2"]⟩,
    ⟨"TOPOFF", "STAGE1", false, [⟨"p", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE2"]⟩,
    ⟨"TOPOFF", "STAGE2", true, [⟨"p", (38 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE3"]⟩,
    ⟨"TOPOFF", "STAGE2", false, [⟨"p", (38 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE3"]⟩,
    ⟨"TOPOFF", "STAGE3", true, [⟨"p", (58 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["TOPOFF"]⟩,
    ⟨"TOPOFF", "STAGE3", false, [⟨"p", (58 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["TOPOFF"]⟩,
    ⟨"TOPOFF", "TOPOFF", true, [⟨"p", (70 : ℚ) / 1, true, (1 : ℚ) / 64⟩], ["COMPLETE"]⟩,
    ⟨"TOPOFF", "TOPOFF", false, [⟨"p", (70 : ℚ) / 1, true, (1 : ℚ) / 64⟩], ["COMPLETE"]⟩,
    ⟨"COMPLETE", "STAGE1", true, [⟨"p", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE2"]⟩,
    ⟨"COMPLETE", "STAGE1", false, [⟨"p", (18 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE2"]⟩,
    ⟨"COMPLETE", "STAGE2", true, [⟨"p", (38 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE3"]⟩,
    ⟨"COMPLETE", "STAGE2", false, [⟨"p", (38 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["STAGE3"]⟩,
    ⟨"COMPLETE", "STAGE3", true, [⟨"p", (58 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["TOPOFF"]⟩,
    ⟨"COMPLETE", "STAGE3", false, [⟨"p", (58 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["TOPOFF"]⟩,
    ⟨"COMPLETE", "TOPOFF", true, [⟨"p", (70 : ℚ) / 1, true, (1 : ℚ) / 64⟩], ["COMPLETE"]⟩,
    ⟨"COMPLETE", "TOPOFF", false, [⟨"p", (70 : ℚ) / 1, true, (1 : ℚ) / 64⟩], ["COMPLETE"]⟩]⟩

end RelCertifier.Progress
