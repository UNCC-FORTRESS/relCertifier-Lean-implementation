import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def lit_csf21_vehicle_bus_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"lit_csf21_vehicle_bus", [
    ⟨"AccCool", "BrkHeatA", .repo, true, ["AccHeatA"]⟩,
    ⟨"AccCool", "CoastHeatT", .repo, true, ["AccHeatA", "BrkHeatA"]⟩,
    ⟨"AccCool", "CoastCoolT", .repo, true, ["AccCoolA", "CoastHeatT"]⟩,
    ⟨"AccCool", "BrkHeatT", .repo, true, ["AccHeatA", "CoastHeatA", "BrkHeatA"]⟩,
    ⟨"AccCool", "BrkCoolT", .repo, true, ["AccCoolA", "BrkHeatT"]⟩,
    ⟨"AccCool", "BrkCoolA", .repo, true, ["AccCoolA", "BrkCoolT", "BrkHeatT"]⟩,
    ⟨"AccHeat", "BrkHeatA", .repo, true, ["AccHeatA"]⟩,
    ⟨"AccHeat", "CoastHeatT", .repo, true, ["AccHeatA", "BrkHeatA"]⟩,
    ⟨"AccHeat", "CoastCoolT", .repo, true, ["AccCoolA", "CoastHeatT"]⟩,
    ⟨"AccHeat", "BrkHeatT", .repo, true, ["AccHeatA", "CoastHeatA", "BrkHeatA"]⟩,
    ⟨"AccHeat", "BrkCoolT", .repo, true, ["AccCoolA", "BrkHeatT"]⟩,
    ⟨"AccHeat", "BrkCoolA", .repo, true, ["AccCoolA", "BrkCoolT", "BrkHeatT"]⟩,
    ⟨"CoastCool", "BrkHeatA", .repo, true, ["CoastHeatA"]⟩,
    ⟨"CoastCool", "AccHeatT", .repo, true, ["CoastHeatA", "BrkHeatA"]⟩,
    ⟨"CoastCool", "AccCoolT", .repo, true, ["CoastCoolA", "AccHeatT"]⟩,
    ⟨"CoastCool", "BrkHeatT", .repo, true, ["AccHeatA", "CoastHeatA", "BrkHeatA"]⟩,
    ⟨"CoastCool", "BrkCoolT", .repo, true, ["CoastCoolA", "BrkHeatT"]⟩,
    ⟨"CoastCool", "BrkCoolA", .repo, true, ["CoastCoolA", "BrkCoolT", "BrkHeatT"]⟩,
    ⟨"CoastHeat", "BrkHeatA", .repo, true, ["CoastHeatA"]⟩,
    ⟨"CoastHeat", "AccHeatT", .repo, true, ["CoastHeatA", "BrkHeatA"]⟩,
    ⟨"CoastHeat", "AccCoolT", .repo, true, ["CoastCoolA", "AccHeatT"]⟩,
    ⟨"CoastHeat", "BrkHeatT", .repo, true, ["AccHeatA", "CoastHeatA", "BrkHeatA"]⟩,
    ⟨"CoastHeat", "BrkCoolT", .repo, true, ["CoastCoolA", "BrkHeatT"]⟩,
    ⟨"CoastHeat", "BrkCoolA", .repo, true, ["CoastCoolA", "BrkCoolT", "BrkHeatT"]⟩,
    ⟨"BrkCool", "CoastHeatA", .repo, true, ["BrkHeatA"]⟩,
    ⟨"BrkCool", "AccHeatT", .repo, true, ["CoastHeatA", "BrkHeatA"]⟩,
    ⟨"BrkCool", "AccCoolT", .repo, true, ["BrkCoolA", "AccHeatT"]⟩,
    ⟨"BrkCool", "CoastHeatT", .repo, true, ["AccHeatA", "CoastHeatA", "BrkHeatA"]⟩,
    ⟨"BrkCool", "CoastCoolT", .repo, true, ["BrkCoolA", "CoastHeatT"]⟩,
    ⟨"BrkCool", "CoastCoolA", .repo, true, ["BrkCoolA", "CoastCoolT", "CoastHeatT"]⟩,
    ⟨"BrkHeat", "CoastHeatA", .repo, true, ["BrkHeatA"]⟩,
    ⟨"BrkHeat", "AccHeatT", .repo, true, ["CoastHeatA", "BrkHeatA"]⟩,
    ⟨"BrkHeat", "AccCoolT", .repo, true, ["BrkCoolA", "AccHeatT"]⟩,
    ⟨"BrkHeat", "CoastHeatT", .repo, true, ["AccHeatA", "CoastHeatA", "BrkHeatA"]⟩,
    ⟨"BrkHeat", "CoastCoolT", .repo, true, ["BrkCoolA", "CoastHeatT"]⟩,
    ⟨"BrkHeat", "CoastCoolA", .repo, true, ["BrkCoolA", "CoastCoolT", "CoastHeatT"]⟩]⟩

end RelCertifier.Choice
