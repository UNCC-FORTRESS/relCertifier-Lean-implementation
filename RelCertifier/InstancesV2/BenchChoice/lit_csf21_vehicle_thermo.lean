import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def lit_csf21_vehicle_thermo_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"lit_csf21_vehicle_thermo", [
    ⟨"AccCool", "BrkHeat", .repo, true, ["AccCool", "AccHeat"]⟩,
    ⟨"AccCool", "BrkCool", .repo, true, ["AccCool", "AccHeat", "BrkHeat"]⟩,
    ⟨"AccCool", "CoastHeat", .repo, true, ["AccCool", "AccHeat", "BrkCool", "BrkHeat"]⟩,
    ⟨"AccHeat", "BrkHeat", .repo, true, ["AccCool", "AccHeat"]⟩,
    ⟨"AccHeat", "BrkCool", .repo, true, ["AccCool", "AccHeat", "BrkHeat"]⟩,
    ⟨"AccHeat", "CoastHeat", .repo, true, ["AccCool", "AccHeat", "BrkCool", "BrkHeat"]⟩,
    ⟨"CoastCool", "BrkHeat", .repo, true, ["CoastCool", "CoastHeat"]⟩,
    ⟨"CoastCool", "BrkCool", .repo, true, ["CoastCool", "CoastHeat", "BrkHeat"]⟩,
    ⟨"CoastCool", "AccHeat", .repo, true, ["CoastCool", "CoastHeat", "BrkCool", "BrkHeat"]⟩,
    ⟨"CoastHeat", "BrkHeat", .repo, true, ["CoastCool", "CoastHeat"]⟩,
    ⟨"CoastHeat", "BrkCool", .repo, true, ["CoastCool", "CoastHeat", "BrkHeat"]⟩,
    ⟨"CoastHeat", "AccHeat", .repo, true, ["CoastCool", "CoastHeat", "BrkCool", "BrkHeat"]⟩,
    ⟨"BrkCool", "CoastHeat", .repo, true, ["BrkCool", "BrkHeat"]⟩,
    ⟨"BrkCool", "CoastCool", .repo, true, ["CoastHeat", "BrkCool", "BrkHeat"]⟩,
    ⟨"BrkCool", "AccHeat", .repo, true, ["CoastCool", "CoastHeat", "BrkCool", "BrkHeat"]⟩,
    ⟨"BrkHeat", "CoastHeat", .repo, true, ["BrkCool", "BrkHeat"]⟩,
    ⟨"BrkHeat", "CoastCool", .repo, true, ["CoastHeat", "BrkCool", "BrkHeat"]⟩,
    ⟨"BrkHeat", "AccHeat", .repo, true, ["CoastCool", "CoastHeat", "BrkCool", "BrkHeat"]⟩]⟩

end RelCertifier.Choice
