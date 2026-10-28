import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def lit_csf21_vehicle_thermo_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"lit_csf21_vehicle_thermo", [
    ⟨"AccCool", "CoastCool", .hop, true, ["AccCool", "AccHeat"]⟩,
    ⟨"AccCool", "CoastHeat", .hop, true, ["AccCool", "AccHeat"]⟩,
    ⟨"AccCool", "BrkCool", .hop, true, ["AccCool", "AccHeat"]⟩,
    ⟨"AccCool", "BrkHeat", .hop, true, ["AccCool", "AccHeat"]⟩,
    ⟨"AccHeat", "CoastCool", .hop, true, ["AccCool", "AccHeat"]⟩,
    ⟨"AccHeat", "CoastHeat", .hop, true, ["AccCool", "AccHeat"]⟩,
    ⟨"AccHeat", "BrkCool", .hop, true, ["AccCool", "AccHeat"]⟩,
    ⟨"AccHeat", "BrkHeat", .hop, true, ["AccCool", "AccHeat"]⟩,
    ⟨"CoastCool", "AccCool", .hop, true, ["CoastCool", "CoastHeat"]⟩,
    ⟨"CoastCool", "AccHeat", .hop, true, ["CoastCool", "CoastHeat"]⟩,
    ⟨"CoastCool", "BrkCool", .hop, true, ["CoastCool", "CoastHeat"]⟩,
    ⟨"CoastCool", "BrkHeat", .hop, true, ["CoastCool", "CoastHeat"]⟩,
    ⟨"CoastHeat", "AccCool", .hop, true, ["CoastCool", "CoastHeat"]⟩,
    ⟨"CoastHeat", "AccHeat", .hop, true, ["CoastCool", "CoastHeat"]⟩,
    ⟨"CoastHeat", "BrkCool", .hop, true, ["CoastCool", "CoastHeat"]⟩,
    ⟨"CoastHeat", "BrkHeat", .hop, true, ["CoastCool", "CoastHeat"]⟩,
    ⟨"BrkCool", "AccCool", .hop, true, ["BrkCool", "BrkHeat"]⟩,
    ⟨"BrkCool", "AccHeat", .hop, true, ["BrkCool", "BrkHeat"]⟩,
    ⟨"BrkCool", "CoastCool", .hop, true, ["BrkCool", "BrkHeat"]⟩,
    ⟨"BrkCool", "CoastHeat", .hop, true, ["BrkCool", "BrkHeat"]⟩,
    ⟨"BrkHeat", "AccCool", .hop, true, ["BrkCool", "BrkHeat"]⟩,
    ⟨"BrkHeat", "AccHeat", .hop, true, ["BrkCool", "BrkHeat"]⟩,
    ⟨"BrkHeat", "CoastCool", .hop, true, ["BrkCool", "BrkHeat"]⟩,
    ⟨"BrkHeat", "CoastHeat", .hop, true, ["BrkCool", "BrkHeat"]⟩]⟩

end RelCertifier.Choice
