import RelCertifier.Trusted.ChoiceEmit

namespace RelCertifier.Choice

def fuelcell_chp_dos_coverV2_choice : RelCertifier.Choice.ChoiceEmitE :=
  ⟨"fuelcell_chp_dos", [
    ⟨"LOW", "MED", .hop, true, ["LOW"]⟩,
    ⟨"HIGH", "MED", .hop, true, ["HIGH"]⟩]⟩

end RelCertifier.Choice
