import AllenderOQ3.ExternalFacts

/-! Frozen statements for the conditional and final theorems. -/

def AllenderOQ3ConditionalStatement : Prop :=
  AllenderOQ3.RotationZeroPlanarityPrinciple →
  AllenderOQ3.HansenArcOrderPrinciple →
  AllenderOQ3.QuantitativeCylindricalACCPrinciple →
  AllenderOQ3Statement
