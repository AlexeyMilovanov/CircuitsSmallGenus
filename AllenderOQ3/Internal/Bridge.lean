import AllenderOQ3.Statement
import AllenderOQ3.Internal.Assembly
import AllenderOQ3.Internal.BridgeStep

set_option autoImplicit false

namespace AllenderOQ3

open AllenderOQ3.Internal

/-- **§7 the planar bridge.**  Induction on the computation width: the base case `w = 0`
is `Assembly.bridge_base` (a width-zero circuit is a single literal) and the induction step
is `BridgeStep.bridge_step`, which extracts the cylindrical core, refines it with N4,
compiles it with External Fact 3 and substitutes the beta ports supplied by the induction
hypothesis at width `w - 1`. -/
theorem bridge_of_principles :
    RotationZeroPlanarityPrinciple →
    HansenArcOrderPrinciple →
    QuantitativeCylindricalACCPrinciple →
    PlanarBridgeStatement := by
  intro _h1 h2 h3 w
  induction w with
  | zero => exact bridge_base
  | succ w ih =>
      obtain ⟨M₁, d₁, e₁, hM₁, hb⟩ := ih
      exact bridge_step h2 h3 (w := w + 1) hM₁ hb

end AllenderOQ3
