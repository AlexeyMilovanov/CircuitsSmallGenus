import AllenderOQ3.Incidence

/-!
# Frozen principle signatures

The propositions in this file are the exact interfaces used by the audited
Allender OQ3 proof. Their statements are checksum-frozen independently of
the proof bodies in `ExternalFacts.lean`.
-/

set_option autoImplicit false

namespace AllenderOQ3

def RotationZeroPlanarityPrinciple : Prop :=
  ∀ {n : Nat} (c : ADRCircuit n),
    orientableCircuitGenus c = 0 → RotationPlanar c

def HansenArcOrderPrinciple : Prop :=
  ∀ {n : Nat} (c : ADRCircuit n),
    ProperLayered c →
    RotationPlanar c →
    (∃! s, IsGraphSource c s) →
    (∃! t, IsGraphSink c t) →
    Nonempty (IncidenceCylinder c)

def QuantitativeCylindricalACCPrinciple : Prop :=
  ∀ width : Nat,
    ∃ modulus depth exponent : Nat,
      2 ≤ modulus ∧
      ∀ {n : Nat} (c : ADRCircuit n),
        HMVNormal c →
        TotalWidthAtMost c width →
        Nonempty (IncidenceCylinder c) →
        ∃ a : ACCCircuit n modulus,
          WellFormedACC a ∧
          (∀ g, a.layer g ≤ depth) ∧
          a.gateCount ≤ (c.gateCount + 1) ^ exponent ∧
          (∀ x, ACCAccepts a x ↔ ADRAccepts c x)

end AllenderOQ3
