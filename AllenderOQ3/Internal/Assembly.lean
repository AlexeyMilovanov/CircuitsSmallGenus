import AllenderOQ3.Statement
import AllenderOQ3.Internal.Semantics

set_option autoImplicit false

namespace AllenderOQ3

/-- The planar bridge *with its parameters fixed*: at computation width `w`, modulus
`M`, depth bound `d` and size exponent `e`, every well-formed rotation-planar circuit of
computation width `≤ w` is simulated by an `ACC[M]` circuit.  This is the body of
`PlanarBridgeStatement`, named so that the parameters can be extracted once and then
used uniformly across a whole circuit family. -/
def PlanarBridgeAt (w M d e : Nat) : Prop :=
  ∀ {n} (c : ADRCircuit n),
    WellFormedADR c → RotationPlanar c → ADRHasWidthAtMost c w →
    ∃ a : ACCCircuit n M, WellFormedACC a ∧ (∀ g, a.layer g ≤ d) ∧
      a.gateCount ≤ (c.gateCount + 1) ^ e ∧
      (∀ x, ACCAccepts a x ↔ ADRAccepts c x)

def PlanarBridgeStatement : Prop :=
  ∀ w, ∃ M d e, 2 ≤ M ∧ PlanarBridgeAt w M d e

/-- At computation width `0` no gate of `c` is an AND or an OR gate; in particular the
output gate is a literal. -/
theorem output_literal_of_width_zero {n : Nat} (c : ADRCircuit n)
    (hw : ADRHasWidthAtMost c 0) :
    ∃ (i : Fin n) (b : Bool), c.kind c.output = .literal i b := by
  have hcomp : (c.kind c.output).isComputation = false := by
    by_contra hne
    have hne' : (c.kind c.output).isComputation = true := by
      simpa using hne
    have hmem : c.output ∈ Finset.univ.filter (fun g : Fin c.gateCount =>
        c.layer g = c.layer c.output ∧ (c.kind g).isComputation = true) := by
      simp [hne']
    have hcard := hw (c.layer c.output)
    have hempty : (Finset.univ.filter (fun g : Fin c.gateCount =>
        c.layer g = c.layer c.output ∧ (c.kind g).isComputation = true)) = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    rw [hempty] at hmem
    simp at hmem
  cases hk : c.kind c.output with
  | literal i b => exact ⟨i, b, rfl⟩
  | andGate => rw [hk] at hcomp; simp [ADRGate.isComputation] at hcomp
  | orGate => rw [hk] at hcomp; simp [ADRGate.isComputation] at hcomp

/-- The single-literal `ACC[2]` circuit on `n` inputs. -/
def literalACC (n : Nat) (i : Fin n) (b : Bool) : ACCCircuit n 2 where
  gateCount := 1
  output := 0
  kind := fun _ => .literal i b
  layer := fun _ => 0
  edge := fun _ _ => false

theorem wellFormedACC_literalACC {n : Nat} (i : Fin n) (b : Bool) :
    WellFormedACC (literalACC n i b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v h
    simp [literalACC] at h
  · intro g
    exact ⟨fun _ => ⟨i, b, rfl⟩, fun _ => rfl⟩
  · intro g h
    simp [literalACC] at h

theorem accAccepts_literalACC {n : Nat} (i : Fin n) (b : Bool) (x : Fin n → Bool) :
    ACCAccepts (literalACC n i b) x ↔ (if b then !(x i) else x i) = true := by
  constructor
  · rintro ⟨v, hv, hout⟩
    have h0 := hv (literalACC n i b).output
    simp only [literalACC] at h0 hout
    rw [h0] at hout
    exact hout
  · intro hb
    refine ⟨fun _ => (if b then !(x i) else x i), ?_, hb⟩
    intro g
    simp only [literalACC]

/-- Literal-output branch: if the output gate of a well-formed ADR circuit is the literal
`i` (possibly negated), then the one-gate `ACC[2]` circuit `literalACC n i b` computes the
same Boolean function. -/
theorem acc_of_literal_output {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {i : Fin n} {b : Bool} (hout : c.kind c.output = ADRGate.literal i b)
    (x : Fin n → Bool) :
    ACCAccepts (literalACC n i b) x ↔ ADRAccepts c x := by
  have hev : ADRValuation c x (Internal.evalADR c hc x) :=
    (Internal.adrValuation_iff_eq_evalADR hc).mpr rfl
  have h0 := hev c.output
  simp only [hout] at h0
  rw [accAccepts_literalACC, Internal.adrAccepts_iff hc, h0]

/-- Base case `w = 0` of `PlanarBridgeStatement`: a width-`0` ADR circuit is a single
literal, hence is computed by a one-gate `ACC[2]` circuit of depth `0` and size `1`.
The rotation-planarity hypothesis is retained to match the shape of
`PlanarBridgeStatement`, but is not needed. -/
theorem bridge_base :
    ∃ M d e, 2 ≤ M ∧ ∀ {n} (c : ADRCircuit n),
      WellFormedADR c → RotationPlanar c → ADRHasWidthAtMost c 0 →
      ∃ a : ACCCircuit n M, WellFormedACC a ∧ (∀ g, a.layer g ≤ d) ∧
        a.gateCount ≤ (c.gateCount + 1) ^ e ∧
        (∀ x, ACCAccepts a x ↔ ADRAccepts c x) := by
  refine ⟨2, 0, 0, le_refl 2, ?_⟩
  intro n c hc _ hw
  obtain ⟨i, b, hkind⟩ := output_literal_of_width_zero c hw
  refine ⟨literalACC n i b, wellFormedACC_literalACC i b, fun g => le_refl 0, ?_, ?_⟩
  · simp [literalACC]
  · intro x
    have hev : ADRValuation c x (Internal.evalADR c hc x) :=
      (Internal.adrValuation_iff_eq_evalADR hc).mpr rfl
    have h0 := hev c.output
    simp only [hkind] at h0
    rw [accAccepts_literalACC, Internal.adrAccepts_iff hc, h0]

/-- A well-formed ADR circuit is properly layered: this is exactly the first clause of
`WellFormedADR`. -/
theorem properLayered_of_wellFormed {n : Nat} {c : ADRCircuit n}
    (hc : WellFormedADR c) : ProperLayered c := hc.1

/-- Composition of external facts 2 and 3 (§7.5): for an already normalized circuit
(fan-in two, single source, single sink, total width `≤ W`) rotation planarity alone
yields the required `ACC[M]` circuit, with `M`, the depth and the size exponent uniform
in the circuit. -/
theorem bridge_of_normalized (h2 : HansenArcOrderPrinciple)
    (h3 : QuantitativeCylindricalACCPrinciple) (W : Nat) :
    ∃ M d e, 2 ≤ M ∧ ∀ {n} (c : ADRCircuit n),
      HMVNormal c → RotationPlanar c → TotalWidthAtMost c W →
      (∃! s, IsGraphSource c s) → (∃! t, IsGraphSink c t) →
      ∃ a : ACCCircuit n M, WellFormedACC a ∧ (∀ g, a.layer g ≤ d) ∧
        a.gateCount ≤ (c.gateCount + 1) ^ e ∧
        (∀ x, ACCAccepts a x ↔ ADRAccepts c x) := by
  obtain ⟨M, d, e, hM, hsim⟩ := h3 W
  refine ⟨M, d, e, hM, ?_⟩
  intro n c hnorm hplanar hwidth hsrc hsnk
  exact hsim c hnorm hwidth
    (h2 c (properLayered_of_wellFormed hnorm.1) hplanar hsrc hsnk)


end AllenderOQ3
