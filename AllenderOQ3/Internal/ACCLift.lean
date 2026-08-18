import AllenderOQ3.Internal.ModulusLift

/-!
# Lifting a recogniser to a larger modulus

The single-letter recognisers available in this development are `ACC[2]`
circuits, while the counting gadgets of the word problem need one common
modulus `M` (a multiple of the exponents of the groups involved).  This file
records the resulting packaging lemma: a recogniser of a predicate over a
modulus `m` becomes a recogniser of the same predicate over any positive
multiple `M` of `m`, at the cost of doubling the depth and multiplying the size
by `M + 2`.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- **Modulus lifting of a recogniser.**  A predicate recognised by an `ACC[m]`
circuit of depth `d` and size `size` is recognised by an `ACC[M]` circuit of
depth `2 * d + 2` and size `(M + 2) * size`, whenever `m ∣ M` and `0 < M`. -/
theorem exists_acc_modulusLift {n m M : Nat} (hdvd : m ∣ M) (hM : 0 < M)
    {d size : Nat} {P : (Fin n → Bool) → Prop}
    (h : ∃ a : ACCCircuit n m,
      WellFormedACC a ∧ (∀ q, a.layer q ≤ d) ∧ a.gateCount ≤ size ∧
        (∀ x, ACCAccepts a x ↔ P x)) :
    ∃ a : ACCCircuit n M,
      WellFormedACC a ∧ (∀ q, a.layer q ≤ 2 * d + 2) ∧ a.gateCount ≤ (M + 2) * size ∧
        (∀ x, ACCAccepts a x ↔ P x) := by
  obtain ⟨a, hwf, hlay, hsize, hacc⟩ := h
  refine ⟨accModulusLift a hdvd, wellFormedACC_accModulusLift a hdvd hwf,
    accModulusLift_layer_le hlay, ?_, fun x => ?_⟩
  · exact le_trans (accModulusLift_gateCount_le a hdvd) (Nat.mul_le_mul_left _ hsize)
  · rw [evalACC_accModulusLift_of_pos hM hwf x]
    exact hacc x

end AllenderOQ3.Internal
