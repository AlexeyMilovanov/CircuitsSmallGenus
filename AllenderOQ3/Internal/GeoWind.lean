import AllenderOQ3.Internal.IntervalStart

/-!
# Winding data for the start map (GEO split, shared interface)

`StartWindingData hw A f` says: the members of `A` can be enumerated so that
their canonical start coordinates unroll strictly monotonically within one
period `w`, and the start coordinates of their `f`-images unroll weakly
monotonically within one period.  This is precisely "the start map weakly
preserves the cyclic order with winding number one" — the geometric content
of paper §4 — packaged as plain `Nat` data so that the degree-one lift can be
built by pure interpolation.

This file only fixes the interface; it is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- The start data of `f` on `A` unrolls monotonically within one winding. -/
def StartWindingData (hw : 0 < w) (A : Finset (Config w))
    (f : Config w → Config w) : Prop :=
  ∀ _ : A.Nonempty, ∃ (k : Nat) (_ : 0 < k) (e : Fin k → Config w)
      (S T : Fin k → Nat),
    (∀ i, e i ∈ A) ∧
    (∀ z ∈ A, ∃ i, e i = z) ∧
    (∀ i j, i < j → S i < S j) ∧
    (∀ i j, S j < S i + w) ∧
    (∀ i j, i ≤ j → T i ≤ T j) ∧
    (∀ i j, T j < T i + w) ∧
    (∀ i, S i % w = (startOf hw (e i)).val) ∧
    (∀ i, T i % w = (startOf hw (f (e i))).val)

end Internal
end AllenderOQ3
