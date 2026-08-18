import AllenderOQ3.Internal.StartSuccBridge
import AllenderOQ3.Internal.ConstantFreeLayers
import AllenderOQ3.Internal.StartRotationLive
import AllenderOQ3.Internal.StartRotationGeoSupport

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- **GEO (the real crux, local form).**
A single constant-free layer `g` bijecting a top-free antichain `A` to `B`
preserves the cyclic start successor.
This encodes the single-winding property of the target start induced by the layer.
The source-side partial-listing issue is discharged by
`sourceOrder_length_pos_of_constantFree` and
`exists_arcWord_true_source_block`; the remaining content is the target-side
first-true cut map and its degree-one order transport. -/
theorem isCyclicStartSucc_preserved_of_constantFreeLayer (hw : 0 < w) {g : TransMonoid w}
    (hg : isConstantFreeMap w g) {A B : Finset (Config w)}
    (hA : ∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hB : ∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hAanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
    (hBanti : ∀ x ∈ B, ∀ y ∈ B, x ≤ y → x = y)
    (hbij : Set.BijOn (runTrans g) ↑A ↑B)
    (x y : Config w) (hx : x ∈ A) (hy : y ∈ A)
    (hsucc : IsCyclicStartSucc hw A x y) :
    IsCyclicStartSucc hw B (runTrans g x) (runTrans g y) := by
  have hF := exists_degree_one_lift_of_constantFreeMap hw hg hA hB hAanti hBanti hbij
  exact isCyclicStartSucc_preserved_of_degree_one_lift hw hA hB hAanti hBanti hbij hF
    x y hx hy hsucc

end Internal
end AllenderOQ3
