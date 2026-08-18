import AllenderOQ3.Internal.GeoLiftGlue
import AllenderOQ3.Internal.GeoWindCore

/-!
# GEO assembly: winding data + glue close the degree-one lift

`sorry`-free modulo its two imports (G2, G3): once those close, this
discharges the GEO leaf `exists_degree_one_lift_of_constantFreeMap`.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- The GEO leaf, assembled from the winding decomposition. -/
theorem exists_degree_one_lift_of_constantFreeMap_assembled (hw : 0 < w)
    {g : TransMonoid w}
    (hg : isConstantFreeMap w g) {A B : Finset (Config w)}
    (hA : ∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hB : ∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hAanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
    (hBanti : ∀ x ∈ B, ∀ y ∈ B, x ≤ y → x = y)
    (hbij : Set.BijOn (runTrans g) ↑A ↑B) :
    ∃ (F : Nat → Nat),
      (∀ x, F (x + w) = F x + w) ∧
      (∀ x y, x ≤ y → F x ≤ F y) ∧
      (∀ x ∈ A, (F (startOf hw x).val) % w = (startOf hw (runTrans g x)).val) :=
  exists_degree_one_lift_of_startWindingData hw
    (startWindingData_of_constantFreeMap hw hg hA hB hAanti hBanti hbij)

end Internal
end AllenderOQ3
