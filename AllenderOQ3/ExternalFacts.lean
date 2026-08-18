import AllenderOQ3.Principles
import AllenderOQ3.Internal.RotationExists
import AllenderOQ3.Internal.NecklaceAssembly
import AllenderOQ3.Internal.ShortWordProblem
import AllenderOQ3.Internal.LetterWordAssembly

/-!
# Three principle signatures, all proved internally

These are the three principle signatures used by the final wrapper.  All three
are now proved internally; nothing is left in the intended trust boundary.
Keeping all three signatures preserves the audited conditional API while
exposing exactly which assumptions the final wrapper supplies.

The first principle says that zero in the candidate's minimum-rotation genus
is attained by a zero-genus rotation; finite attainment is proved below from
`Internal.exists_rotation_genus_eq`.  The second is the finite,
proof-extracted Hansen interface: a planar properly layered st-graph has a
common cyclic order of arc incidences.  Its formulation intentionally does
*not* use the weaker vertex-only HMV predicate; it is discharged below by the
necklace construction `Internal.hansenArcOrder_impl`.  The third packages the
quantitative HMV and Barrington--Therien simulation, with one modulus, depth,
and size exponent for all circuits of a fixed total width.
-/

set_option autoImplicit false

namespace AllenderOQ3

namespace External

/-- The formerly external attainment principle, now kernel-proved. -/
theorem rotationZeroPlanarity : RotationZeroPlanarityPrinciple := by
  intro n c hzero
  obtain ⟨r, hr⟩ := Internal.exists_rotation_genus_eq c
  exact ⟨r, hr.trans hzero⟩

/-- The formerly external Hansen arc-order principle, now kernel-proved from the
necklace construction of `Internal.hansenArcOrder_impl`. -/
theorem hansenArcOrder : HansenArcOrderPrinciple := by
  exact Internal.hansenArcOrder_impl

/-- The formerly external quantitative cylindrical ACC simulation, now
kernel-proved from the short-word-problem route. -/
theorem quantitativeCylindricalACC :
    QuantitativeCylindricalACCPrinciple := by
  exact Internal.quantitativeCylindricalACC_of_shortWordProblem Internal.shortWordProblemACC_impl

end External
end AllenderOQ3
