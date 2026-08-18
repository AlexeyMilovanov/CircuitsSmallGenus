import AllenderOQ3.Internal.NecklaceSource
import AllenderOQ3.Principles

set_option autoImplicit false

/-!
# Assembly of the Hansen arc-order principle

The necklace words and layer listings of `CutNecklace` are fed to the proved
certificate constructor `incidenceCylinder_of_rotatedWords`.  The only open
inputs are the three genus-zero obligations stated at the end of `CutNecklace`.

The rotation-tolerant constructor is the correct one here: by
`not_doubleGrouped_crossing_four` a transition whose source and target fibres
interleave admits no single word grouped along both keys, so the stricter
`incidenceCylinder_of_words` is unusable for a general planar transition.
-/

namespace AllenderOQ3.Internal

theorem hansenArcOrder_impl : HansenArcOrderPrinciple := by
  intro n c hL hP hUS hUT
  obtain ⟨r, hr⟩ := hP
  exact incidenceCylinder_of_rotatedWords (necklaceLayerOrder hL r) (necklaceWord hL r)
    (fun ell => necklaceWord_nodup hL r ell)
    (fun ell e => necklaceWord_complete hL r hr hUS hUT ell e)
    (fun ell => necklace_groupedAlong_source hL r hr hUS hUT ell)
    (fun ell => necklace_groupedAlong_target hL r hr hUS hUT ell)

end AllenderOQ3.Internal
