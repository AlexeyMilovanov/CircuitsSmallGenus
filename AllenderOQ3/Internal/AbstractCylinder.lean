import AllenderOQ3.Internal.AbstractCircuit
import AllenderOQ3.Internal.FaninReducePortSplit

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# Incidence certificates on an abstract gate type, up to one rotation

`incidenceCylinder_ofSpec` asks for one arc word per transition which is grouped both
along the source order and along the target order.  A transition inherited from a given
certificate only has a *source-major* and a *target-major* word which agree up to a cyclic
rotation, so this file provides the two-word variant used by the N4 refinement.
-/

variable {n : Nat} {G : Type} [Fintype G] [DecidableEq G]

/-- **Lemma 1 of `docs/INCIDENCE_REFINEMENT.md`, two-word form.**  A source-major word and
a target-major word per transition, agreeing up to a cyclic rotation, make `ofSpec s`
incidence-cylindrical. -/
theorem incidenceCylinder_ofSpec_two (s : ADRSpec n G)
    (order : ∀ ell, CyclicListing (SpecLayerVertex s ell))
    (wordS wordT : ∀ ell, List (SpecTransitionArc s ell))
    (hrot : ∀ ell, CyclicRotation (wordS ell) (wordT ell))
    (hnodup : ∀ ell, (wordS ell).Nodup)
    (hcomplete : ∀ ell (e : SpecTransitionArc s ell), e ∈ wordS ell)
    (hS : ∀ ell, GroupedAlong specArcSource (order ell).entries (wordS ell))
    (hT : ∀ ell, GroupedAlong specArcTarget (order (ell + 1)).entries (wordT ell)) :
    Nonempty (IncidenceCylinder (ofSpec s)) := by
  classical
  refine ⟨{ layerOrder := fun ell =>
              { entries := (order ell).entries.map (specLayerVertexEquiv s ell)
                nodup := (order ell).nodup.map (specLayerVertexEquiv s ell).injective
                complete := fun v => by
                  obtain ⟨g, rfl⟩ := (specLayerVertexEquiv s ell).surjective v
                  exact List.mem_map_of_mem ((order ell).complete g) }
            transitionOrder := fun ell => ?_ }⟩
  refine arcOrderCertificate_of_rotatedDoubleGrouped
    ((order ell).entries.map (specLayerVertexEquiv s ell))
    ((order (ell + 1)).entries.map (specLayerVertexEquiv s (ell + 1)))
    ((wordS ell).map (specTransitionArcEquiv s ell))
    ((wordT ell).map (specTransitionArcEquiv s ell))
    (cyclicRotation_refl _) (cyclicRotation_refl _)
    (cyclicInterval_of_portSplit _ (hrot ell))
    ((hnodup ell).map (specTransitionArcEquiv s ell).injective) (fun e => ?_) ?_ ?_
  · obtain ⟨a, rfl⟩ := (specTransitionArcEquiv s ell).surjective e
    exact List.mem_map_of_mem (hcomplete ell a)
  · exact groupedAlong_map specArcSource arcSource (specTransitionArcEquiv s ell)
      (specLayerVertexEquiv s ell) (specLayerVertexEquiv s ell).injective
      (fun _ => rfl) _ _ (hS ell)
  · exact groupedAlong_map specArcTarget arcTarget (specTransitionArcEquiv s ell)
      (specLayerVertexEquiv s (ell + 1)) (specLayerVertexEquiv s (ell + 1)).injective
      (fun _ => rfl) _ _ (hT ell)

end AllenderOQ3.Internal
