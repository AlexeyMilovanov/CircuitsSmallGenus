import AllenderOQ3.Incidence

set_option autoImplicit false

namespace AllenderOQ3.Internal

theorem cyclicInterval_of_portSplit {alpha beta : Type} (f : alpha → beta) {xs ys : List alpha} :
    CyclicRotation xs ys → CyclicRotation (xs.map f) (ys.map f) := by
  rintro ⟨p, q, hx, hy⟩
  refine ⟨p.map f, q.map f, ?_, ?_⟩
  · rw [hx, List.map_append]
  · rw [hy, List.map_append]

end AllenderOQ3.Internal
