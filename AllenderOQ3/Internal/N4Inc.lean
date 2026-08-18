import AllenderOQ3.Internal.N4Spec
import AllenderOQ3.Internal.IncidenceToolkit

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# The predecessor lists read off an incidence certificate

`n4Inc c cyl g` lists the predecessors of `g` in the order in which the certificate of
the transition into the layer of `g` lists the incoming arcs of `g`.  This is the ordering
along which the strips of the N4 refinement fold, and the reason the refined circuit is
again incidence-cylindrical.
-/

variable {n : Nat} (c : ADRCircuit n) (cyl : IncidenceCylinder c)

/-- The incoming arcs of a gate on a positive layer. -/
theorem n4Inc_eq_map {g : Fin c.gateCount} (h : c.layer g ≠ 0) :
    n4Inc c cyl g =
      ((cyl.transitionOrder (c.layer g - 1)).incoming
        ⟨g, by omega⟩).map (fun e => e.1.1) := by
  rw [n4Inc, dif_neg h]

theorem n4Inc_eq_nil {g : Fin c.gateCount} (h : c.layer g = 0) : n4Inc c cyl g = [] := by
  rw [n4Inc, dif_pos h]

/-- The entries of `n4Inc` are exactly the predecessors. -/
theorem n4Inc_mem_iff (hc : WellFormedADR c) (g u : Fin c.gateCount) :
    u ∈ n4Inc c cyl g ↔ c.edge u g = true := by
  by_cases h : c.layer g = 0
  · rw [n4Inc_eq_nil c cyl h]
    simp only [List.not_mem_nil, false_iff]
    intro hedge
    have := hc.1 u g hedge
    omega
  · rw [n4Inc_eq_map c cyl h]
    constructor
    · intro hu
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu
      have htarget : e.1.2 = g :=
        (((cyl.transitionOrder (c.layer g - 1)).incoming_exact ⟨g, by omega⟩ e).mp he)
      have hedge : c.edge e.1.1 e.1.2 = true := e.2.1
      rw [htarget] at hedge
      exact hedge
    · intro hedge
      have hprop : ProperLayered c := hc.1
      refine List.mem_map.mpr ⟨incomingArc hprop ⟨g, by omega⟩ hedge, ?_, rfl⟩
      exact ((cyl.transitionOrder (c.layer g - 1)).incoming_exact ⟨g, by omega⟩ _).mpr rfl

/-- `n4Inc` lists every predecessor once. -/
theorem n4Inc_nodup (g : Fin c.gateCount) : (n4Inc c cyl g).Nodup := by
  by_cases h : c.layer g = 0
  · rw [n4Inc_eq_nil c cyl h]
    exact List.nodup_nil
  · rw [n4Inc_eq_map c cyl h]
    refine ((cyl.transitionOrder (c.layer g - 1)).incoming_nodup ⟨g, by omega⟩).map_on ?_
    intro e he f hf hef
    have h1 : e.1.2 = g :=
      ((cyl.transitionOrder (c.layer g - 1)).incoming_exact ⟨g, by omega⟩ e).mp he
    have h2 : f.1.2 = g :=
      ((cyl.transitionOrder (c.layer g - 1)).incoming_exact ⟨g, by omega⟩ f).mp hf
    exact Subtype.ext (Prod.ext hef (by rw [h1, h2]))

/-- The length of `n4Inc` is the fan-in. -/
theorem n4Inc_length (hc : WellFormedADR c) (g : Fin c.gateCount) :
    (n4Inc c cyl g).length = predecessorCount c g := by
  classical
  by_cases h : c.layer g = 0
  · rw [n4Inc_eq_nil c cyl h]
    have hzero : (Finset.univ.filter fun u => c.edge u g = true) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro u _ hedge
      have := hc.1 u g hedge
      omega
    simp [predecessorCount, hzero]
  · rw [n4Inc_eq_map c cyl h, List.length_map]
    exact length_incoming_eq_predecessorCount hc.1 _ ⟨g, by omega⟩

/-- Every entry of `n4Inc g` lies on the layer below `g`. -/
theorem n4Inc_layer (hc : WellFormedADR c) (g u : Fin c.gateCount) (hu : u ∈ n4Inc c cyl g) :
    c.layer u + 1 = c.layer g :=
  hc.1 u g ((n4Inc_mem_iff c cyl hc g u).mp hu)

end AllenderOQ3.Internal
