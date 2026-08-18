import AllenderOQ3.Internal.Semantics

/-!
# Directed reachability and a discrete intermediate value theorem for layers

In a well-formed ADR circuit every edge raises the layer by exactly one, so the
layer function is a discrete "height" along directed paths.  This file records
the two consequences that later milestones use: reachability is monotone in the
layer, and every intermediate layer between the endpoints of a directed path is
actually realised by a vertex on that path.

Note that these statements use the *directed* relation `c.edge`, not the
symmetric `UnderlyingAdj`/`VertexReachable`.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- Directed reachability along circuit edges. -/
def EdgeReach {n : Nat} (c : ADRCircuit n) (a b : Fin c.gateCount) : Prop :=
  Relation.ReflTransGen (fun p q => c.edge p q = true) a b

theorem edgeReach_refl {n : Nat} (c : ADRCircuit n) (a : Fin c.gateCount) :
    EdgeReach c a a := Relation.ReflTransGen.refl

theorem edgeReach_tail {n : Nat} {c : ADRCircuit n} {a b d : Fin c.gateCount}
    (h : EdgeReach c a b) (he : c.edge b d = true) : EdgeReach c a d :=
  Relation.ReflTransGen.tail h he

/-- Directed reachability cannot decrease the layer. -/
theorem edgeReach_layer_le {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {a b : Fin c.gateCount} (h : EdgeReach c a b) : c.layer a ≤ c.layer b := by
  induction h with
  | refl => exact Nat.le_refl _
  | @tail b' d hab hbd ih =>
      have := hc.1 b' d hbd
      omega

/-- Discrete intermediate value theorem: any layer between the layers of the
endpoints of a directed path is attained by a vertex on that path. -/
theorem edgeReach_meets_layer {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {a b : Fin c.gateCount} (h : EdgeReach c a b) {l : Nat}
    (hlo : c.layer a ≤ l) (hhi : l ≤ c.layer b) :
    ∃ z, EdgeReach c a z ∧ EdgeReach c z b ∧ c.layer z = l := by
  induction h with
  | refl =>
      exact ⟨a, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, by omega⟩
  | @tail b' d hab hbd ih =>
      have hstep := hc.1 b' d hbd
      by_cases hcase : l ≤ c.layer b'
      · obtain ⟨z, hz1, hz2, hz3⟩ := ih hcase
        exact ⟨z, hz1, Relation.ReflTransGen.tail hz2 hbd, hz3⟩
      · refine ⟨d, Relation.ReflTransGen.tail hab hbd, Relation.ReflTransGen.refl, by omega⟩

/-- Every undirected adjacency in a well-formed circuit shifts the layer by
exactly one, in one direction or the other. -/
theorem underlyingAdj_layer_succ {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {a b : Fin c.gateCount} (h : UnderlyingAdj c a b) :
    c.layer a + 1 = c.layer b ∨ c.layer b + 1 = c.layer a := by
  rcases h.1 with hab | hba
  · exact Or.inl (hc.1 a b hab)
  · exact Or.inr (hc.1 b a hba)

/-- Discrete intermediate value theorem for the *undirected* graph: along a walk
in the underlying graph the layer changes by exactly one at each step, so every
layer between the layers of the two endpoints is realised by some vertex that is
still connected to the starting point. -/
theorem connected_meets_layer {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {u v : Fin c.gateCount} (h : VertexReachable c u v) {l : Nat}
    (hlo : min (c.layer u) (c.layer v) ≤ l) (hhi : l ≤ max (c.layer u) (c.layer v)) :
    ∃ w : Fin c.gateCount, VertexReachable c u w ∧ c.layer w = l := by
  induction h with
  | refl => exact ⟨u, Relation.ReflTransGen.refl, by omega⟩
  | @tail b d hub hbd ih =>
      have hstep := underlyingAdj_layer_succ hc hbd
      by_cases hcase : min (c.layer u) (c.layer b) ≤ l ∧ l ≤ max (c.layer u) (c.layer b)
      · obtain ⟨w, hw1, hw2⟩ := ih hcase.1 hcase.2
        exact ⟨w, hw1, hw2⟩
      · refine ⟨d, Relation.ReflTransGen.tail hub hbd, ?_⟩
        omega

end AllenderOQ3.Internal
