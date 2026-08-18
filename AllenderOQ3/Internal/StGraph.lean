import AllenderOQ3.Internal.LayerPath
import AllenderOQ3.Internal.OrbitCount
import AllenderOQ3.Incidence

/-!
# E1-A: proper-layered st-graph preliminaries

These are the combinatorial preliminaries used by the Hansen arc-order argument
(external fact E1).  We work with `ProperLayered c` (every edge raises the layer
by exactly one) rather than the full `WellFormedADR`, and with the *directed*
reachability relation `EdgeReach`.

The main facts:

* `properLayered_acyclic` — a directed path between distinct vertices strictly
  raises the layer;
* `exists_pred_of_ne_source` / `exists_succ_of_ne_sink` — a non-source has an
  in-edge, a non-sink has an out-edge;
* `mem_st_path` — every vertex lies on a directed source→sink path;
* `source_alone_in_layer` / `sink_alone_in_layer` — the source is the only
  vertex on its layer, likewise the sink;
* `connected_of_unique_source` — the underlying graph is connected;
* `isolated_free` — with at least one edge there are no isolated vertices.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace AllenderOQ3
namespace Internal

variable {n : Nat} {c : ADRCircuit n}

/-- Along a directed path the layer is non-decreasing (the `ProperLayered`
version of `edgeReach_layer_le`). -/
theorem properLayered_layer_le (hP : ProperLayered c) {a b : Fin c.gateCount}
    (h : EdgeReach c a b) : c.layer a ≤ c.layer b := by
  induction h with
  | refl => exact Nat.le_refl _
  | @tail b' d hab hbd ih =>
      have := hP b' d hbd
      omega

/-- A directed path between distinct vertices strictly raises the layer. -/
theorem properLayered_acyclic (hP : ProperLayered c) {u v : Fin c.gateCount}
    (hR : EdgeReach c u v) (hNe : u ≠ v) : c.layer u < c.layer v := by
  have key : ∀ w, EdgeReach c u w → u = w ∨ c.layer u < c.layer w := by
    intro w hw
    induction hw with
    | refl => exact Or.inl rfl
    | @tail b' d hab hbd ih =>
        have hstep := hP b' d hbd
        rcases ih with h | h
        · subst h; exact Or.inr (by omega)
        · exact Or.inr (by omega)
  rcases key v hR with h | h
  · exact absurd h hNe
  · exact h

/-- A vertex that is not a graph source has an incoming edge. -/
theorem exists_pred_of_ne_source
    {v : Fin c.gateCount} (hNe : ¬ IsGraphSource c v) :
    ∃ u, c.edge u v = true := by
  by_contra hcon
  push_neg at hcon
  apply hNe
  unfold IsGraphSource
  intro u
  have h := hcon u
  simp only [ne_eq, Bool.not_eq_true] at h
  exact h

/-- A vertex that is not a graph sink has an outgoing edge. -/
theorem exists_succ_of_ne_sink
    {v : Fin c.gateCount} (hNe : ¬ IsGraphSink c v) :
    ∃ u, c.edge v u = true := by
  by_contra hcon
  push_neg at hcon
  apply hNe
  unfold IsGraphSink
  intro u
  have h := hcon u
  simp only [ne_eq, Bool.not_eq_true] at h
  exact h

/-- A directed path is also an undirected walk. -/
theorem vertexReachable_of_edgeReach {a b : Fin c.gateCount}
    (h : EdgeReach c a b) : VertexReachable c a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b' d hab hbd ih =>
      rcases eq_or_ne b' d with h | h
      · subst h; exact ih
      · exact Relation.ReflTransGen.tail ih ⟨Or.inl hbd, h⟩

/-- Every vertex is reachable from some graph source by a directed path. -/
theorem exists_source_reach (hP : ProperLayered c) (hS : ∃! s, IsGraphSource c s)
    (v : Fin c.gateCount) : ∃ s, IsGraphSource c s ∧ EdgeReach c s v := by
  suffices H : ∀ L, ∀ v : Fin c.gateCount, c.layer v = L →
      ∃ s, IsGraphSource c s ∧ EdgeReach c s v by
    exact H (c.layer v) v rfl
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro v hv
    by_cases hsrc : IsGraphSource c v
    · exact ⟨v, hsrc, edgeReach_refl c v⟩
    · obtain ⟨u, hu⟩ := exists_pred_of_ne_source hsrc
      have hstep := hP u v hu
      have hlt : c.layer u < L := by omega
      obtain ⟨s, hs, hsu⟩ := ih (c.layer u) hlt u rfl
      exact ⟨s, hs, edgeReach_tail hsu hu⟩

/-- Every vertex reaches some graph sink by a directed path. -/
theorem exists_sink_reach (hP : ProperLayered c) (hT : ∃! t, IsGraphSink c t)
    (v : Fin c.gateCount) : ∃ t, IsGraphSink c t ∧ EdgeReach c v t := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ g : Fin c.gateCount, c.layer g ≤ M :=
    ⟨Finset.univ.sup c.layer, fun g => Finset.le_sup (f := c.layer) (Finset.mem_univ g)⟩
  suffices H : ∀ D, ∀ v : Fin c.gateCount, M - c.layer v = D →
      ∃ t, IsGraphSink c t ∧ EdgeReach c v t by
    exact H (M - c.layer v) v rfl
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro v hv
    by_cases hsink : IsGraphSink c v
    · exact ⟨v, hsink, edgeReach_refl c v⟩
    · obtain ⟨u, hu⟩ := exists_succ_of_ne_sink hsink
      have hstep := hP v u hu
      have hlt : M - c.layer u < D := by
        have h1 := hM u
        omega
      obtain ⟨t, ht, hut⟩ := ih (M - c.layer u) hlt u rfl
      exact ⟨t, ht, Relation.ReflTransGen.head hu hut⟩

/-- Every vertex lies on a directed source→sink path. -/
theorem mem_st_path (hP : ProperLayered c) (hS : ∃! s, IsGraphSource c s)
    (hT : ∃! t, IsGraphSink c t) (v : Fin c.gateCount) :
    (∃ s, IsGraphSource c s ∧ EdgeReach c s v) ∧
      (∃ t, IsGraphSink c t ∧ EdgeReach c v t) :=
  ⟨exists_source_reach hP hS v, exists_sink_reach hP hT v⟩

/-- The graph source is the only vertex of its layer. -/
theorem source_alone_in_layer (hP : ProperLayered c) (hS : ∃! s, IsGraphSource c s)
    {s : Fin c.gateCount} (hs : IsGraphSource c s) (v : Fin c.gateCount) :
    c.layer v = c.layer s → v = s := by
  intro hlayer
  obtain ⟨s', hs', hreach⟩ := exists_source_reach hP hS v
  obtain ⟨s0, _, huniq⟩ := hS
  have heq : s' = s := (huniq s' hs').trans (huniq s hs).symm
  subst heq
  by_contra hne
  have := properLayered_acyclic hP hreach (Ne.symm hne)
  omega

/-- The graph sink is the only vertex of its layer. -/
theorem sink_alone_in_layer (hP : ProperLayered c)
    (hT : ∃! t, IsGraphSink c t)
    {t : Fin c.gateCount} (ht : IsGraphSink c t) (v : Fin c.gateCount) :
    c.layer v = c.layer t → v = t := by
  intro hlayer
  obtain ⟨t', ht', hreach⟩ := exists_sink_reach hP hT v
  obtain ⟨t0, _, huniq⟩ := hT
  have heq : t' = t := (huniq t' ht').trans (huniq t ht).symm
  subst heq
  by_contra hne
  have := properLayered_acyclic hP hreach hne
  omega

/-- Under a unique source and sink, the underlying graph is connected: every
pair of vertices is reachable. -/
theorem vertexReachable_all_of_unique_source (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) :
    ∀ u v, VertexReachable c u v := by
  obtain ⟨s, hs, huniq⟩ := hS
  have hfroms : ∀ u, VertexReachable c s u := by
    intro u
    obtain ⟨s', hs', hreach⟩ := exists_source_reach hP ⟨s, hs, huniq⟩ u
    have hs's : s' = s := huniq s' hs'
    subst hs's
    exact vertexReachable_of_edgeReach hreach
  intro u v
  exact (vertexReachable_equiv c).trans
    ((vertexReachable_equiv c).symm (hfroms u)) (hfroms v)

open Classical in
/-- Under a unique source and sink, there is exactly one connected component. -/
theorem connected_of_unique_source (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t) :
    componentCount c = 1 := by
  have hall := vertexReachable_all_of_unique_source hP hS
  refine Nat.le_antisymm ?_ (componentCount_pos c)
  dsimp [componentCount]
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hab : a.val ≤ b.val := ha b (hall a b)
  have hba : b.val ≤ a.val := hb a (hall b a)
  exact Fin.ext (Nat.le_antisymm hab hba)

open Classical in
/-- Under a unique source and sink, if at least one edge exists then there are no
isolated vertices. -/
theorem isolated_free (hP : ProperLayered c) (hS : ∃! s, IsGraphSource c s)
    (hT : ∃! t, IsGraphSink c t) (hEdges : ∃ u v, c.edge u v = true) :
    isolatedVertexCount c = 0 := by
  obtain ⟨a, b, hab⟩ := hEdges
  have hab_ne : a ≠ b := by
    intro h
    rw [h] at hab
    have := hP b b hab
    omega
  have hall := vertexReachable_all_of_unique_source hP hS
  unfold isolatedVertexCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _ hiso
  obtain ⟨w, hw⟩ : ∃ w, w ≠ u := by
    rcases eq_or_ne a u with h | h
    · exact ⟨b, fun hbu => hab_ne (h.trans hbu.symm)⟩
    · exact ⟨a, h⟩
  rcases Relation.ReflTransGen.cases_head (hall u w) with heq | ⟨z, hadj, -⟩
  · exact hw heq.symm
  · exact hiso z hadj

end Internal
end AllenderOQ3
