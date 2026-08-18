import AllenderOQ3.Internal.StGraph

/-!
# E1-B1: up/down classification of darts

In a properly layered st-graph every dart of the underlying (undirected) graph
is either *up* — it runs along a circuit edge, raising the layer by one — or
*down* — it runs against a circuit edge, lowering the layer by one.  This file
records that dichotomy, the fact that reversal swaps the two classes, and the
existence of an up-dart at every non-sink and of a down-dart at every
non-source.  These are the local ingredients of the Euler/Morse corner count
used by the Hansen arc-order argument.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace AllenderOQ3
namespace Internal

variable {n : Nat} {c : ADRCircuit n}

/-- A dart is *up* when it runs along a circuit edge. -/
def dartIsUp (d : CircuitDart c) : Bool := c.edge d.source d.target

/-- In a properly layered circuit no pair of gates is joined in both
directions. -/
theorem edge_asymm (hP : ProperLayered c) {u v : Fin c.gateCount}
    (h : c.edge u v = true) : c.edge v u = false := by
  by_contra hcon
  simp only [Bool.not_eq_false] at hcon
  have h1 := hP u v h
  have h2 := hP v u hcon
  omega

/-- The reverse edge of a down-dart is a circuit edge. -/
theorem edge_of_not_dartIsUp (d : CircuitDart c) (h : dartIsUp d = false) :
    c.edge d.target d.source = true := by
  rcases d.property.1 with hf | hb
  · exact absurd hf (by simpa [dartIsUp] using h)
  · exact hb

/-- An up-dart raises the layer by exactly one. -/
theorem layer_of_dartIsUp (hP : ProperLayered c) (d : CircuitDart c)
    (h : dartIsUp d = true) : c.layer d.target = c.layer d.source + 1 :=
  (hP _ _ h).symm

/-- A down-dart lowers the layer by exactly one. -/
theorem layer_of_not_dartIsUp (hP : ProperLayered c) (d : CircuitDart c)
    (h : dartIsUp d = false) : c.layer d.source = c.layer d.target + 1 :=
  (hP _ _ (edge_of_not_dartIsUp d h)).symm

/-- Reversing a dart swaps the up/down classes. -/
theorem dartIsUp_dartReverse (hP : ProperLayered c) (d : CircuitDart c) :
    dartIsUp (dartReverse c d) = ! dartIsUp d := by
  have hsrc : (dartReverse c d).source = d.target := rfl
  have htgt : (dartReverse c d).target = d.source := rfl
  rcases Bool.eq_false_or_eq_true (dartIsUp d) with h | h
  · have hback : c.edge d.target d.source = false :=
      edge_asymm hP (by simpa [dartIsUp] using h)
    simp only [dartIsUp] at h ⊢
    simp only [hsrc, htgt, hback, h, Bool.not_true]
  · have hback : c.edge d.target d.source = true := edge_of_not_dartIsUp d h
    simp only [dartIsUp] at h ⊢
    simp only [hsrc, htgt, hback, h, Bool.not_false]

/-- Every non-sink is the tail of an up-dart. -/
theorem exists_up_dart_of_ne_sink (hP : ProperLayered c)
    (hT : ∃! t, IsGraphSink c t) {v : Fin c.gateCount} (hNe : ¬ IsGraphSink c v) :
    ∃ d : CircuitDart c, d.source = v ∧ dartIsUp d = true := by
  obtain ⟨u, hu⟩ := exists_succ_of_ne_sink hNe
  have hvu : v ≠ u := by
    intro hEq
    have := hP v u hu
    rw [hEq] at this
    omega
  exact ⟨⟨(v, u), ⟨Or.inl hu, hvu⟩⟩, rfl, hu⟩

/-- Every non-source is the tail of a down-dart. -/
theorem exists_down_dart_of_ne_source (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) {v : Fin c.gateCount}
    (hNe : ¬ IsGraphSource c v) :
    ∃ d : CircuitDart c, d.source = v ∧ dartIsUp d = false := by
  obtain ⟨u, hu⟩ := exists_pred_of_ne_source hNe
  have huv : u ≠ v := by
    intro hEq
    have := hP u v hu
    rw [hEq] at this
    omega
  exact ⟨⟨(v, u), ⟨Or.inr hu, Ne.symm huv⟩⟩, rfl, edge_asymm hP hu⟩

/-- Every *internal* vertex — one that is neither the graph source nor the graph
sink — is simultaneously the tail of an up-dart and the tail of a down-dart.
This is the local ingredient behind `switchCount v ≥ 1` (E1-B2): a rotation
cycle at `v` that contains both an up-dart and a down-dart must switch between
the two directions at least once. -/
theorem exists_updown_dart_of_internal (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    {v : Fin c.gateCount} (hns : ¬ IsGraphSource c v) (hnt : ¬ IsGraphSink c v) :
    (∃ d : CircuitDart c, d.source = v ∧ dartIsUp d = true) ∧
      (∃ d : CircuitDart c, d.source = v ∧ dartIsUp d = false) :=
  ⟨exists_up_dart_of_ne_sink hP hT hnt, exists_down_dart_of_ne_source hP hS hns⟩

end Internal
end AllenderOQ3
