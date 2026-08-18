import AllenderOQ3.Internal.ConfigInterval
import AllenderOQ3.Internal.NonCrossingDefs
import AllenderOQ3.Internal.NonCrossingCyclic
import AllenderOQ3.Internal.IncidenceToolkit

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)

/-
The statement originally recorded in this file was

```
theorem predecessor_set_is_cyclic_interval (ell : Nat)
    (h1 : (cert.layerOrder ell).entries.length = w)
    (h2 : (cert.layerOrder (ell + 1)).entries.length = w)
    (v : LayerVertex c (ell + 1)) :
    ∃ (start : Fin w) (len : Nat),
      0 < len ∧ len ≤ w ∧
      (∀ k : Nat, k < len →
        c.edge (vtxAt c cert ell h1 (finShift k start)).val v.val = true) ∧
      (len < w → c.edge (vtxAt c cert ell h1 (finShift len start)).val v.val = false) ∧
      (len < w → c.edge (vtxAt c cert ell h1 (finPred start)).val v.val = false) := by
  sorry
```

It is **false as stated**: the conclusion asserts `0 < len` together with an edge into `v`
from the position `finShift 0 start = start`, so it forces every layer-`(ell+1)` vertex to
have at least one predecessor.  Nothing in `ADRCircuit` or in `IncidenceCylinder` implies
that — an edge-free circuit is incidence-cylindrical (`incidenceCylinder_of_edgeFree`) and
has no predecessors at all.  This is refuted below in
`predecessor_set_is_cyclic_interval_false`.

The corrected statement, `predecessor_set_is_cyclic_interval`, adds the missing
non-degeneracy hypothesis that `v` has a predecessor in layer `ell`, which is exactly what
the conclusion needs; the hypothesis `h2` of the original statement plays no role and has
been dropped.
-/

/-- **The predecessor set of a layer vertex contains a maximal cyclic interval.**

`v` is a vertex of layer `ell + 1` with at least one predecessor at position `j` of the
cyclic order of layer `ell`.  Then the indicator configuration of the predecessors of `v`
has a maximal cyclic block of `true`s: a starting position `start` and a length `len` with
`0 < len ≤ w` such that positions `start, …, start + len - 1` are predecessors of `v`, while
positions `start + len` and `start - 1` are not (unless the block is all of `Fin w`).

The hypothesis that `v` has a predecessor is necessary: see
`predecessor_set_is_cyclic_interval_false`. -/
theorem predecessor_set_is_cyclic_interval (ell : Nat)
    (h1 : (cert.layerOrder ell).entries.length = w)
    (v : LayerVertex c (ell + 1))
    (hv : ∃ j : Fin w, c.edge (vtxAt c cert ell h1 j).val v.val = true) :
    ∃ (start : Fin w) (len : Nat),
      0 < len ∧ len ≤ w ∧
      (∀ k : Nat, k < len →
        c.edge (vtxAt c cert ell h1 (finShift k start)).val v.val = true) ∧
      (len < w → c.edge (vtxAt c cert ell h1 (finShift len start)).val v.val = false) ∧
      (len < w → c.edge (vtxAt c cert ell h1 (finPred start)).val v.val = false) := by
  classical
  obtain ⟨j, hj⟩ := hv
  obtain ⟨start, len, hlen⟩ :=
    exists_isCyclicInterval
      (s := fun i : Fin w => c.edge (vtxAt c cert ell h1 i).val v.val) j hj
  exact ⟨start, len, hlen⟩

/-! ### The non-degeneracy hypothesis cannot be dropped -/

/-- A full cyclic listing of a fintype has exactly `Fintype.card` entries. -/
theorem length_entries_eq_card {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (L : CyclicListing alpha) : L.entries.length = Fintype.card alpha := by
  have huniv : L.entries.toFinset = (Finset.univ : Finset alpha) := by
    ext a
    simp [L.complete a]
  have := List.toFinset_card_of_nodup L.nodup
  rw [huniv] at this
  rw [← this, Finset.card_univ]

/-- A two-gate, edge-free circuit: one vertex in layer `0` and one vertex in layer `1`. -/
def edgeFreeTwoLayer : ADRCircuit 1 where
  gateCount := 2
  output := ⟨0, by omega⟩
  kind := fun _ => .andGate
  layer := fun g => g.val
  edge := fun _ _ => false

theorem card_layerVertex_edgeFreeTwoLayer (ell : Nat) (hell : ell < 2) :
    Fintype.card (LayerVertex edgeFreeTwoLayer ell) = 1 := by
  rw [Fintype.card_subtype]
  interval_cases ell <;> decide

/-- **The original form of the lemma is false.**  Without assuming that the target vertex
has a predecessor, no maximal cyclic interval of predecessors can exist: the edge-free
circuit `edgeFreeTwoLayer` is incidence-cylindrical and has width one, yet its unique
layer-`1` vertex has no predecessor. -/
theorem predecessor_set_is_cyclic_interval_false :
    ¬ (∀ (n w : Nat) (c : ADRCircuit n) (cert : IncidenceCylinder c) (ell : Nat)
        (h1 : (cert.layerOrder ell).entries.length = w)
        (_h2 : (cert.layerOrder (ell + 1)).entries.length = w)
        (v : LayerVertex c (ell + 1)),
        ∃ (start : Fin w) (len : Nat),
          0 < len ∧ len ≤ w ∧
          (∀ k : Nat, k < len →
            c.edge (vtxAt c cert ell h1 (finShift k start)).val v.val = true) ∧
          (len < w → c.edge (vtxAt c cert ell h1 (finShift len start)).val v.val = false) ∧
          (len < w → c.edge (vtxAt c cert ell h1 (finPred start)).val v.val = false)) := by
  classical
  intro H
  obtain ⟨cert⟩ :=
    incidenceCylinder_of_edgeFree edgeFreeTwoLayer (fun _ _ => rfl)
  have h1 : (cert.layerOrder 0).entries.length = 1 := by
    rw [length_entries_eq_card, card_layerVertex_edgeFreeTwoLayer 0 (by omega)]
  have h2 : (cert.layerOrder (0 + 1)).entries.length = 1 := by
    rw [length_entries_eq_card, card_layerVertex_edgeFreeTwoLayer 1 (by omega)]
  have hv : LayerVertex edgeFreeTwoLayer (0 + 1) := ⟨⟨1, by decide⟩, rfl⟩
  obtain ⟨start, len, hpos, -, hall, -, -⟩ :=
    H 1 1 edgeFreeTwoLayer cert 0 h1 h2 hv
  have := hall 0 hpos
  exact Bool.false_ne_true this

end AllenderOQ3.Internal
