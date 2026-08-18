import AllenderOQ3.Internal.StateRelation

/-!
# Existence of a slot assignment for a bounded-width circuit

`LayerIndexing c w` (see `AllenderOQ3.Internal.StateRelation`) is the datum that
makes the state formalism instantiable: a slot in `Fin w` for every gate, injective
on the computation gates of a common layer.  This file constructs one from the
bounded-width hypothesis `ADRHasWidthAtMost c w`, provided `0 < w` (which is needed
to give the literal gates *some* slot; at `w = 0` a circuit with a single literal
gate has computation width `0` but a nonempty gate set, so `Fin w` is empty and no
slot assignment exists).

The slot of a computation gate `g` is its *rank* inside its layer: the number of
computation gates of the same layer that come strictly before it.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n : Nat}

/-- The computation gates of the layer of `g` that come strictly before `g`. -/
private def earlierCohort (c : ADRCircuit n) (g : Fin c.gateCount) :
    Finset (Fin c.gateCount) :=
  Finset.univ.filter (fun h : Fin c.gateCount =>
    (c.kind h).isComputation = true ∧ c.layer h = c.layer g ∧ h < g)

/-- The rank of `g` among the computation gates of its own layer. -/
private def layerRank (c : ADRCircuit n) (g : Fin c.gateCount) : Nat :=
  (earlierCohort c g).card

private theorem earlierCohort_subset_cohort (c : ADRCircuit n) (g : Fin c.gateCount) :
    earlierCohort c g ⊆
      Finset.univ.filter (fun h : Fin c.gateCount =>
        c.layer h = c.layer g ∧ (c.kind h).isComputation = true) := by
  intro h hh
  simp only [earlierCohort, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
  exact ⟨hh.2.1, hh.1⟩

private theorem layerRank_lt {w : Nat} {c : ADRCircuit n} (hw : ADRHasWidthAtMost c w)
    {g : Fin c.gateCount} (hg : (c.kind g).isComputation = true) :
    layerRank c g < w := by
  have hsub := earlierCohort_subset_cohort c g
  have hmem : g ∈ Finset.univ.filter (fun h : Fin c.gateCount =>
      c.layer h = c.layer g ∧ (c.kind h).isComputation = true) := by
    simp [hg]
  have hnot : g ∉ earlierCohort c g := by
    simp [earlierCohort]
  have hss : earlierCohort c g ⊂
      Finset.univ.filter (fun h : Fin c.gateCount =>
        c.layer h = c.layer g ∧ (c.kind h).isComputation = true) :=
    (Finset.ssubset_iff_of_subset hsub).mpr ⟨g, hmem, hnot⟩
  exact lt_of_lt_of_le (Finset.card_lt_card hss) (hw (c.layer g))

private theorem layerRank_strictMono {c : ADRCircuit n} {g h : Fin c.gateCount}
    (hgc : (c.kind g).isComputation = true) (hlayer : c.layer g = c.layer h)
    (hlt : g < h) : layerRank c g < layerRank c h := by
  have hsub : earlierCohort c g ⊆ earlierCohort c h := by
    intro k hk
    simp only [earlierCohort, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨hk.1, by rw [hk.2.1, hlayer], lt_trans hk.2.2 hlt⟩
  have hmem : g ∈ earlierCohort c h := by
    simp only [earlierCohort, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hgc, hlayer, hlt⟩
  have hnot : g ∉ earlierCohort c g := by
    simp [earlierCohort]
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨g, hmem, hnot⟩)

/-- A circuit of computation width at most `w`, with `0 < w`, admits a slot assignment:
each computation gate is placed at its rank inside its layer, and the literal gates are
parked in slot `0`. -/
theorem exists_layerIndexing_of_width {w : Nat} (c : ADRCircuit n)
    (hw : ADRHasWidthAtMost c w) (hw0 : 0 < w) : Nonempty (LayerIndexing c w) := by
  classical
  refine ⟨⟨fun g =>
    if hg : (c.kind g).isComputation = true then ⟨layerRank c g, layerRank_lt hw hg⟩
    else ⟨0, hw0⟩, ?_⟩⟩
  intro g h hgc hhc hlayer hslot
  simp only [dif_pos hgc, dif_pos hhc, Fin.mk.injEq] at hslot
  rcases lt_trichotomy g h with hlt | heq | hgt
  · exact absurd hslot (Nat.ne_of_lt (layerRank_strictMono hgc hlayer hlt))
  · exact heq
  · exact absurd hslot.symm (Nat.ne_of_lt (layerRank_strictMono hhc hlayer.symm hgt))

end AllenderOQ3.Internal
