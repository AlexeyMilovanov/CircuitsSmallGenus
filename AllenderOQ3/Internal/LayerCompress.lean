import AllenderOQ3.Internal.Prune
import AllenderOQ3.Internal.LayerPath
import AllenderOQ3.Internal.OrbitCount

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- Some gate attains the minimum layer.  Proved via the finite
minimal-representative principle `exists_minRep` (with the trivial "everything
is related" equivalence), so it needs none of the `Finset.inf'` API. -/
theorem exists_min_gate {n : Nat} (c : ADRCircuit n) :
    ∃ x : Fin c.gateCount, ∀ y, c.layer x ≤ c.layer y := by
  have hr : Equivalence (fun _ _ : Fin c.gateCount => True) := by
    constructor
    · intro _; trivial
    · intro _ _ _; trivial
    · intro _ _ _ _ _; trivial
  obtain ⟨x, _, hx⟩ := exists_minRep hr c.layer c.output
  exact ⟨x, fun y => hx y True.intro⟩

/-- The minimum layer occupied by any gate.  Defined through `exists_min_gate`
so that `minActiveLayer_le` and `exists_layer_eq_minActiveLayer` are immediate;
the value is the minimum of `c.layer`, exactly as the previous
`Finset.univ.inf' … c.layer` definition. -/
noncomputable def minActiveLayer {n : Nat} (c : ADRCircuit n) : Nat :=
  c.layer (Classical.choose (exists_min_gate c))

/-- `minActiveLayer c` is a lower bound for every gate layer. -/
theorem minActiveLayer_le {n : Nat} (c : ADRCircuit n) (g : Fin c.gateCount) :
    minActiveLayer c ≤ c.layer g :=
  Classical.choose_spec (exists_min_gate c) g

/-- `minActiveLayer c` is attained by some gate. -/
theorem exists_layer_eq_minActiveLayer {n : Nat} (c : ADRCircuit n) :
    ∃ g, c.layer g = minActiveLayer c :=
  ⟨Classical.choose (exists_min_gate c), rfl⟩

def shiftLayers {n : Nat} (c : ADRCircuit n) (m : Nat) : ADRCircuit n :=
  { c with layer := fun g => c.layer g - m }

theorem wellFormed_shiftLayers {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {m : Nat} (hm : ∀ g, m ≤ c.layer g) : WellFormedADR (shiftLayers c m) := by
  constructor
  · intro u v h
    have h1 := hc.1 u v h
    have hm_u := hm u
    have hm_v := hm v
    dsimp [shiftLayers]
    omega
  · intro g hg h
    exact hc.2 g hg h

/-- Translating every layer down by `m` does not increase the computation width,
**provided** every layer is at least `m` (otherwise truncated subtraction would
collapse the layers `0 … m` onto layer `0` and could increase the width).  The
hypothesis `hm` holds for the intended shift `m = minActiveLayer c`. -/
theorem width_shiftLayers {n : Nat} {c : ADRCircuit n} {w m : Nat}
    (hw : ADRHasWidthAtMost c w) (hm : ∀ g, m ≤ c.layer g) :
    ADRHasWidthAtMost (shiftLayers c m) w := by
  intro ell
  refine le_trans (Finset.card_le_card ?_) (hw (ell + m))
  intro g hg
  rw [Finset.mem_filter] at hg ⊢
  obtain ⟨-, h1, h2⟩ := hg
  refine ⟨Finset.mem_univ g, ?_, h2⟩
  have hml := hm g
  have h1' : c.layer g - m = ell := h1
  omega

theorem accepts_shiftLayers {n : Nat} (c : ADRCircuit n) (m : Nat) (x : Fin n → Bool) :
    ADRAccepts (shiftLayers c m) x ↔ ADRAccepts c x := Iff.rfl

/-- Shifting layers does not change the rotation genus.  NOTE: this is **not**
`rfl`.  `OrientableRotation` is a `structure` indexed by the whole circuit, and
`shiftLayers c m` is not definitionally equal to `c` (its `.layer` field differs),
so `OrientableRotation (shiftLayers c m)` is not defeq to `OrientableRotation c`.
The proof must transport rotations across the two circuits (the underlying
`CircuitDart`, `UnderlyingAdj`, `componentCount`, `underlyingEdgeCount`,
`isolatedVertexCount`, `facePermutation` and `gateCount` are all defeq, since they
ignore `.layer`, so `rotationGenus` is preserved once the rotation is transported).
-/
theorem genus_shiftLayers {n : Nat} (c : ADRCircuit n) (m : Nat) :
    orientableCircuitGenus (shiftLayers c m) = orientableCircuitGenus c := by
  unfold orientableCircuitGenus
  congr 1
  ext g
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨⟨r.rotation, r.preservesSource, r.cyclicAtVertex⟩, hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨⟨r.rotation, r.preservesSource, r.cyclicAtVertex⟩, hr⟩

theorem layer_occupied_of_between {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (hcone : ∀ g, EdgeReach c g c.output) {l : Nat}
    (hlo : minActiveLayer c ≤ l) (hhi : l ≤ c.layer c.output) :
    ∃ g, c.layer g = l := by
  obtain ⟨g0, hg0⟩ := exists_layer_eq_minActiveLayer c
  have hg0le : c.layer g0 ≤ l := by rw [hg0]; exact hlo
  obtain ⟨z, _, _, hz⟩ := edgeReach_meets_layer hc (hcone g0) hg0le hhi
  exact ⟨z, hz⟩

theorem layerSpan_lt_gateCount {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (hcone : ∀ g, EdgeReach c g c.output) :
    c.layer c.output - minActiveLayer c < c.gateCount := by
  classical
  have hmin := minActiveLayer_le c c.output
  have hsub : Finset.Icc (minActiveLayer c) (c.layer c.output) ⊆
      Finset.univ.image c.layer := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨g, hg⟩ := layer_occupied_of_between hc hcone hl.1 hl.2
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, hg⟩
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h1
  have h2 : (Finset.univ.image c.layer).card ≤ c.gateCount := by
    calc (Finset.univ.image c.layer).card
        ≤ (Finset.univ : Finset (Fin c.gateCount)).card := Finset.card_image_le
      _ = c.gateCount := by simp
  omega

end AllenderOQ3.Internal
