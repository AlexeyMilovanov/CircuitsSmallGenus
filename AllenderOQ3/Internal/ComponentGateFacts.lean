import AllenderOQ3.Internal.ConstantFreeLayers

/-!
# Gate-semantics facts for constant-free layers (T1.3)

The per-gate characterization of `layerTransMap` truth values needed by the
component lemma (plan 6b): a true `AND` target has all predecessors true, a
true `OR` target has a true predecessor, every target of a constant-free
layer is a computation gate with a nonempty incoming block, and hence every
true target coordinate has a true source coordinate.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)

/-- The width-`w` coordinate of a layer vertex. -/
noncomputable def vertCoord {w : Nat} (hW : TotalWidthAtMost c w) {ell : Nat}
    (u : LayerVertex c ell) : Fin w :=
  ⟨(FullLayerIndexing c cert ell u).val, fullIndex_lt c cert hW ell u⟩

/-- A constant-free target is an `AND` or an `OR`. -/
theorem kind_and_or_or_of_constantFree {ell : Nat}
    (hcf : ConstantFreeLayer c ell) (v : LayerVertex c (ell + 1)) :
    c.kind v.val = ADRGate.andGate ∨ c.kind v.val = ADRGate.orGate := by
  have h := (hcf v).1
  cases hk : c.kind v.val with
  | literal i b =>
    rw [hk] at h
    simp [ADRGate.isComputation] at h
  | andGate => exact Or.inl rfl
  | orGate => exact Or.inr rfl

/-- A constant-free target has a nonempty incoming block. -/
theorem incoming_ne_nil_of_constantFree (hc : WellFormedADR c) {ell : Nat}
    (hcf : ConstantFreeLayer c ell) (v : LayerVertex c (ell + 1)) :
    (cert.transitionOrder ell).incoming v ≠ [] := by
  obtain ⟨-, u, hu⟩ := hcf v
  have hlu : c.layer u = ell := layer_pred_eq c hc hu
  intro hnil
  have hmem : (⟨(u, v.val), hu, hlu, v.2⟩ : TransitionArc c ell)
      ∈ (cert.transitionOrder ell).incoming v :=
    ((cert.transitionOrder ell).incoming_exact v _).mpr rfl
  rw [hnil] at hmem
  simp at hmem

/-- **`AND` semantics**: a true `AND` target is exactly one with all
predecessor coordinates true. -/
theorem layerTransMap_and_true_iff {w : Nat} (hc : WellFormedADR c)
    (hW : TotalWidthAtMost c w) (x : Fin n → Bool) {ell : Nat}
    (s : Config w) {j : Fin w}
    (hj : j.val < (cert.layerOrder (ell + 1)).entries.length)
    (hkind : c.kind ((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, hj⟩).val
      = ADRGate.andGate) :
    layerTransMap c cert x ell s j = true
      ↔ ∀ u (hu : c.edge u
            ((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, hj⟩).val = true),
          s (vertCoord c cert hW ⟨u, layer_pred_eq c hc hu⟩) = true := by
  dsimp only [layerTransMap]
  rw [dif_pos hj]
  simp only [hkind]
  rw [decide_eq_true_iff]
  constructor
  · intro hall u hu
    have hb := hall u hu
    have hlu : c.layer u = ell := layer_pred_eq c hc hu
    rw [dif_pos hlu, dif_pos (fullIndex_lt c cert hW ell ⟨u, hlu⟩)] at hb
    exact hb
  · intro hall u hu
    have hlu : c.layer u = ell := layer_pred_eq c hc hu
    rw [dif_pos hlu, dif_pos (fullIndex_lt c cert hW ell ⟨u, hlu⟩)]
    exact hall u hu

/-- **`OR` semantics**: a true `OR` target is exactly one with some
predecessor coordinate true. -/
theorem layerTransMap_or_true_iff {w : Nat} (hc : WellFormedADR c)
    (hW : TotalWidthAtMost c w) (x : Fin n → Bool) {ell : Nat}
    (s : Config w) {j : Fin w}
    (hj : j.val < (cert.layerOrder (ell + 1)).entries.length)
    (hkind : c.kind ((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, hj⟩).val
      = ADRGate.orGate) :
    layerTransMap c cert x ell s j = true
      ↔ ∃ u, ∃ (hu : c.edge u
            ((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, hj⟩).val = true),
          s (vertCoord c cert hW ⟨u, layer_pred_eq c hc hu⟩) = true := by
  dsimp only [layerTransMap]
  rw [dif_pos hj]
  simp only [hkind]
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨u, hu, hb⟩
    have hlu : c.layer u = ell := layer_pred_eq c hc hu
    rw [dif_pos hlu, dif_pos (fullIndex_lt c cert hW ell ⟨u, hlu⟩)] at hb
    exact ⟨u, hu, hb⟩
  · rintro ⟨u, hu, hs⟩
    refine ⟨u, hu, ?_⟩
    have hlu : c.layer u = ell := layer_pred_eq c hc hu
    rw [dif_pos hlu, dif_pos (fullIndex_lt c cert hW ell ⟨u, hlu⟩)]
    exact hs

/-- **Every true target of a constant-free layer has a true predecessor.** -/
theorem exists_true_pred_of_layerTransMap_true {w : Nat} (hc : WellFormedADR c)
    (hW : TotalWidthAtMost c w) (x : Fin n → Bool) {ell : Nat}
    (hcf : ConstantFreeLayer c ell) (s : Config w) {j : Fin w}
    (hj : j.val < (cert.layerOrder (ell + 1)).entries.length)
    (htrue : layerTransMap c cert x ell s j = true) :
    ∃ u, ∃ (hu : c.edge u
          ((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, hj⟩).val = true),
        s (vertCoord c cert hW ⟨u, layer_pred_eq c hc hu⟩) = true := by
  rcases kind_and_or_or_of_constantFree c hcf
      ((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, hj⟩) with hand | hor
  · obtain ⟨-, u0, hu0⟩ := hcf ((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, hj⟩)
    exact ⟨u0, hu0,
      (layerTransMap_and_true_iff c cert hc hW x s hj hand).mp htrue u0 hu0⟩
  · exact (layerTransMap_or_true_iff c cert hc hW x s hj hor).mp htrue

/-- Above the listed target layer every output coordinate is false. -/
theorem layerTransMap_false_of_ge {w : Nat} (x : Fin n → Bool) {ell : Nat}
    (s : Config w) {j : Fin w}
    (hj : ¬ j.val < (cert.layerOrder (ell + 1)).entries.length) :
    layerTransMap c cert x ell s j = false := by
  dsimp only [layerTransMap]
  rw [dif_neg hj]

end AllenderOQ3.Internal
