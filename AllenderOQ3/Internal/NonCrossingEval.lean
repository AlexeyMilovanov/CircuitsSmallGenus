import AllenderOQ3.Internal.FullLayerIndexing
import AllenderOQ3.Internal.StateRelation
import AllenderOQ3.Internal.CylNormal

set_option autoImplicit false
set_option linter.unusedVariables false

namespace AllenderOQ3.Internal

variable {n : Nat} (c : ADRCircuit n)

/-- The length of the certificate's layer listing equals the number of layer
vertices; bridges `FullLayerIndexing` to `TotalWidthAtMost`. -/
theorem layerOrder_length_eq_card (cert : IncidenceCylinder c) (ell : Nat) :
    (cert.layerOrder ell).entries.length =
      (Finset.univ.filter fun g : Fin c.gateCount => c.layer g = ell).card := by
  have h1 : Fintype.card (LayerVertex c ell) =
      (cert.layerOrder ell).entries.length :=
    (Fintype.card_congr (FullLayerIndexing c cert ell)).trans (Fintype.card_fin _)
  rw [← h1, ← Fintype.card_subtype _]

noncomputable def layerIndexingSlot (cert : IncidenceCylinder c) {W : Nat} (hW : TotalWidthAtMost c W) (g : Fin c.gateCount) : Fin W :=
  let ell := c.layer g
  let idx := (FullLayerIndexing c cert ell) ⟨g, rfl⟩
  have h1 : Fintype.card (LayerVertex c ell) = (cert.layerOrder ell).entries.length := by
    calc Fintype.card (LayerVertex c ell) = Fintype.card (Fin (cert.layerOrder ell).entries.length) := Fintype.card_congr (FullLayerIndexing c cert ell)
      _ = (cert.layerOrder ell).entries.length := Fintype.card_fin _
  have h2 : (Finset.univ.filter fun x : Fin c.gateCount => c.layer x = ell).card = Fintype.card (LayerVertex c ell) := by
    exact (Fintype.card_subtype _).symm
  have h3 : (cert.layerOrder ell).entries.length ≤ W := by
    rw [← h1, ← h2]
    exact hW ell
  ⟨idx.val, lt_of_lt_of_le idx.isLt h3⟩

theorem slot_inj_helper (cert : IncidenceCylinder c) (ell1 ell2 : Nat) (g h : Fin c.gateCount)
    (hg : c.layer g = ell1) (hh : c.layer h = ell2) (hell : ell1 = ell2)
    (eq1 : ((FullLayerIndexing c cert ell1) ⟨g, hg⟩).val = ((FullLayerIndexing c cert ell2) ⟨h, hh⟩).val) : g = h := by
  cases hell
  have eq2 : (FullLayerIndexing c cert ell1) ⟨g, hg⟩ = (FullLayerIndexing c cert ell1) ⟨h, hh⟩ := Fin.ext eq1
  have eq3 : (⟨g, hg⟩ : LayerVertex c ell1) = ⟨h, hh⟩ := (Equiv.apply_eq_iff_eq _).mp eq2
  exact congrArg Subtype.val eq3

noncomputable def layerIndexing_of_full (cert : IncidenceCylinder c) {W : Nat}
    (hW : TotalWidthAtMost c W) : LayerIndexing c W where
  slot := layerIndexingSlot c cert hW
  injOnLayer g h _ _ hlayer hslot := by
    have eq1 : (layerIndexingSlot c cert hW g).val = (layerIndexingSlot c cert hW h).val := by rw [hslot]
    dsimp [layerIndexingSlot] at eq1
    exact slot_inj_helper c cert (c.layer g) (c.layer h) g h rfl rfl hlayer eq1

/-- A width-zero circuit is impossible: the output gate always occupies its
own layer, so that filter is nonempty and has card ≥ 1. -/
theorem totalWidthAtMost_zero_elim (h : TotalWidthAtMost c 0) : False := by
  have hcard := h (c.layer c.output)
  have hmem : c.output ∈ Finset.univ.filter
      (fun g : Fin c.gateCount => c.layer g = c.layer c.output) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hpos : 0 < (Finset.univ.filter
      (fun g : Fin c.gateCount => c.layer g = c.layer c.output)).card :=
    Finset.card_pos.mpr ⟨c.output, hmem⟩
  omega

end AllenderOQ3.Internal
