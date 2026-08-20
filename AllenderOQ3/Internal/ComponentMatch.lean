import AllenderOQ3.Internal.ComponentIncidence
import AllenderOQ3.Internal.ComponentMerge
import AllenderOQ3.Internal.IntervalPieces
import AllenderOQ3.Internal.TransitionMonoid
import AllenderOQ3.Internal.ComponentGateFacts
import AllenderOQ3.Internal.NonCrossingUnits

namespace AllenderOQ3.Internal

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)
variable (xIn : Fin n → Bool) (ell : Nat)
variable (hN : HMVNormal c) (hW : TotalWidthAtMost c w)
variable (hfull : (cert.layerOrder (ell + 1)).entries.length = w)
variable (hcf : ConstantFreeLayer c ell)
variable (x : Config w)

/-- The matched-pair image lemma: If `nbr K = I`, then in the equality case (the
neighbour map is a bijection) the transition maps `pieceConfig I` exactly to `K`.

The equality case forces each output piece to touch exactly one input piece.
The two containments then follow from the gate semantics: a `true` output
coordinate of `K` has all/one of its predecessors sourced in `I`, and any input
coordinate making the target true forces the containing output piece to be `K`. -/
theorem runTrans_pieceConfig_eq_of_nbr {I K : Config w}
    (hK : K ∈ intervalsOf (layerTransMap c cert xIn ell x))
    (hI : I = nbr c cert xIn ell hN hW hfull hcf x K)
    (h_bij : Set.BijOn (nbr c cert xIn ell hN hW hfull hcf x)
             (intervalsOf (layerTransMap c cert xIn ell x))
             (intervalsOf x)) :
    layerTransMap c cert xIn ell I = K := by
  have hLe : (cert.layerOrder ell).entries.length ≤ w := layerEntries_length_le hW ell
  have hI_mem : I ∈ intervalsOf x := by
    rw [hI]
    exact nbr_mem_intervalsOf c cert xIn ell hN hW hfull hcf x K hK
  -- In the bijection case, an input piece touched by `K'` is exactly `nbr K'`.
  have touch_eq_nbr : ∀ {K' I' : Config w},
      K' ∈ intervalsOf (layerTransMap c cert xIn ell x) → I' ∈ intervalsOf x →
      Touch c cert ell hfull hW I' K' →
      nbr c cert xIn ell hN hW hfull hcf x K' = I' := by
    intro K' I' hK' hI' htouch
    obtain ⟨K'', hK''mem, hK''eq⟩ := h_bij.surjOn (Finset.mem_coe.mpr hI')
    have hK''memF : K'' ∈ intervalsOf (layerTransMap c cert xIn ell x) := hK''mem
    have ht'' : Touch c cert ell hfull hW I' K'' := by
      have h := touch_nbr c cert xIn ell hN hW hfull hcf x K'' hK''memF
      rwa [hK''eq] at h
    have hK'eq : K' = K'' :=
      touch_uniq c cert xIn ell hN hW hfull hcf x hI' hK' hK''memF htouch ht''
    rw [hK'eq, hK''eq]
  funext j
  have hj : j.val < (cert.layerOrder (ell + 1)).entries.length := by rw [hfull]; exact j.isLt
  -- Containment 1: `layerTransMap I ≤ K`.
  have h_f_le : layerTransMap c cert xIn ell I j = true → K j = true := by
    intro hjI
    have hI_le_x : I ≤ x := by
      intro i hi
      exact le_of_isIntervalPiece (mem_intervalsOf.mp hI_mem) hi
    have h_mono := layerTransMap_monotone (w := w) (c := c) (cert := cert) xIn ell
    have h_le := h_mono hI_le_x
    have hy_j : layerTransMap c cert xIn ell x j = true := h_le j hjI
    obtain ⟨K', hK'mem, hK'j⟩ := exists_piece_mem hy_j
    have htouch : Touch c cert ell hfull hW I K' := by
      rcases kind_and_or_or_of_constantFree c hcf (vtxAt c cert (ell + 1) hfull j) with hand | hor
      · obtain ⟨-, u0, hu0⟩ := hcf (vtxAt c cert (ell + 1) hfull j)
        have hall := (layerTransMap_and (x := xIn) hLe hfull hN.1 I j hand).mp hjI
        exact
          ⟨j, ⟨u0, layer_pred_eq c hN.1 hu0⟩, hK'j, hu0, hall ⟨u0, layer_pred_eq c hN.1 hu0⟩ hu0⟩
      · obtain ⟨u0, hu0, hu0I⟩ := (layerTransMap_or (x := xIn) hLe hfull hN.1 I j hor).mp hjI
        exact ⟨j, u0, hK'j, hu0, hu0I⟩
    have hnbrK' : nbr c cert xIn ell hN hW hfull hcf x K' = I := touch_eq_nbr hK'mem hI_mem htouch
    have hK'eqK : K' = K := by
      apply h_bij.injOn (Finset.mem_coe.mpr hK'mem) (Finset.mem_coe.mpr hK)
      rw [hnbrK', hI]
    rw [← hK'eqK]; exact hK'j
  -- Containment 2: `K ≤ layerTransMap I`.
  have h_le_f : K j = true → layerTransMap c cert xIn ell I j = true := by
    intro hjK
    have hy_j : layerTransMap c cert xIn ell x j = true :=
      le_of_isIntervalPiece (mem_intervalsOf.mp hK) hjK
    have pred_in_I : ∀ (u : LayerVertex c ell),
        c.edge u.val (vtxAt c cert (ell + 1) hfull j).val = true →
        x (idxOfVtx c cert ell hLe u) = true →
        I (idxOfVtx c cert ell hLe u) = true := by
      intro u hu hxu
      obtain ⟨Iu, hIu_mem, hIu_u⟩ := exists_piece_mem hxu
      have htouch : Touch c cert ell hfull hW Iu K := ⟨j, u, hjK, hu, hIu_u⟩
      have hnbrK : nbr c cert xIn ell hN hW hfull hcf x K = Iu := touch_eq_nbr hK hIu_mem htouch
      have hIeq : I = Iu := hI.trans hnbrK
      rw [hIeq]; exact hIu_u
    rcases kind_and_or_or_of_constantFree c hcf (vtxAt c cert (ell + 1) hfull j) with hand | hor
    · rw [layerTransMap_and (x := xIn) hLe hfull hN.1 I j hand]
      intro u hu
      have hx_all := (layerTransMap_and (x := xIn) hLe hfull hN.1 x j hand).mp hy_j
      exact pred_in_I u hu (hx_all u hu)
    · rw [layerTransMap_or (x := xIn) hLe hfull hN.1 I j hor]
      obtain ⟨u, hu, hxu⟩ := (layerTransMap_or (x := xIn) hLe hfull hN.1 x j hor).mp hy_j
      exact ⟨u, hu, pred_in_I u hu hxu⟩
  cases hk : K j
  · cases hI_j : layerTransMap c cert xIn ell I j
    · rfl
    · have h2 := h_f_le hI_j
      rw [hk] at h2
      contradiction
  · cases hI_j : layerTransMap c cert xIn ell I j
    · have h2 := h_le_f hk
      rw [hI_j] at h2
      contradiction
    · rfl

end AllenderOQ3.Internal
