import AllenderOQ3.Internal.ComponentGateFacts
import AllenderOQ3.Internal.ArcWordBlocksPartial
import AllenderOQ3.Internal.LivePosition
import AllenderOQ3.Internal.RotationPosition
import AllenderOQ3.Internal.TrueRun
import AllenderOQ3.Internal.ComponentMerge

namespace AllenderOQ3.Internal

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)
variable (xIn : Fin n → Bool) (ell : Nat)
variable (hN : HMVNormal c) (hW : TotalWidthAtMost c w)
variable (hfull : (cert.layerOrder (ell + 1)).entries.length = w)
variable (hcf : ConstantFreeLayer c ell)
variable (x : Config w)

/-- The neighbour map: associates an output piece K to an input piece I. Returns ⊥ if K is not a
  piece. -/
noncomputable def nbr (K : Config w) : Config w :=
  if hK : K ∈ intervalsOf (layerTransMap c cert xIn ell x) then
    have hw : 0 < w := by
      obtain ⟨start, _⟩ := mem_intervalsOf.mp hK
      exact start.pos
    have h1 : IsIntervalConfig K := isIntervalConfig_of_mem_intervalsOf hK
    have hwlen : 0 < lenOf K := (eq_pieceConfig_canonical h1 hw).1
    have hc : K = pieceConfig (startOf hw K) (lenOf K) := (eq_pieceConfig_canonical h1 hw).2.2
    have h2 : K (startOf hw K) = true := by
      have hc_app : K (startOf hw K) = pieceConfig (startOf hw K) (lenOf K) (startOf hw K) :=
        congrFun hc _
      rw [hc_app, pieceConfig_true_iff]
      exact ⟨0, hwlen, by simp⟩
    have h3 : layerTransMap c cert xIn ell x (startOf hw K) = true :=
      le_of_isIntervalPiece (mem_intervalsOf.mp hK) h2
    have hj : (startOf hw K).val < (cert.layerOrder (ell + 1)).entries.length := by
      rw [hfull]
      exact (startOf hw K).isLt
    have h4 := exists_true_pred_of_layerTransMap_true c cert hN.1 hW xIn hcf x hj h3
    let u := Classical.choose h4
    let hu := Classical.choose (Classical.choose_spec h4)
    let hx := Classical.choose_spec (Classical.choose_spec h4)
    let h5 := exists_piece_mem hx
    Classical.choose h5
  else
    ⊥

/-- The neighbour piece is a valid interval piece of the input configuration x. -/
theorem nbr_mem_intervalsOf (K : Config w) (hK : K ∈ intervalsOf (layerTransMap c cert xIn ell x)) :
    nbr c cert xIn ell hN hW hfull hcf x K ∈ intervalsOf x := by
  dsimp [nbr]
  rw [dif_pos hK]
  have hw : 0 < w := by
    obtain ⟨start, _⟩ := mem_intervalsOf.mp hK
    exact start.pos
  have h1 : IsIntervalConfig K := isIntervalConfig_of_mem_intervalsOf hK
  have hwlen : 0 < lenOf K := (eq_pieceConfig_canonical h1 hw).1
  have hc : K = pieceConfig (startOf hw K) (lenOf K) := (eq_pieceConfig_canonical h1 hw).2.2
  have h2 : K (startOf hw K) = true := by
    have hc_app : K (startOf hw K) = pieceConfig (startOf hw K) (lenOf K) (startOf hw K) :=
      congrFun hc _
    rw [hc_app, pieceConfig_true_iff]
    exact ⟨0, hwlen, by simp⟩
  have h3 : layerTransMap c cert xIn ell x (startOf hw K) = true :=
    le_of_isIntervalPiece (mem_intervalsOf.mp hK) h2
  have hj : (startOf hw K).val < (cert.layerOrder (ell + 1)).entries.length := by
    rw [hfull]
    exact (startOf hw K).isLt
  have h4 := exists_true_pred_of_layerTransMap_true c cert hN.1 hW xIn hcf x hj h3
  let u := Classical.choose h4
  let hu := Classical.choose (Classical.choose_spec h4)
  let hx := Classical.choose_spec (Classical.choose_spec h4)
  let h5 := exists_piece_mem hx
  exact (Classical.choose_spec h5).1

/-- **The neighbour of an output piece touches it.**  Its distinguished witness
is the true predecessor of the target at the start of `K`. -/
theorem touch_nbr (K : Config w) (hK : K ∈ intervalsOf (layerTransMap c cert xIn ell x)) :
    Touch c cert ell hfull hW (nbr c cert xIn ell hN hW hfull hcf x K) K := by
  dsimp only [nbr]
  rw [dif_pos hK]
  have hw : 0 < w := by
    obtain ⟨start, _⟩ := mem_intervalsOf.mp hK
    exact start.pos
  have h1 : IsIntervalConfig K := isIntervalConfig_of_mem_intervalsOf hK
  have hwlen : 0 < lenOf K := (eq_pieceConfig_canonical h1 hw).1
  have hc : K = pieceConfig (startOf hw K) (lenOf K) := (eq_pieceConfig_canonical h1 hw).2.2
  have h2 : K (startOf hw K) = true := by
    have hc_app : K (startOf hw K) = pieceConfig (startOf hw K) (lenOf K) (startOf hw K) :=
      congrFun hc _
    rw [hc_app, pieceConfig_true_iff]
    exact ⟨0, hwlen, by simp⟩
  have h3 : layerTransMap c cert xIn ell x (startOf hw K) = true :=
    le_of_isIntervalPiece (mem_intervalsOf.mp hK) h2
  have hj : (startOf hw K).val < (cert.layerOrder (ell + 1)).entries.length := by
    rw [hfull]
    exact (startOf hw K).isLt
  have h4 := exists_true_pred_of_layerTransMap_true c cert hN.1 hW xIn hcf x hj h3
  let u := Classical.choose h4
  let hu := Classical.choose (Classical.choose_spec h4)
  let hx := Classical.choose_spec (Classical.choose_spec h4)
  let h5 := exists_piece_mem hx
  refine ⟨startOf hw K, ⟨u, layer_pred_eq c hN.1 hu⟩, h2, hu, ?_⟩
  change Classical.choose h5
      (idxOfVtx c cert ell (layerEntries_length_le hW ell) ⟨u, layer_pred_eq c hN.1 hu⟩) = true
  rw [← vertCoord_eq_idxOfVtx]
  exact (Classical.choose_spec h5).2

/-- **The neighbour map is injective.**  Two output pieces with the same
neighbour both touch it, so they coincide by the merging run. -/
theorem nbr_injOn :
    Set.InjOn (nbr c cert xIn ell hN hW hfull hcf x)
      (intervalsOf (layerTransMap c cert xIn ell x)) := by
  intro K1 hK1 K2 hK2 hEq
  have hK1' : K1 ∈ intervalsOf (layerTransMap c cert xIn ell x) := hK1
  have hK2' : K2 ∈ intervalsOf (layerTransMap c cert xIn ell x) := hK2
  have ht1 := touch_nbr c cert xIn ell hN hW hfull hcf x K1 hK1'
  have ht2 := touch_nbr c cert xIn ell hN hW hfull hcf x K2 hK2'
  rw [hEq] at ht1
  have hI : nbr c cert xIn ell hN hW hfull hcf x K2 ∈ intervalsOf x :=
    nbr_mem_intervalsOf c cert xIn ell hN hW hfull hcf x K2 hK2'
  exact touch_uniq c cert xIn ell hN hW hfull hcf x hI hK1' hK2' ht1 ht2

end AllenderOQ3.Internal
