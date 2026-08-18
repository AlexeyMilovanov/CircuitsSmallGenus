import AllenderOQ3.Internal.ArcWordBlocksPartial
import AllenderOQ3.Internal.ComponentGateFacts
import AllenderOQ3.Internal.IntervalStart

/-!
# Live-source interval bridge for the rotation geometry

`live_interval_bridge` handles a `Fin w` cyclic interval whose canonical
start is already in the live source prefix `Fin L`.  The rotation proof also
meets intervals starting in the dead suffix `[L, w)` and wrapping into that
prefix.  In that case the live part starts at `0` and has length
`min L (len - (w - start))`.

The theorem below packages both cases.  It is the source-side B1 atom needed
before applying `exists_arcWord_interval_block_pos`; it makes no geometric
claim about the target layer.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {n w : Nat} {c : ADRCircuit n} {cert : IncidenceCylinder c}

/-- A source vertex's width coordinate is its position in the source listing. -/
theorem vertCoord_eq_vtxPos_cast (hW : TotalWidthAtMost c w) (ell : Nat)
    (u : LayerVertex c ell) :
    vertCoord c cert hW u =
      (⟨(vtxPos (cert := cert) ell u).val,
        lt_of_lt_of_le (vtxPos (cert := cert) ell u).isLt
          (layerOrder_length_le c cert hW ell)⟩ : Fin w) := by
  rfl

/-- A positive-width constant-free layer has a nonempty source listing:
choose any filled target and use its required predecessor. -/
theorem sourceOrder_length_pos_of_constantFree (hw : 0 < w) (hc : WellFormedADR c)
    (ell : Nat) (hfull : (cert.layerOrder (ell + 1)).entries.length = w)
    (hcf : ConstantFreeLayer c ell) :
    0 < (cert.layerOrder ell).entries.length := by
  have hj : 0 < (cert.layerOrder (ell + 1)).entries.length := by omega
  let v : LayerVertex c (ell + 1) :=
    (FullLayerIndexing c cert (ell + 1)).symm ⟨0, hj⟩
  obtain ⟨-, u, hu⟩ := hcf v
  have hlu : c.layer u = ell := layer_pred_eq c hc hu
  have hmem : (⟨u, hlu⟩ : LayerVertex c ell) ∈
      (cert.layerOrder ell).entries :=
    (cert.layerOrder ell).complete _
  by_contra h
  have hzero : (cert.layerOrder ell).entries.length = 0 := by omega
  have hnil : (cert.layerOrder ell).entries = [] :=
    List.eq_nil_of_length_eq_zero hzero
  rw [hnil] at hmem
  simp at hmem

/-- The live coordinates of any cyclic interval form one cyclic interval on
the live position circle.  When the original start is dead, the live interval
starts at position `0`; it may have length zero. -/
theorem live_interval_bridge_any_start {w L : Nat} (hLpos : 0 < L) (hLw : L ≤ w)
    (a : Fin w) (lenJ : Nat) (hJw : lenJ ≤ w) :
    ∃ a' : Fin L, ∃ len', len' ≤ L ∧ ∀ p : Fin L,
      ((∃ k, k < len' ∧ finShift k a' = p) ↔
       (∃ k, k < lenJ ∧
         finShift k a = (⟨p.val, lt_of_lt_of_le p.isLt hLw⟩ : Fin w))) := by
  by_cases haL : a.val < L
  · obtain ⟨len', hlen', hbridge⟩ := live_interval_bridge hLw a haL lenJ hJw
    exact ⟨⟨a.val, haL⟩, len', hlen', hbridge⟩
  · let d := w - a.val
    let len' := min L (lenJ - d)
    refine ⟨⟨0, hLpos⟩, len', Nat.min_le_left _ _, ?_⟩
    intro p
    have ha_le : L ≤ a.val := by omega
    have had : a.val + d = w := by
      dsimp [d]
      omega
    have hpw : p.val < w := lt_of_lt_of_le p.isLt hLw
    constructor
    · rintro ⟨k, hk, hkp⟩
      have hkL : k < L := lt_of_lt_of_le hk (Nat.min_le_left _ _)
      have hkr : k < lenJ - d := lt_of_lt_of_le hk (Nat.min_le_right _ _)
      have hkeq : k = p.val := by
        rw [Fin.ext_iff, finShift_val] at hkp
        simpa [Nat.mod_eq_of_lt hkL] using hkp
      refine ⟨d + p.val, by omega, ?_⟩
      rw [Fin.ext_iff, finShift_val]
      have hsum : a.val + (d + p.val) = w + p.val := by omega
      rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt hpw]
    · rintro ⟨k, hk, hkp⟩
      have haw : w ≤ a.val + k := by
        by_contra hlt
        have hval : a.val + k = p.val := by
          rw [Fin.ext_iff, finShift_val, Nat.mod_eq_of_lt (by omega)] at hkp
          exact hkp
        omega
      have haw2 : a.val + k - w < w := by omega
      have hval : a.val + k - w = p.val := by
        rw [Fin.ext_iff, finShift_val, Nat.mod_eq_sub_mod haw,
          Nat.mod_eq_of_lt haw2] at hkp
        exact hkp
      have hkd : k = d + p.val := by omega
      have hpr : p.val < lenJ - d := by omega
      have hplen : p.val < len' := by
        dsimp [len']
        exact lt_min p.isLt hpr
      refine ⟨p.val, hplen, ?_⟩
      rw [Fin.ext_iff, finShift_val]
      simp [Nat.mod_eq_of_lt p.isLt]

/-- The arcs emitted by the live part of an interval configuration form one
contiguous block of the source-major arc word, even when the source listing is
shorter than `w` and the interval starts in the dead suffix. -/
theorem exists_arcWord_true_source_block (hW : TotalWidthAtMost c w) (ell : Nat)
    (hLpos : 0 < (cert.layerOrder ell).entries.length) {y : Config w}
    (hy : IsIntervalConfig y) :
    ∃ P Q : List (TransitionArc c ell),
      CyclicRotation
        ((cert.layerOrder ell).entries.flatMap
          ((cert.transitionOrder ell).outgoing))
        (P ++ Q) ∧
      (∀ e ∈ P, y (vertCoord c cert hW (arcSource e)) = true) ∧
      (∀ e ∈ Q, y (vertCoord c cert hW (arcSource e)) = false) ∧
      (∀ e : TransitionArc c ell,
        y (vertCoord c cert hW (arcSource e)) = true → e ∈ P) := by
  let L := (cert.layerOrder ell).entries.length
  have hLw : L ≤ w := layerOrder_length_le c cert hW ell
  have hw : 0 < w := lt_of_lt_of_le hLpos hLw
  obtain ⟨-, hlenle, hyPiece⟩ := eq_pieceConfig_canonical hy hw
  obtain ⟨a', len', hlen', hbridge⟩ :=
    live_interval_bridge_any_start hLpos hLw (startOf hw y) (lenOf y) hlenle
  obtain ⟨P, Q, hrot, hP, hQ, hcomplete⟩ :=
    exists_arcWord_interval_block_pos (cert := cert) ell a' len' hlen'
  have htrue : ∀ e : TransitionArc c ell,
      y (vertCoord c cert hW (arcSource e)) = true ↔
        ∃ k, k < len' ∧
          vtxPos (cert := cert) ell (arcSource e) = finShift k a' := by
    intro e
    rw [hyPiece, pieceConfig_true_iff,
      vertCoord_eq_vtxPos_cast (cert := cert) hW ell]
    constructor
    · intro h
      have hr := (hbridge (vtxPos (cert := cert) ell (arcSource e))).mpr h
      obtain ⟨k, hk, heq⟩ := hr
      exact ⟨k, hk, heq.symm⟩
    · rintro ⟨k, hk, heq⟩
      exact (hbridge (vtxPos (cert := cert) ell (arcSource e))).mp
        ⟨k, hk, heq.symm⟩
  refine ⟨P, Q, hrot, ?_, ?_, ?_⟩
  · intro e he
    exact (htrue e).mpr (hP e he)
  · intro e he
    cases hval : y (vertCoord c cert hW (arcSource e)) with
    | false => rfl
    | true => exact absurd ((htrue e).mp hval) (hQ e he)
  · intro e he
    exact hcomplete e ((htrue e).mp he)

end Internal
end AllenderOQ3
