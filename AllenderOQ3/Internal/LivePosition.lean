import AllenderOQ3.Internal.ArcWordBlocksPartial
import AllenderOQ3.Internal.IntervalPieces

namespace AllenderOQ3.Internal

variable {w : Nat}

/-- C4': If a piece contains a live coordinate (val < L), its live positions form a cyclic interval
  modulo L. -/
theorem piece_to_live_position_interval {L : Nat} (hLw : L ≤ w)
    {x : Config w} {start : Fin w} {len : Nat} (hcyc : IsCyclicInterval x start len)
    (h_live : ∃ j, j.val < L ∧ (pieceConfig start len) j = true) :
    ∃ (a' : Fin w) (haL : a'.val < L) (len' : Nat),
      len' ≤ L ∧
      (pieceConfig start len) a' = true ∧
      ∀ p : Fin L,
        ((∃ k, k < len' ∧ finShift k (⟨a'.val, haL⟩ : Fin L) = p) ↔
         (pieceConfig start len) (⟨p.val, lt_of_lt_of_le p.isLt hLw⟩ : Fin w)) := by
  let P (k : Nat) := (finShift k start).val < L
  have h_ex : ∃ k, P k := by
    obtain ⟨j, hjL, hj_true⟩ := h_live
    obtain ⟨k, hk_lt, hk_eq⟩ := pieceConfig_true_iff.mp hj_true
    use k
    change (finShift k start).val < L
    rw [hk_eq]
    exact hjL
  let k0 := Nat.find h_ex
  have hk0_P : P k0 := Nat.find_spec h_ex
  have hk0_lt : k0 < len := by
    obtain ⟨j, hjL, hj_true⟩ := h_live
    obtain ⟨k, hk_lt, hk_eq⟩ := pieceConfig_true_iff.mp hj_true
    have hk_P : P k := by
      change (finShift k start).val < L
      rw [hk_eq]
      exact hjL
    have hk0_le_k := Nat.find_min' h_ex hk_P
    omega
  let a' := finShift k0 start
  have haL : a'.val < L := hk0_P
  have ha_true : pieceConfig start len a' = true := by
    apply pieceConfig_true_iff.mpr
    exact ⟨k0, hk0_lt, rfl⟩
  let lenJ := len - k0
  have hJw : lenJ ≤ w := by
    have h1 : len ≤ w := hcyc.2.1
    omega
  obtain ⟨len', hlen'L, h_bridge⟩ := live_interval_bridge hLw a' haL lenJ hJw
  use a', haL, len', hlen'L, ha_true
  intro p
  rw [h_bridge p]
  rw [pieceConfig_true_iff]
  constructor
  · rintro ⟨k, hk_lt, hk_eq⟩
    use k + k0
    constructor
    · omega
    · have h_shift : finShift (k + k0) start = finShift k a' := by
        dsimp [a']
        rw [finShift_finShift]
        congr 1
        omega
      rw [h_shift, hk_eq]
  · rintro ⟨k, hk_lt, hk_eq⟩
    have hk_P : P k := by
      change (finShift k start).val < L
      rw [hk_eq]
      exact p.isLt
    have hk0_le_k : k0 ≤ k := Nat.find_min' h_ex hk_P
    use k - k0
    constructor
    · omega
    · have h_shift : finShift (k - k0) a' = finShift k start := by
        dsimp [a']
        rw [finShift_finShift]
        have h_add : k0 + (k - k0) = k := by omega
        rw [h_add]
      rw [h_shift, hk_eq]

end AllenderOQ3.Internal
