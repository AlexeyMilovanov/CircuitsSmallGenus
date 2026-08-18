import AllenderOQ3.Internal.IntervalPieces
import AllenderOQ3.Internal.IntervalCount -- For C2-uniq

namespace AllenderOQ3.Internal

variable {w : Nat}

/-- C2: If a contiguous sequence of coordinates are all true, the start and end belong to the same piece. -/
theorem same_piece_of_true_run {z : Config w} {a b : Fin w} {d : Nat}
    (h_run : ∀ k ≤ d, z (finShift k a) = true)
    (h_end : finShift d a = b) :
    ∃ y ∈ intervalsOf z, y a = true ∧ y b = true := by
  have ha : z a = true := by
    have hza := h_run 0 (Nat.zero_le d)
    rwa [finShift_zero] at hza
  obtain ⟨y, hy, hya⟩ := exists_piece_mem ha
  use y
  refine ⟨hy, hya, ?_⟩
  rw [mem_intervalsOf] at hy
  obtain ⟨start, len, hcyc, rfl⟩ := hy
  rw [pieceConfig_true_iff] at hya
  obtain ⟨k, hk_lt, hk_eq⟩ := hya
  rw [pieceConfig_true_iff]
  rcases eq_or_lt_of_le hcyc.2.1 with hlen_eq | hlen_lt
  · obtain ⟨k', hk', hkeq'⟩ := finShift_surj_lt start b
    exact ⟨k', hlen_eq ▸ hk', hkeq'⟩
  · by_cases h_kd : k + d < len
    · use k + d
      refine ⟨h_kd, ?_⟩
      rw [← h_end, ← hk_eq, finShift_finShift]
    · push_neg at h_kd
      have h_m : len - k ≤ d := by omega
      have hz : z (finShift (len - k) a) = true := h_run (len - k) h_m
      have h_shift : finShift (len - k) a = finShift len start := by
        rw [← hk_eq, finShift_finShift]
        have h_add : k + (len - k) = len := by omega
        rw [h_add]
      rw [h_shift] at hz
      have h_false := hcyc.2.2.2.1 hlen_lt
      rw [hz] at h_false
      contradiction

/-- C2 variant with uniqueness -/
theorem mem_same_piece_of_true_run {z y_a y_b : Config w} {a b : Fin w} {d : Nat}
    (hy_a : y_a ∈ intervalsOf z) (hy_b : y_b ∈ intervalsOf z)
    (h_a : y_a a = true) (h_b : y_b b = true)
    (h_run : ∀ k ≤ d, z (finShift k a) = true)
    (h_end : finShift d a = b) :
    y_a = y_b := by
  obtain ⟨y, hy, hya, hyb⟩ := same_piece_of_true_run h_run h_end
  have h1 := eq_of_mem_intervalsOf_of_true hy_a hy h_a hya
  have h2 := eq_of_mem_intervalsOf_of_true hy_b hy h_b hyb
  exact h1.trans h2.symm

end AllenderOQ3.Internal
