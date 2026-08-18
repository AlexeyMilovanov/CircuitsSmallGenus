import AllenderOQ3.Internal.IntervalStart

open Finset
namespace AllenderOQ3.Internal

variable {w : Nat}

theorem pieceConfig_full_eq_true {s : Fin w} {j : Fin w} : pieceConfig s w j = true := by
  obtain ⟨k, hk, hkeq⟩ := finShift_surj_lt s j
  exact pieceConfig_true_iff.mpr ⟨k, hk, hkeq⟩

theorem finPred_iterate_lt {k₁ m : Nat} {s₁ : Fin w} (hm : m < k₁) :
    finPred^[m + 1] (finShift k₁ s₁) = finShift (k₁ - m - 1) s₁ := by
  have h3 : finShift (m + 1) (finShift (k₁ - m - 1) s₁) = finShift k₁ s₁ := by
    rw [finShift_finShift]
    congr 1
    omega
  rw [← h3]
  exact finPred_iterate_finShift_cancel (m + 1) _

theorem eq_k_of_pieces {z : Config w} {s₁ s₂ j : Fin w} {l₁ l₂ k₁ k₂ : Nat}
    (hc₁ : IsCyclicInterval z s₁ l₁) (hc₂ : IsCyclicInterval z s₂ l₂)
    (hl1 : l₁ < w) (hl2 : l₂ < w)
    (hk1 : k₁ < l₁) (hk2 : k₂ < l₂)
    (eq1 : finShift k₁ s₁ = j) (eq2 : finShift k₂ s₂ = j) : k₁ = k₂ := by
  rcases lt_trichotomy k₁ k₂ with h | h | h
  · have h1 := @finPred_iterate_lt w k₂ k₁ s₂ h
    rw [eq2] at h1
    have h2 : finPred^[k₁ + 1] j = finPred s₁ := by
      have : finPred^[k₁] j = s₁ := by
        rw [← eq1, finPred_iterate_finShift_cancel]
      have step : finPred^[k₁ + 1] j = finPred (finPred^[k₁] j) := Function.iterate_succ_apply' finPred k₁ j
      rw [step, this]
    rw [h2] at h1
    have hf : z (finPred s₁) = false := hc₁.2.2.2.2 hl1
    have ht : z (finShift (k₂ - k₁ - 1) s₂) = true := by
      apply hc₂.2.2.1
      omega
    rw [h1] at hf
    rw [hf] at ht
    exact False.elim (Bool.false_ne_true ht)
  · exact h
  · have h1 := @finPred_iterate_lt w k₁ k₂ s₁ h
    rw [eq1] at h1
    have h2 : finPred^[k₂ + 1] j = finPred s₂ := by
      have : finPred^[k₂] j = s₂ := by
        rw [← eq2, finPred_iterate_finShift_cancel]
      have step : finPred^[k₂ + 1] j = finPred (finPred^[k₂] j) := Function.iterate_succ_apply' finPred k₂ j
      rw [step, this]
    rw [h2] at h1
    have hf : z (finPred s₂) = false := hc₂.2.2.2.2 hl2
    have ht : z (finShift (k₁ - k₂ - 1) s₁) = true := by
      apply hc₁.2.2.1
      omega
    rw [h1] at hf
    rw [hf] at ht
    exact False.elim (Bool.false_ne_true ht)

/-- C2-uniq: Two interval pieces of the same configuration that share a true coordinate are equal. -/
theorem eq_of_mem_intervalsOf_of_true {z y₁ y₂ : Config w} {j : Fin w}
    (hy₁ : y₁ ∈ intervalsOf z) (hy₂ : y₂ ∈ intervalsOf z)
    (hj₁ : y₁ j = true) (hj₂ : y₂ j = true) : y₁ = y₂ := by
  obtain ⟨s₁, l₁, hc₁, rfl⟩ := mem_intervalsOf.mp hy₁
  obtain ⟨s₂, l₂, hc₂, rfl⟩ := mem_intervalsOf.mp hy₂
  obtain ⟨k₁, hk₁, hkeq₁⟩ := pieceConfig_true_iff.mp hj₁
  obtain ⟨k₂, hk₂, hkeq₂⟩ := pieceConfig_true_iff.mp hj₂
  by_cases hall : IsAllTrue z
  · have hl1 : l₁ = w := by
      by_contra hc
      push_neg at hc
      have hlt : l₁ < w := lt_of_le_of_ne hc₁.2.1 hc
      have hf : z (finShift l₁ s₁) = false := hc₁.2.2.2.1 hlt
      have ht : z (finShift l₁ s₁) = true := hall _
      rw [hf] at ht
      exact False.elim (Bool.false_ne_true ht)
    have hl2 : l₂ = w := by
      by_contra hc
      push_neg at hc
      have hlt : l₂ < w := lt_of_le_of_ne hc₂.2.1 hc
      have hf : z (finShift l₂ s₂) = false := hc₂.2.2.2.1 hlt
      have ht : z (finShift l₂ s₂) = true := hall _
      rw [hf] at ht
      exact False.elim (Bool.false_ne_true ht)
    subst hl1 hl2
    ext i
    rw [pieceConfig_full_eq_true, pieceConfig_full_eq_true]
  · have hl1 : l₁ < w := by
      by_contra hc
      push_neg at hc
      have hl1_eq : l₁ = w := le_antisymm hc₁.2.1 hc
      subst hl1_eq
      have hall_true : IsAllTrue z := by
        intro i
        obtain ⟨k, hk, hkeq⟩ := finShift_surj_lt s₁ i
        have := hc₁.2.2.1 k hk
        rw [hkeq] at this
        exact this
      exact hall hall_true
    have hl2 : l₂ < w := by
      by_contra hc
      push_neg at hc
      have hl2_eq : l₂ = w := le_antisymm hc₂.2.1 hc
      subst hl2_eq
      have hall_true : IsAllTrue z := by
        intro i
        obtain ⟨k, hk, hkeq⟩ := finShift_surj_lt s₂ i
        have := hc₂.2.2.1 k hk
        rw [hkeq] at this
        exact this
      exact hall hall_true
    have heqk : k₁ = k₂ := eq_k_of_pieces hc₁ hc₂ hl1 hl2 hk₁ hk₂ hkeq₁ hkeq₂
    have hs_eq : s₁ = s₂ := by
      subst heqk
      have h1 : finPred^[k₁] j = s₁ := by
        rw [← hkeq₁, finPred_iterate_finShift_cancel]
      have h2 : finPred^[k₁] j = s₂ := by
        rw [← hkeq₂, finPred_iterate_finShift_cancel]
      rw [← h1, h2]
    subst hs_eq
    have hl_eq : l₁ = l₂ := by
      rcases lt_trichotomy l₁ l₂ with hlt | heq | hlt
      · have hf : z (finShift l₁ s₁) = false := hc₁.2.2.2.1 hl1
        have ht : z (finShift l₁ s₁) = true := hc₂.2.2.1 l₁ hlt
        rw [hf] at ht
        exact False.elim (Bool.false_ne_true ht)
      · exact heq
      · have hf : z (finShift l₂ s₁) = false := hc₂.2.2.2.1 hl2
        have ht : z (finShift l₂ s₁) = true := hc₁.2.2.1 l₂ hlt
        rw [hf] at ht
        exact False.elim (Bool.false_ne_true ht)
    subst hl_eq
    rfl

/-- C0: The number of pieces equals the interval count. -/
theorem intervalCount_eq_card_intervalsOf (z : Config w) :
    intervalCount z = (intervalsOf z).card := by
  unfold intervalCount
  by_cases hw : w = 0
  · rw [if_pos hw]
    have : intervalsOf z = ∅ := by
      ext y
      simp only [Finset.notMem_empty, iff_false, mem_intervalsOf]
      rintro ⟨start, len, hc, -⟩
      have := start.isLt
      omega
    rw [this, Finset.card_empty]
  · rw [if_neg hw]
    have hw_pos : 0 < w := by omega
    by_cases hall : IsAllTrue z
    · rw [if_pos hall]
      have : intervalsOf z = {z} := by
        ext y
        simp only [Finset.mem_singleton, mem_intervalsOf]
        constructor
        · rintro ⟨start, len, hc, rfl⟩
          have hlen : len = w := by
            by_contra hc_ne
            push_neg at hc_ne
            have hlt : len < w := lt_of_le_of_ne hc.2.1 hc_ne
            have hf : z (finShift len start) = false := hc.2.2.2.1 hlt
            have ht : z (finShift len start) = true := hall _
            rw [hf] at ht
            exact False.elim (Bool.false_ne_true ht)
          subst hlen
          ext i
          rw [pieceConfig_full_eq_true]
          exact (hall i).symm
        · intro hy
          rw [hy]
          refine ⟨⟨0, hw_pos⟩, w, ?_, ?_⟩
          · refine ⟨hw_pos, le_refl w, fun k _ => hall _, fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
          · ext i
            rw [pieceConfig_full_eq_true]
            exact hall i
      rw [this, Finset.card_singleton]
    · rw [if_neg hall]
      have heq : Finset.univ.filter (fun i => z (finPred i) = false ∧ z i = true) = risingEdges z := rfl
      rw [heq]
      symm
      apply Finset.card_bij (fun y _ => startOf hw_pos y)
      · intro y hy
        have hy_int := isIntervalConfig_of_mem_intervalsOf hy
        obtain ⟨s₁, l₁, hc₁, rfl⟩ := mem_intervalsOf.mp hy
        have hl1 : l₁ < w := by
          by_contra hc
          push_neg at hc
          have hl1_eq : l₁ = w := le_antisymm hc₁.2.1 hc
          subst hl1_eq
          have hall_true : IsAllTrue z := by
            intro i
            obtain ⟨k, hk, hkeq⟩ := finShift_surj_lt s₁ i
            have := hc₁.2.2.1 k hk
            rw [hkeq] at this
            exact this
          exact hall hall_true
        have h_start_eq : startOf hw_pos (pieceConfig s₁ l₁) = s₁ := (startOf_lenOf_of_piece hc₁.1 hl1 rfl hw_pos).1
        rw [h_start_eq, mem_risingEdges]
        have hf : z (finPred s₁) = false := hc₁.2.2.2.2 hl1
        have ht : z s₁ = true := by
          have := hc₁.2.2.1 0 hc₁.1
          rw [finShift_zero] at this
          exact this
        exact ⟨hf, ht⟩
      · intro y₁ hy₁ y₂ hy₂ hstart
        obtain ⟨s₁, l₁, hc₁, rfl⟩ := mem_intervalsOf.mp hy₁
        obtain ⟨s₂, l₂, hc₂, rfl⟩ := mem_intervalsOf.mp hy₂
        have hl1 : l₁ < w := by
          by_contra hc
          push_neg at hc
          have hl1_eq : l₁ = w := le_antisymm hc₁.2.1 hc
          subst hl1_eq
          have hall_true : IsAllTrue z := by
            intro i
            obtain ⟨k, hk, hkeq⟩ := finShift_surj_lt s₁ i
            have := hc₁.2.2.1 k hk
            rw [hkeq] at this
            exact this
          exact hall hall_true
        have hl2 : l₂ < w := by
          by_contra hc
          push_neg at hc
          have hl2_eq : l₂ = w := le_antisymm hc₂.2.1 hc
          subst hl2_eq
          have hall_true : IsAllTrue z := by
            intro i
            obtain ⟨k, hk, hkeq⟩ := finShift_surj_lt s₂ i
            have := hc₂.2.2.1 k hk
            rw [hkeq] at this
            exact this
          exact hall hall_true
        have h_start1 : startOf hw_pos (pieceConfig s₁ l₁) = s₁ := (startOf_lenOf_of_piece hc₁.1 hl1 rfl hw_pos).1
        have h_start2 : startOf hw_pos (pieceConfig s₂ l₂) = s₂ := (startOf_lenOf_of_piece hc₂.1 hl2 rfl hw_pos).1
        rw [h_start1, h_start2] at hstart
        subst hstart
        have hl_eq : l₁ = l₂ := by
          rcases lt_trichotomy l₁ l₂ with hlt | heq | hlt
          · have hf : z (finShift l₁ s₁) = false := hc₁.2.2.2.1 hl1
            have ht : z (finShift l₁ s₁) = true := hc₂.2.2.1 l₁ hlt
            rw [hf] at ht
            exact False.elim (Bool.false_ne_true ht)
          · exact heq
          · have hf : z (finShift l₂ s₁) = false := hc₂.2.2.2.1 hl2
            have ht : z (finShift l₂ s₁) = true := hc₁.2.2.1 l₂ hlt
            rw [hf] at ht
            exact False.elim (Bool.false_ne_true ht)
        subst hl_eq
        rfl
      · intro i hi
        rw [mem_risingEdges] at hi
        have ht : z i = true := hi.2
        obtain ⟨y, hy, hyi⟩ := exists_piece_mem ht
        refine ⟨y, hy, ?_⟩
        obtain ⟨s₁, l₁, hc₁, rfl⟩ := mem_intervalsOf.mp hy
        have hl1 : l₁ < w := by
          by_contra hc
          push_neg at hc
          have hl1_eq : l₁ = w := le_antisymm hc₁.2.1 hc
          subst hl1_eq
          have hall_true : IsAllTrue z := by
            intro j
            obtain ⟨k, hk, hkeq⟩ := finShift_surj_lt s₁ j
            have := hc₁.2.2.1 k hk
            rw [hkeq] at this
            exact this
          exact hall hall_true
        have h_start1 : startOf hw_pos (pieceConfig s₁ l₁) = s₁ := (startOf_lenOf_of_piece hc₁.1 hl1 rfl hw_pos).1
        rw [h_start1]
        obtain ⟨k, hk, hkeq⟩ := pieceConfig_true_iff.mp hyi
        have h_k_zero : k = 0 := by
          by_contra hk_ne
          have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
          have h_pred : finPred i = finShift (k - 1) s₁ := by
            rw [← hkeq]
            exact finPred_finShift_of_pos hk_pos s₁
          have ht_pred : z (finPred i) = true := by
            rw [h_pred]
            apply hc₁.2.2.1
            omega
          rw [hi.1] at ht_pred
          exact False.elim (Bool.false_ne_true ht_pred)
        subst h_k_zero
        rw [finShift_zero] at hkeq
        exact hkeq

end AllenderOQ3.Internal
