import AllenderOQ3.Internal.IntervalStart
import AllenderOQ3.Internal.IntervalPieces

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical

namespace AllenderOQ3.Internal

variable {w : Nat}

theorem intervalCount_eq_card_risingEdges (s : Config w) (hw : 0 < w) (h : ¬ IsAllTrue s) :
    intervalCount s = (risingEdges s).card := by
  unfold intervalCount
  rw [if_neg (ne_of_gt hw)]
  rw [if_neg h]
  rfl

theorem intervalCount_eq_one_of_isIntervalConfig (hw : 0 < w) {y : Config w} (h : IsIntervalConfig y) : intervalCount y = 1 := by
  unfold IsIntervalConfig IsIntervalPiece at h
  rcases h with ⟨start, len, hcyc, rfl⟩
  have hlen : 0 < len ∧ len ≤ w := ⟨hcyc.1, hcyc.2.1⟩
  by_cases hlen_w : len = w
  · have hall : IsAllTrue (pieceConfig start len) := by
      intro i
      rw [pieceConfig_true_iff]
      obtain ⟨k, hk_lt, hk_eq⟩ := finShift_surj_lt start i
      exact ⟨k, by rw [hlen_w]; exact hk_lt, hk_eq⟩
    exact intervalCount_one_iff_allTrue _ hw hall
  · have hlen_lt : len < w := lt_of_le_of_ne hlen.2 hlen_w
    have hall : ¬ IsAllTrue (pieceConfig start len) := by
      intro h
      have h1 := h (finPred start)
      have h2 := hcyc.2.2.2.2 hlen_lt
      rw [h2] at h1
      exact Bool.false_ne_true h1
    rw [intervalCount_eq_card_risingEdges _ hw hall]
    rw [risingEdges_pieceConfig hlen.1 hlen_lt]
    exact Finset.card_singleton start

theorem isIntervalConfig_of_intervalCount_eq_one (hw : 0 < w) {y : Config w} (h : intervalCount y = 1) : IsIntervalConfig y := by
  by_cases hall : IsAllTrue y
  · refine ⟨⟨0, hw⟩, w, ?_, ?_⟩
    · refine ⟨hw, le_refl w, fun k _ => hall _, fun h => absurd h (lt_irrefl w), fun h => absurd h (lt_irrefl w)⟩
    · ext j
      have : y j = true := hall j
      rw [this]
      symm
      rw [pieceConfig_true_iff]
      obtain ⟨k, hk_lt, hk_eq⟩ := finShift_surj_lt ⟨0, hw⟩ j
      exact ⟨k, hk_lt, hk_eq⟩
  · have h1 : (risingEdges y).card = 1 := by
      rw [← intervalCount_eq_card_risingEdges y hw hall]
      exact h
    have h1_ex : ∃ a, risingEdges y = {a} := Finset.card_eq_one.mp h1
    rcases h1_ex with ⟨start, hstart⟩
    have hrising : start ∈ risingEdges y := by rw [hstart]; apply Finset.mem_singleton.mpr rfl
    rw [mem_risingEdges] at hrising
    obtain ⟨start', len', hcyc⟩ := exists_isCyclicInterval y start hrising.2
    have hlen'_lt : len' < w := by
      by_contra hc
      push_neg at hc
      have h_eq : len' = w := le_antisymm hcyc.2.1 hc
      have hall' : IsAllTrue y := by
        intro i
        obtain ⟨k, hk_lt, hk_eq⟩ := finShift_surj_lt start' i
        rw [← hk_eq]
        exact hcyc.2.2.1 k (by rw [h_eq]; exact hk_lt)
      exact hall hall'
    have hrising' : start' ∈ risingEdges y := by
      rw [mem_risingEdges]
      have ht : y start' = true := by
        have := hcyc.2.2.1 0 hcyc.1
        rw [finShift_zero] at this
        exact this
      exact ⟨hcyc.2.2.2.2 hlen'_lt, ht⟩
    have h_start_eq : start' = start := by
      have h_in : start' ∈ ({start} : Finset (Fin w)) := by rw [← hstart]; exact hrising'
      exact Finset.mem_singleton.mp h_in
    rw [h_start_eq] at hcyc
    refine ⟨start, len', hcyc, ?_⟩
    ext j
    cases h_j : y j
    · symm
      cases h_p : pieceConfig start len' j
      · rfl
      · rw [pieceConfig_true_iff] at h_p
        obtain ⟨k, hk_lt, hk_eq⟩ := h_p
        have := hcyc.2.2.1 k hk_lt
        rw [hk_eq] at this
        rw [this] at h_j
        exact False.elim (Bool.false_ne_true h_j.symm)
    · have hyj : y j = true := h_j
      rw [mem_intervalsOf_true_iff] at hyj
      obtain ⟨y_piece, hy_piece, hy_piece_j⟩ := hyj
      rw [mem_intervalsOf] at hy_piece
      obtain ⟨s, l, hcyc_s, rfl⟩ := hy_piece
      have hl_lt : l < w := by
        by_contra hc
        push_neg at hc
        have h_eq : l = w := le_antisymm hcyc_s.2.1 hc
        have hall' : IsAllTrue y := by
          intro i
          obtain ⟨k, hk_lt, hk_eq⟩ := finShift_surj_lt s i
          rw [← hk_eq]
          exact hcyc_s.2.2.1 k (by rw [h_eq]; exact hk_lt)
        exact hall hall'
      have h_s_rising : s ∈ risingEdges y := by
        rw [mem_risingEdges]
        have ht : y s = true := by
          have := hcyc_s.2.2.1 0 hcyc_s.1
          rw [finShift_zero] at this
          exact this
        exact ⟨hcyc_s.2.2.2.2 hl_lt, ht⟩
      have h_s_eq : s = start := by
        have h_in : s ∈ ({start} : Finset (Fin w)) := by rw [← hstart]; exact h_s_rising
        exact Finset.mem_singleton.mp h_in
      rw [h_s_eq] at hcyc_s hy_piece_j
      have h_l_eq : l = len' := by
        rcases lt_trichotomy l len' with hlt | heq | hgt
        · have hf : y (finShift l start) = false := hcyc_s.2.2.2.1 hl_lt
          have ht : y (finShift l start) = true := hcyc.2.2.1 l hlt
          rw [hf] at ht
          have ht_rev : false = true := ht
          exact False.elim (Bool.false_ne_true ht_rev)
        · exact heq
        · have hf : y (finShift len' start) = false := hcyc.2.2.2.1 hlen'_lt
          have ht : y (finShift len' start) = true := hcyc_s.2.2.1 len' hgt
          rw [hf] at ht
          have ht_rev : false = true := ht
          exact False.elim (Bool.false_ne_true ht_rev)
      rw [h_l_eq] at hy_piece_j
      symm
      exact hy_piece_j

theorem intervalsOf_eq_singleton_of_isIntervalConfig (_hw : 0 < w) {y : Config w} (h : IsIntervalConfig y) : intervalsOf y = {y} := by
  ext y'
  constructor
  · intro hy'
    rw [mem_intervalsOf] at hy'
    obtain ⟨s, l, hs, rfl⟩ := hy'
    unfold IsIntervalConfig IsIntervalPiece at h
    obtain ⟨start, len, hcyc, rfl⟩ := h
    have hlen : 0 < len ∧ len ≤ w := ⟨hcyc.1, hcyc.2.1⟩
    by_cases hlen_w : len = w
    · have hall : IsAllTrue (pieceConfig start len) := by
        intro i
        rw [pieceConfig_true_iff]
        obtain ⟨k, hk_lt, hk_eq⟩ := finShift_surj_lt start i
        exact ⟨k, by rw [hlen_w]; exact hk_lt, hk_eq⟩
      have hl_w : l = w := by
        by_contra hc
        push_neg at hc
        have hlt : l < w := lt_of_le_of_ne hs.2.1 hc
        have hf : pieceConfig start len (finShift l s) = false := hs.2.2.2.1 hlt
        have ht : pieceConfig start len (finShift l s) = true := hall _
        rw [hf] at ht
        have ht_rev : false = true := ht
        exact Bool.false_ne_true ht_rev
      rw [hl_w, hlen_w]
      have hy'_eq_y : pieceConfig s w = pieceConfig start w := by
        ext j
        have h1 : pieceConfig s w j = true := by
          rw [pieceConfig_true_iff]
          obtain ⟨k, hk_lt, hk_eq⟩ := finShift_surj_lt s j
          exact ⟨k, hk_lt, hk_eq⟩
        have h2 : pieceConfig start w j = true := by
          rw [pieceConfig_true_iff]
          obtain ⟨k, hk_lt, hk_eq⟩ := finShift_surj_lt start j
          exact ⟨k, hk_lt, hk_eq⟩
        rw [h1, h2]
      rw [hy'_eq_y]
      exact Finset.mem_singleton.mpr rfl
    · have hlen_lt : len < w := lt_of_le_of_ne hlen.2 hlen_w
      have hl_lt : l < w := by
        by_contra hc
        push_neg at hc
        have h_eq : l = w := le_antisymm hs.2.1 hc
        have hall' : IsAllTrue (pieceConfig start len) := by
          intro i
          obtain ⟨k, hk_lt, hk_eq⟩ := finShift_surj_lt s i
          rw [← hk_eq]
          exact hs.2.2.1 k (by rw [h_eq]; exact hk_lt)
        have hf : pieceConfig start len (finShift len start) = false := hcyc.2.2.2.1 hlen_lt
        have ht : pieceConfig start len (finShift len start) = true := hall' _
        rw [hf] at ht
        have ht_rev : false = true := ht
        exact Bool.false_ne_true ht_rev
      have h_s_rising : s ∈ risingEdges (pieceConfig start len) := by
        rw [mem_risingEdges]
        have ht : pieceConfig start len s = true := by
          have := hs.2.2.1 0 hs.1
          rw [finShift_zero] at this
          exact this
        exact ⟨hs.2.2.2.2 hl_lt, ht⟩
      have h_s_eq : s = start := by
        have h1 : risingEdges (pieceConfig start len) = {start} := risingEdges_pieceConfig hlen.1 hlen_lt
        rw [h1] at h_s_rising
        exact Finset.mem_singleton.mp h_s_rising
      rw [h_s_eq] at hs
      have h_l_eq : l = len := by
        rcases lt_trichotomy l len with hlt | heq | hgt
        · have hf : pieceConfig start len (finShift l start) = false := hs.2.2.2.1 hl_lt
          have ht : pieceConfig start len (finShift l start) = true := hcyc.2.2.1 l hlt
          rw [hf] at ht
          have ht_rev : false = true := ht
          exact False.elim (Bool.false_ne_true ht_rev)
        · exact heq
        · have hf : pieceConfig start len (finShift len start) = false := hcyc.2.2.2.1 hlen_lt
          have ht : pieceConfig start len (finShift len start) = true := hs.2.2.1 len hgt
          rw [hf] at ht
          have ht_rev : false = true := ht
          exact False.elim (Bool.false_ne_true ht_rev)
      rw [h_s_eq, h_l_eq]
      exact Finset.mem_singleton.mpr rfl
  · intro hy'
    have : y' = y := Finset.mem_singleton.mp hy'
    rw [this]
    exact mem_intervalsOf.mpr h

end AllenderOQ3.Internal
