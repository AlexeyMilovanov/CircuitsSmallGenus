import AllenderOQ3.Internal.IntervalPieces

/-!
# Canonical start and length of an interval configuration

An interval configuration (`IsIntervalConfig`) determines its block
canonically: the *start* is the unique rising edge (or `0` for the full
configuration, which has none), the *length* is the number of `true`
coordinates.  This file proves the canonicalization
(`isCyclicInterval_canonical`, `eq_pieceConfig_canonical`) and its direct
consequences:

* `startOf_eq_of_witness` — any block witness has the canonical start (for
  proper blocks);
* `le_of_startOf_eq` — two interval configurations with the same start are
  comparable, with the shorter below the longer.

These are the combinatorial substrate for the cyclic-rotation analysis of
antichains of interval configurations (HMV Lemma 10).

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## Rising edges -/

open Classical in
/-- The rising edges of a configuration: `false` before, `true` at. -/
noncomputable def risingEdges (y : Config w) : Finset (Fin w) :=
  Finset.univ.filter (fun i => y (finPred i) = false ∧ y i = true)

theorem mem_risingEdges {y : Config w} {i : Fin w} :
    i ∈ risingEdges y ↔ y (finPred i) = false ∧ y i = true := by
  simp [risingEdges]

/-- Stepping back from a positive shift. -/
theorem finPred_finShift_of_pos {k : Nat} (hk : 0 < k) (j : Fin w) :
    finPred (finShift k j) = finShift (k - 1) j := by
  have h1 : finShift k j = finShift 1 (finShift (k - 1) j) := by
    rw [finShift_finShift]
    congr 1
    omega
  rw [h1, finPred_shift_one]

/-- A proper block has exactly one rising edge: its start. -/
theorem risingEdges_pieceConfig {start : Fin w} {len : Nat}
    (hpos : 0 < len) (hlt : len < w) :
    risingEdges (pieceConfig start len) = {start} := by
  ext i
  rw [mem_risingEdges, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨k, hk, hkeq⟩ := pieceConfig_true_iff.mp h2
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, finShift_zero] at hkeq
      exact hkeq.symm
    · exfalso
      have hpred : finPred i = finShift (k - 1) start := by
        rw [← hkeq]
        exact finPred_finShift_of_pos hk0 start
      have : pieceConfig start len (finPred i) = true := by
        rw [hpred]
        exact pieceConfig_true_iff.mpr ⟨k - 1, by omega, rfl⟩
      rw [h1] at this
      exact Bool.false_ne_true this
  · intro heq
    rw [heq]
    refine ⟨?_, pieceConfig_true_iff.mpr ⟨0, hpos, by simp⟩⟩
    cases hval : pieceConfig start len (finPred start) with
    | false => rfl
    | true =>
      obtain ⟨k, hk, hkeq⟩ := pieceConfig_true_iff.mp hval
      have hw : 0 < w := start.pos
      have hpred : finPred start = finShift (w - 1) start := rfl
      rw [hpred] at hkeq
      have hkw : k = w - 1 := finShift_amount_inj (by omega) (by omega) hkeq
      omega

/-- The full block has no rising edge. -/
theorem risingEdges_pieceConfig_full {start : Fin w} :
    risingEdges (pieceConfig start w) = ∅ := by
  ext i
  rw [mem_risingEdges]
  simp only [Finset.notMem_empty, iff_false]
  rintro ⟨h1, -⟩
  obtain ⟨k, hk, hkeq⟩ := finShift_surj_lt start (finPred i)
  have : pieceConfig start w (finPred i) = true :=
    pieceConfig_true_iff.mpr ⟨k, hk, hkeq⟩
  rw [h1] at this
  exact Bool.false_ne_true this

/-! ## Canonical data -/

open Classical in
/-- The canonical start: the unique rising edge, or `0` for the full
configuration. -/
noncomputable def startOf (hw : 0 < w) (y : Config w) : Fin w :=
  if h : (risingEdges y).Nonempty then h.choose else ⟨0, hw⟩

open Classical in
/-- The canonical length: the number of `true` coordinates. -/
noncomputable def lenOf (y : Config w) : Nat :=
  (Finset.univ.filter (fun i => y i = true)).card

/-- The `true` set of a block is the injective image of `Finset.range len`. -/
theorem filter_pieceConfig_eq_image {start : Fin w} {len : Nat} :
    (Finset.univ.filter (fun i => pieceConfig start len i = true))
      = (Finset.range len).image (fun k => finShift k start) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_range]
  rw [pieceConfig_true_iff]

theorem lenOf_pieceConfig {start : Fin w} {len : Nat} (hle : len ≤ w) :
    lenOf (pieceConfig start len) = len := by
  rw [lenOf, filter_pieceConfig_eq_image, Finset.card_image_of_injOn,
    Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  exact finShift_amount_inj (by omega) (by omega) hab

/-- **Canonicalization of a proper block.** -/
theorem startOf_lenOf_of_piece {y : Config w} {start : Fin w} {len : Nat}
    (hpos : 0 < len) (hlt : len < w) (hy : y = pieceConfig start len) (hw : 0 < w) :
    startOf hw y = start ∧ lenOf y = len := by
  have hedge : risingEdges y = {start} := by
    rw [hy]
    exact risingEdges_pieceConfig hpos hlt
  constructor
  · rw [startOf]
    have hne : (risingEdges y).Nonempty := by
      rw [hedge]
      exact ⟨start, Finset.mem_singleton_self start⟩
    rw [dif_pos hne]
    have hmem : hne.choose ∈ ({start} : Finset (Fin w)) := by
      rw [← hedge]
      exact hne.choose_spec
    exact Finset.mem_singleton.mp hmem
  · rw [hy]
    exact lenOf_pieceConfig (by omega)

/-- **Canonicalization of the full block.** -/
theorem startOf_lenOf_of_piece_full {y : Config w} {start : Fin w}
    (hy : y = pieceConfig start w) (hw : 0 < w) :
    startOf hw y = ⟨0, hw⟩ ∧ lenOf y = w := by
  constructor
  · rw [startOf]
    have hemp : ¬ (risingEdges y).Nonempty := by
      rw [hy, risingEdges_pieceConfig_full]
      exact fun h => Finset.not_nonempty_empty h
    rw [dif_neg hemp]
  · rw [hy]
    exact lenOf_pieceConfig (le_refl w)

/-- **Every interval configuration is its own canonical block.** -/
theorem eq_pieceConfig_canonical {y : Config w} (h : IsIntervalConfig y) (hw : 0 < w) :
    0 < lenOf y ∧ lenOf y ≤ w ∧ y = pieceConfig (startOf hw y) (lenOf y) := by
  obtain ⟨start, len, hcyc, hy⟩ := h
  obtain ⟨hpos, hlew, htrue, hright, hleft⟩ := hcyc
  rcases Nat.lt_or_ge len w with hlt | hge
  · obtain ⟨hs, hl⟩ := startOf_lenOf_of_piece hpos hlt hy hw
    refine ⟨by rw [hl]; omega, by rw [hl]; omega, ?_⟩
    rw [hs, hl]
    exact hy
  · have hlen : len = w := by omega
    rw [hlen] at hy
    obtain ⟨hs, hl⟩ := startOf_lenOf_of_piece_full hy hw
    refine ⟨by rw [hl]; omega, by rw [hl], ?_⟩
    rw [hs, hl, hy]
    funext j
    have h1 : pieceConfig start w j = true := by
      obtain ⟨k, hk, hkeq⟩ := finShift_surj_lt start j
      exact pieceConfig_true_iff.mpr ⟨k, hk, hkeq⟩
    have h2 : pieceConfig (⟨0, hw⟩ : Fin w) w j = true := by
      obtain ⟨k, hk, hkeq⟩ := finShift_surj_lt (⟨0, hw⟩ : Fin w) j
      exact pieceConfig_true_iff.mpr ⟨k, hk, hkeq⟩
    rw [h1, h2]

/-- **Interval configurations with a common start are comparable**: the shorter
is below the longer. -/
theorem le_of_startOf_eq {y z : Config w} (hy : IsIntervalConfig y)
    (hz : IsIntervalConfig z) (hw : 0 < w)
    (hstart : startOf hw y = startOf hw z) (hlen : lenOf y ≤ lenOf z) : y ≤ z := by
  obtain ⟨-, hylew, hyeq⟩ := eq_pieceConfig_canonical hy hw
  obtain ⟨-, hzlew, hzeq⟩ := eq_pieceConfig_canonical hz hw
  intro j
  by_cases hyj : y j = true
  · have hzj : z j = true := by
      rw [hyeq] at hyj
      obtain ⟨k, hk, hkeq⟩ := pieceConfig_true_iff.mp hyj
      rw [hzeq]
      refine pieceConfig_true_iff.mpr ⟨k, by omega, ?_⟩
      rw [← hstart]
      exact hkeq
    rw [hyj, hzj]
  · have hyj' : y j = false := by
      cases hval : y j with
      | false => rfl
      | true => exact absurd hval hyj
    rw [hyj']
    exact Bool.false_le _

/-- Distinct incomparable interval configurations have distinct starts. -/
theorem startOf_ne_of_incomparable {y z : Config w} (hy : IsIntervalConfig y)
    (hz : IsIntervalConfig z) (hw : 0 < w)
    (hnc : ¬ y ≤ z) (hnc' : ¬ z ≤ y) : startOf hw y ≠ startOf hw z := by
  intro heq
  rcases Nat.lt_or_ge (lenOf y) (lenOf z) with h | h
  · exact hnc (le_of_startOf_eq hy hz hw heq (by omega))
  · exact hnc' (le_of_startOf_eq hz hy hw heq.symm h)

end Internal
end AllenderOQ3
