import AllenderOQ3.Internal.StartRank

/-!
# B2-core, combinatorial half (COMB): a rank-successor step forces a rotation

This file discharges the *purely combinatorial* half of the B2 crux
(`AntichainRotationCore.startRotationBetween_of_cyclic_order_preservation`),
leaving only the geometric input.

* `eq_add_of_succ_commute` — the `ZMod` atom: a self-map of `ZMod n` commuting
  with `+ 1` is a translation, `σ i = σ 0 + i`.
* `image_startRank_eq_range` / `exists_mem_startRank_eq` — on an antichain of
  interval configurations the start rank is a bijection onto
  `Finset.range L.card` (injectivity is `startRank_injOn`, the bound is
  `startRank_lt_card`, and a cardinality count upgrades this to surjectivity).
* `isStartRotationBetween_of_rank_succ_step` — **COMB**: if `f` sends
  rank-consecutive members of `A` (consecutive in `ZMod A.card`, i.e.
  cyclically) to rank-consecutive members of `B`, then `f` shifts the start
  rank by a constant offset, i.e. `IsStartRotationBetween hw A.card A B f`.

So the remaining debt in the crux is exactly the geometric statement that a
constant-free layer preserves the cyclic successor of the start order (the
degree-one / single-winding content of the arc-word block reading); feeding
that into `isStartRotationBetween_of_rank_succ_step` closes the crux.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## The `ZMod` atom -/

/-- A self-map of `ZMod n` that commutes with the successor is the translation
by `σ 0`.  (Stated for every `n`, including `n = 0`, where `ZMod 0 = ℤ`; the
induction runs over `ℤ` in both directions.) -/
theorem eq_add_of_succ_commute {n : Nat} (σ : ZMod n → ZMod n)
    (h : ∀ i, σ (i + 1) = σ i + 1) : ∀ i, σ i = σ 0 + i := by
  have key : ∀ k : ℤ, σ ((k : ℤ) : ZMod n) = σ 0 + ((k : ℤ) : ZMod n) := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ m ih =>
      have hcast : (((m : ℤ) + 1 : ℤ) : ZMod n) = ((m : ℤ) : ZMod n) + 1 := by
        push_cast; ring
      rw [hcast, h, ih]
      ring
    | pred m ih =>
      have hcast : ((-(m : ℤ) - 1 : ℤ) : ZMod n) + 1 = ((-(m : ℤ) : ℤ) : ZMod n) := by
        push_cast; ring
      have hstep := h (((-(m : ℤ) - 1 : ℤ) : ZMod n))
      rw [hcast, ih] at hstep
      have hcast2 : ((-(m : ℤ) : ℤ) : ZMod n) = ((-(m : ℤ) - 1 : ℤ) : ZMod n) + 1 := by
        push_cast; ring
      rw [hcast2] at hstep
      have : σ ((-(m : ℤ) - 1 : ℤ) : ZMod n) + 1
          = (σ 0 + ((-(m : ℤ) - 1 : ℤ) : ZMod n)) + 1 := by
        rw [← hstep]; ring
      exact add_right_cancel this
  intro i
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
  exact key k

/-! ## The start rank is a bijection onto an initial segment -/

/-- On an antichain of interval configurations the start rank hits every value
below `L.card`. -/
theorem image_startRank_eq_range (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) :
    L.image (startRank hw L) = Finset.range L.card := by
  have hsub : L.image (startRank hw L) ⊆ Finset.range L.card := by
    intro s hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_range.mpr (startRank_lt_card hw hy)
  have hcard : (L.image (startRank hw L)).card = L.card :=
    Finset.card_image_of_injOn (startRank_injOn hw hInt hanti)
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [hcard, Finset.card_range]

/-- Surjectivity of the start rank onto `{0, …, L.card - 1}`. -/
theorem exists_mem_startRank_eq (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) {k : Nat} (hk : k < L.card) :
    ∃ y ∈ L, startRank hw L y = k := by
  have hmem : k ∈ L.image (startRank hw L) := by
    rw [image_startRank_eq_range hw hInt hanti]
    exact Finset.mem_range.mpr hk
  obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hmem
  exact ⟨y, hy, hyk⟩

/-! ## COMB: cyclic-successor preservation implies a start rotation -/

/-- **COMB half of the B2 crux.**  If `f` maps cyclically rank-consecutive
members of the antichain `A` to cyclically rank-consecutive members of `B`
(the rank being read in `ZMod A.card`), then `f` shifts the start rank by a
constant offset — it is a relative start rotation `A → B`.

No hypothesis on `B` is needed: the successor hypothesis already carries all
information about the target ranks. -/
theorem isStartRotationBetween_of_rank_succ_step (hw : 0 < w) {A B : Finset (Config w)}
    (hAInt : ∀ y ∈ A, IsIntervalConfig y)
    (hAanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
    {f : Config w → Config w}
    (hstep : ∀ x ∈ A, ∀ y ∈ A,
      (startRank hw A y : ZMod A.card) = (startRank hw A x : ZMod A.card) + 1 →
      (startRank hw B (f y) : ZMod A.card) = (startRank hw B (f x) : ZMod A.card) + 1) :
    IsStartRotationBetween hw A.card A B f := by
  rcases Nat.eq_zero_or_pos A.card with hcard0 | hcardpos
  · refine ⟨0, ?_⟩
    intro y hy
    rw [Finset.card_eq_zero.mp hcard0] at hy
    exact absurd hy (Finset.notMem_empty y)
  haveI : NeZero A.card := ⟨by omega⟩
  have hrep : ∀ i : ZMod A.card, ∃ x, x ∈ A ∧
      ((startRank hw A x : Nat) : ZMod A.card) = i := by
    intro i
    obtain ⟨y, hy, hyk⟩ :=
      exists_mem_startRank_eq hw hAInt hAanti (k := i.val) (ZMod.val_lt i)
    refine ⟨y, hy, ?_⟩
    rw [hyk]
    exact ZMod.natCast_rightInverse i
  choose rep hrepmem hrepval using hrep
  set σ : ZMod A.card → ZMod A.card :=
    fun i => ((startRank hw B (f (rep i)) : Nat) : ZMod A.card) with hσdef
  have hsucc : ∀ i, σ (i + 1) = σ i + 1 := by
    intro i
    refine hstep (rep i) (hrepmem i) (rep (i + 1)) (hrepmem (i + 1)) ?_
    rw [hrepval, hrepval]
  have hmain := eq_add_of_succ_commute σ hsucc
  refine ⟨σ 0, ?_⟩
  intro y hy
  set i : ZMod A.card := ((startRank hw A y : Nat) : ZMod A.card) with hidef
  have hreq : rep i = y := by
    have hnat : startRank hw A (rep i) = startRank hw A y :=
      natCast_inj_of_lt (startRank_lt_card hw (hrepmem i)) (startRank_lt_card hw hy)
        (by rw [hrepval i, hidef])
    exact startRank_injOn hw hAInt hAanti (Finset.mem_coe.mpr (hrepmem i))
      (Finset.mem_coe.mpr hy) hnat
  have hval : σ i = ((startRank hw B (f y) : Nat) : ZMod A.card) := by
    change ((startRank hw B (f (rep i)) : Nat) : ZMod A.card) = _
    rw [hreq]
  have := hmain i
  rw [hval] at this
  rw [this, hidef]
  ring

end Internal
end AllenderOQ3
