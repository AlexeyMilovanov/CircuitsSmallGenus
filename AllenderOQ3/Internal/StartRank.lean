import AllenderOQ3.Internal.IntervalStart

/-!
# Start rank and rotations of a finite cyclic order (Part B, B3/B4)

For a `Finset L` of interval configurations forming an antichain (paper §4,
plan item T-P2/B3), the canonical start `startOf` is injective on `L`
(`startOf_injOn`), and the **start rank** — the number of members whose start
is strictly smaller — is an order isomorphism `L ≃ Fin L.card` in disguise
(`startRank_injOn`, `startRank_lt_card`).

Reading the rank in `ZMod L.card` linearizes the cyclic order: a *rotation* of
the start cycle is exactly a constant additive offset on the rank
(`IsStartRotation`).  The single mathematical payload of this file is that two
rotations of one finite cyclic order commute (`startRotations_commute`): the
composite ranks differ by `c + d` versus `d + c`, equal by `add_comm`, and the
rank is injective on `L`.

This is the B3 ("rotations commute") + B4 ("transfer to the permutation")
content of the section; the geometric input that `runTrans m` *is* a start
rotation (B2) is discharged separately.  Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## Start injectivity on an antichain -/

/-- On an antichain of interval configurations, the canonical start is
injective (distinct members are incomparable, so their starts differ by
`startOf_ne_of_incomparable`). -/
theorem startOf_injOn (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) :
    Set.InjOn (startOf hw) ↑L := by
  intro x hx y hy hxy
  simp only [Finset.mem_coe] at hx hy
  by_contra hne
  have hnc : ¬ x ≤ y := fun h => hne (hanti x hx y hy h)
  have hnc' : ¬ y ≤ x := fun h => hne ((hanti y hy x hx h).symm)
  exact startOf_ne_of_incomparable (hInt x hx) (hInt y hy) hw hnc hnc' hxy

/-! ## Start rank -/

open Classical in
/-- The **start rank** of `y` relative to `L`: the number of distinct member
starts strictly below `startOf y`.  On `L` this is the position of `y` in the
start-sorted order. -/
noncomputable def startRank (hw : 0 < w) (L : Finset (Config w)) (y : Config w) : Nat :=
  ((L.image (startOf hw)).filter (fun s => s < startOf hw y)).card

/-- The rank of a member is `< L.card`. -/
theorem startRank_lt_card (hw : 0 < w) {L : Finset (Config w)} {y : Config w}
    (hy : y ∈ L) : startRank hw L y < L.card := by
  have hmem : startOf hw y ∈ L.image (startOf hw) := Finset.mem_image_of_mem _ hy
  have hsub : (L.image (startOf hw)).filter (fun s => s < startOf hw y)
      ⊆ (L.image (startOf hw)).erase (startOf hw y) := by
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [Finset.mem_erase]
    exact ⟨ne_of_lt hs.2, hs.1⟩
  calc startRank hw L y
      ≤ ((L.image (startOf hw)).erase (startOf hw y)).card := Finset.card_le_card hsub
    _ < (L.image (startOf hw)).card := Finset.card_erase_lt_of_mem hmem
    _ ≤ L.card := Finset.card_image_le

/-- The start rank is strictly monotone in the start, hence injective on the
antichain. -/
theorem startRank_injOn (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) :
    Set.InjOn (startRank hw L) ↑L := by
  have hstartinj := startOf_injOn hw hInt hanti
  have hmono : ∀ x ∈ L, ∀ y ∈ L, startOf hw x < startOf hw y →
      startRank hw L x < startRank hw L y := by
    intro x hx y hy hlt
    unfold startRank
    apply Finset.card_lt_card
    have hsub : (L.image (startOf hw)).filter (fun s => s < startOf hw x)
        ⊆ (L.image (startOf hw)).filter (fun s => s < startOf hw y) := by
      intro s hs
      rw [Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, lt_trans hs.2 hlt⟩
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨startOf hw x, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_image_of_mem _ hx, hlt⟩
    · rw [Finset.mem_filter]
      rintro ⟨-, h⟩
      exact absurd h (lt_irrefl _)
  intro x hx y hy hxy
  simp only [Finset.mem_coe] at hx hy
  by_contra hne
  have hsne : startOf hw x ≠ startOf hw y := fun h =>
    hne (hstartinj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h)
  rcases lt_trichotomy (startOf hw x) (startOf hw y) with h | h | h
  · exact absurd hxy (ne_of_lt (hmono x hx y hy h))
  · exact hsne h
  · exact absurd hxy.symm (ne_of_lt (hmono y hy x hx h))

/-! ## Rotations of the start cycle -/

/-- Two naturals below `n` with equal image in `ZMod n` are equal. -/
theorem natCast_inj_of_lt {n a b : Nat} (ha : a < n) (hb : b < n)
    (h : (a : ZMod n) = (b : ZMod n)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

open Classical in
/-- `f` is a **start rotation** of `L`: on `L`, the start rank shifts by a
constant offset `c` in `ZMod L.card`.  This is the linearized form of "a
rotation of the finite cyclic order of starts". -/
def IsStartRotation (hw : 0 < w) (L : Finset (Config w)) (f : Config w → Config w) : Prop :=
  ∃ c : ZMod L.card, ∀ y ∈ L,
    (startRank hw L (f y) : ZMod L.card) = (startRank hw L y : ZMod L.card) + c

open Classical in
/-- **Relative form.**  `f` shifts the start rank by a constant offset `c : ZMod n`
when transported from the antichain `A` to the antichain `B`.  With `n = A.card`
and `A = B = L` this is exactly `IsStartRotation`; the extra generality lets the
per-layer rotations of a word compose (all with the fixed modulus `n = L.card`,
since every intermediate image has the same cardinality). -/
def IsStartRotationBetween (hw : 0 < w) (n : Nat) (A B : Finset (Config w))
    (f : Config w → Config w) : Prop :=
  ∃ c : ZMod n, ∀ y ∈ A,
    (startRank hw B (f y) : ZMod n) = (startRank hw A y : ZMod n) + c

/-- `IsStartRotation` is the self, canonical-modulus case of the relative form. -/
theorem isStartRotation_of_between_self (hw : 0 < w) {L : Finset (Config w)}
    {f : Config w → Config w} (h : IsStartRotationBetween hw L.card L L f) :
    IsStartRotation hw L f := h

/-- Offsets add along a composite of relative rotations sharing the modulus `n`. -/
theorem isStartRotationBetween_trans (hw : 0 < w) {n : Nat}
    {A B C : Finset (Config w)} {f g : Config w → Config w}
    (hf : IsStartRotationBetween hw n A B f) (hg : IsStartRotationBetween hw n B C g)
    (hfm : Set.MapsTo f ↑A ↑B) :
    IsStartRotationBetween hw n A C (fun x => g (f x)) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c + d, ?_⟩
  intro y hy
  have hfy : f y ∈ B := Finset.mem_coe.mp (hfm (Finset.mem_coe.mpr hy))
  rw [hd (f y) hfy, hc y hy]
  ring

/-- **B3 + B4.**  Two start rotations of one antichain commute element-wise: the
two composite ranks are `startRank x + d + c` and `startRank x + c + d`, equal by
`add_comm`, and the rank is injective on `L`. -/
theorem startRotations_commute (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y)
    {f g : Config w → Config w}
    (hf : IsStartRotation hw L f) (hg : IsStartRotation hw L g)
    (hfm : Set.MapsTo f ↑L ↑L) (hgm : Set.MapsTo g ↑L ↑L)
    {x : Config w} (hx : x ∈ L) :
    f (g x) = g (f x) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  have hgx : g x ∈ L := Finset.mem_coe.mp (hgm (Finset.mem_coe.mpr hx))
  have hfx : f x ∈ L := Finset.mem_coe.mp (hfm (Finset.mem_coe.mpr hx))
  have hfgx : f (g x) ∈ L := Finset.mem_coe.mp (hfm (Finset.mem_coe.mpr hgx))
  have hgfx : g (f x) ∈ L := Finset.mem_coe.mp (hgm (Finset.mem_coe.mpr hfx))
  have e1 : (startRank hw L (f (g x)) : ZMod L.card)
      = (startRank hw L x : ZMod L.card) + d + c := by
    rw [hc (g x) hgx, hd x hx]
  have e2 : (startRank hw L (g (f x)) : ZMod L.card)
      = (startRank hw L x : ZMod L.card) + c + d := by
    rw [hd (f x) hfx, hc x hx]
  have eZ : (startRank hw L (f (g x)) : ZMod L.card)
      = (startRank hw L (g (f x)) : ZMod L.card) := by
    rw [e1, e2]; ring
  have eN : startRank hw L (f (g x)) = startRank hw L (g (f x)) :=
    natCast_inj_of_lt (startRank_lt_card hw hfgx) (startRank_lt_card hw hgfx) eZ
  exact startRank_injOn hw hInt hanti (Finset.mem_coe.mpr hfgx) (Finset.mem_coe.mpr hgfx) eN

end Internal
end AllenderOQ3
