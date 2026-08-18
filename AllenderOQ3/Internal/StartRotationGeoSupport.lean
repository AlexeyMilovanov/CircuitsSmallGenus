import AllenderOQ3.Internal.StartSuccBridge
import AllenderOQ3.Internal.ConstantFreeLayers
import AllenderOQ3.Internal.StartRotationLive
import AllenderOQ3.Internal.GeoLiftAssembly
import AllenderOQ3.Internal.StartRotationRankShift

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- **The target-side degree-one lift (GEO — open geometric leaf).**  A
constant-free map `g` bijecting a top-free antichain of interval configurations
`A` onto another such antichain `B` induces, on the canonical start coordinates,
a lift `F : ℕ → ℕ` that is degree one (`F (x + w) = F x + w`), weakly monotone,
and computes the output start of every member of `A` by reduction `mod w`.

This is the genuine geometric content of the section (paper §4 / plan 6c): the
arcs emitted from an interval form a contiguous block of the common arc word
(`StartRotationLive.exists_arcWord_true_source_block`), and reading the block
gives the target-side first-true cut map, whose single-winding is exactly the
degree-one property `F (x + w) = F x + w`.  Once produced, the pure combinatorics
(`isStartRotationBetween_of_degree_one_lift`) turns it into a start rotation. -/
theorem exists_degree_one_lift_of_constantFreeMap (hw : 0 < w) {g : TransMonoid w}
    (hg : isConstantFreeMap w g) {A B : Finset (Config w)}
    (hA : ∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hB : ∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hAanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
    (hBanti : ∀ x ∈ B, ∀ y ∈ B, x ≤ y → x = y)
    (hbij : Set.BijOn (runTrans g) ↑A ↑B) :
    ∃ (F : Nat → Nat),
      (∀ x, F (x + w) = F x + w) ∧
      (∀ x y, x ≤ y → F x ≤ F y) ∧
      (∀ x ∈ A, (F (startOf hw x).val) % w = (startOf hw (runTrans g x)).val) :=
  exists_degree_one_lift_of_constantFreeMap_assembled hw hg hA hB hAanti hBanti hbij

/-- **The pure-combinatorial half of GEO.**  A degree-one, weakly monotone lift
`F` that computes the output starts of a *bijection* `f : A → B` between two
top-free interval antichains realizes `f` as a **relative start rotation**: the
start rank shifts by the constant offset "number of wrapping members" in
`ZMod A.card`.

The proof reduces to `StartRotationRankShift.rotation_rank_shift`: writing every
`F (start z)` in the window `[m, m + w)` (where `m` is the minimum such value,
the strict upper bound using injectivity of `f` and of `startOf` on `B`), the
output start is `(r + v z) % w` for a fixed rotation amount `r = m % w`, so the
rotation lemma applies verbatim. -/
theorem isStartRotationBetween_of_degree_one_lift (hw : 0 < w)
    {A B : Finset (Config w)}
    (hA : ∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hB : ∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hAanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
    (hBanti : ∀ x ∈ B, ∀ y ∈ B, x ≤ y → x = y)
    {f : Config w → Config w}
    (hbij : Set.BijOn f ↑A ↑B)
    (hF : ∃ F : Nat → Nat,
      (∀ x, F (x + w) = F x + w) ∧
      (∀ x y, x ≤ y → F x ≤ F y) ∧
      (∀ x ∈ A, (F (startOf hw x).val) % w = (startOf hw (f x)).val)) :
    IsStartRotationBetween hw A.card A B f := by
  classical
  have hAInt : ∀ z ∈ A, IsIntervalConfig z := fun z hz => (hA z hz).1
  have hBInt : ∀ z ∈ B, IsIntervalConfig z := fun z hz => (hB z hz).1
  obtain ⟨F, hFper, hFmono, hFstart⟩ := hF
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · exact ⟨0, fun y hy => absurd hy (by rw [hAe]; exact Finset.notMem_empty y)⟩
  -- The window minimum `m` of the lifted starts.
  have himgne : (A.image (fun z => F (startOf hw z).val)).Nonempty := hAne.image _
  set m : Nat := (A.image (fun z => F (startOf hw z).val)).min' himgne with hm
  have hm_le : ∀ z ∈ A, m ≤ F (startOf hw z).val := fun z hz =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ hz)
  obtain ⟨z0, hz0A, hz0m⟩ := Finset.mem_image.mp (Finset.min'_mem _ himgne)
  -- Basic dictionary: output start is `F (start ·) % w`; `startOf` is injective on `B`.
  have hbrel : ∀ z ∈ A, (startOf hw (f z)).val = F (startOf hw z).val % w :=
    fun z hz => (hFstart z hz).symm
  have hstartinjB : Set.InjOn (startOf hw) ↑B := startOf_injOn hw hBInt hBanti
  -- `F` is *strictly* monotone along the starts of `A` (output starts are distinct).
  have hFstrict : ∀ z ∈ A, ∀ z' ∈ A,
      (startOf hw z').val < (startOf hw z).val →
        F (startOf hw z').val < F (startOf hw z).val := by
    intro z hz z' hz' hlt
    rcases lt_or_eq_of_le (hFmono _ _ (le_of_lt hlt)) with h | h
    · exact h
    · exfalso
      have hval : (startOf hw (f z')).val = (startOf hw (f z)).val := by
        rw [hbrel z' hz', hbrel z hz, h]
      have hfeq : f z' = f z :=
        hstartinjB (hbij.mapsTo hz') (hbij.mapsTo hz) (Fin.ext hval)
      exact absurd (hbij.injOn hz' hz hfeq ▸ hlt) (lt_irrefl _)
  -- Window: every lifted start is `< m + w` (strictness again from distinctness).
  have hwin : ∀ z ∈ A, F (startOf hw z).val < m + w := by
    intro z hz
    have hle : F (startOf hw z).val ≤ m + w := by
      have hstep : (startOf hw z).val ≤ (startOf hw z0).val + w := by
        have := (startOf hw z).isLt; omega
      calc F (startOf hw z).val ≤ F ((startOf hw z0).val + w) := hFmono _ _ hstep
        _ = F (startOf hw z0).val + w := hFper _
        _ = m + w := by rw [hz0m]
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hbz : (startOf hw (f z)).val = m % w := by
        rw [hbrel z hz, h, Nat.add_mod_right]
      have hbz0 : (startOf hw (f z0)).val = m % w := by rw [hbrel z0 hz0A, hz0m]
      have hfeq : f z = f z0 :=
        hstartinjB (hbij.mapsTo hz) (hbij.mapsTo hz0A) (Fin.ext (by rw [hbz, hbz0]))
      have hzz0 : z = z0 := hbij.injOn hz hz0A hfeq
      rw [hzz0, hz0m] at h; omega
  -- The rotation data `v`, `r`.
  set v : Config w → Nat := fun z => F (startOf hw z).val - m with hv
  have hvw : ∀ z ∈ A, v z < w := by
    intro z hz; have h1 := hwin z hz; have h2 := hm_le z hz; simp only [hv]; omega
  set r : Nat := m % w with hr
  have hrw : r < w := Nat.mod_lt _ hw
  -- Output start is exactly the rotation `(r + v z) % w`.
  have hbmod : ∀ z ∈ A, (startOf hw (f z)).val = (r + v z) % w := by
    intro z hz
    have hmv : F (startOf hw z).val = m + v z := by
      have := hm_le z hz; simp only [hv]; omega
    rw [hbrel z hz, hmv, hr]
    exact ((Nat.mod_modEq m w).add_right (v z)).symm
  -- Order equivalence: raw start order equals `v` order on `A`.
  have hord : ∀ z ∈ A, ∀ z' ∈ A,
      (startOf hw z' < startOf hw z ↔ v z' < v z) := by
    intro z hz z' hz'
    rw [Fin.lt_def]
    have hFiff : (startOf hw z').val < (startOf hw z).val ↔
        F (startOf hw z').val < F (startOf hw z).val := by
      constructor
      · exact fun h => hFstrict z hz z' hz' h
      · intro h; by_contra hcon; push_neg at hcon
        exact absurd (hFmono _ _ hcon) (by omega)
    rw [hFiff]
    simp only [hv]
    have h1 := hm_le z hz; have h2 := hm_le z' hz'; omega
  -- Assemble via the abstract rotation lemma.
  obtain ⟨K, hKcard⟩ := rotation_rank_shift A r hrw v hvw
  refine ⟨(K : ZMod A.card), fun z hz => ?_⟩
  have hrankA : startRank hw A z = (A.filter (fun z' => v z' < v z)).card := by
    rw [startRank_eq_card_filter hw hAInt hAanti,
      Finset.filter_congr (fun z' hz' => hord z hz z' hz')]
  have hrankB : startRank hw B (f z)
      = (A.filter (fun z' => (r + v z') % w < (r + v z) % w)).card := by
    rw [startRank_eq_card_filter hw hBInt hBanti]
    have hBimg : B = A.image f := by
      apply Finset.coe_injective; rw [Finset.coe_image]; exact hbij.image_eq.symm
    rw [hBimg, Finset.filter_image,
      Finset.card_image_of_injOn
        (hbij.injOn.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    refine congrArg Finset.card (Finset.filter_congr (fun z' hz' => ?_))
    rw [Fin.lt_def, hbmod z' hz', hbmod z hz]
  rw [hrankA, hrankB]
  exact hKcard z hz

/-- **A degree-one weakly monotone lift preserves the cyclic start successor.**
The lift `F` realizes the *bijection* `f : A → B` as a start rotation
(`isStartRotationBetween_of_degree_one_lift`); a rotation shifts every rank by
one fixed constant, so it commutes with the `+1` rank step, i.e. the cyclic
start successor (`StartSuccBridge`). -/
theorem isCyclicStartSucc_preserved_of_degree_one_lift (hw : 0 < w)
    {A B : Finset (Config w)}
    (hA : ∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hB : ∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hAanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
    (hBanti : ∀ x ∈ B, ∀ y ∈ B, x ≤ y → x = y)
    {f : Config w → Config w}
    (hbij : Set.BijOn f ↑A ↑B)
    (hF : ∃ F : Nat → Nat,
      (∀ x, F (x + w) = F x + w) ∧
      (∀ x y, x ≤ y → F x ≤ F y) ∧
      (∀ x ∈ A, (F (startOf hw x).val) % w = (startOf hw (f x)).val))
    (x y : Config w) (hx : x ∈ A) (hy : y ∈ A)
    (hsucc : IsCyclicStartSucc hw A x y) :
    IsCyclicStartSucc hw B (f x) (f y) := by
  obtain ⟨K, hK⟩ :=
    isStartRotationBetween_of_degree_one_lift hw hA hB hAanti hBanti hbij hF
  have hAInt : ∀ z ∈ A, IsIntervalConfig z := fun z hz => (hA z hz).1
  have hBInt : ∀ z ∈ B, IsIntervalConfig z := fun z hz => (hB z hz).1
  have hcard : A.card = B.card := by
    have himg : A.image f = B :=
      Finset.coe_injective (by rw [Finset.coe_image]; exact hbij.image_eq)
    rw [← himg, Finset.card_image_of_injOn hbij.injOn]
  have hfx : f x ∈ B := hbij.mapsTo hx
  have hfy : f y ∈ B := hbij.mapsTo hy
  have hstepA : (startRank hw A y : ZMod A.card) = (startRank hw A x : ZMod A.card) + 1 :=
    rank_succ_of_isCyclicStartSucc hw hAInt hAanti hx hsucc
  have hstepB : (startRank hw B (f y) : ZMod A.card)
      = (startRank hw B (f x) : ZMod A.card) + 1 := by
    rw [hK y hy, hK x hx, hstepA]; ring
  rw [hcard] at hstepB
  exact isCyclicStartSucc_of_rank_succ hw hBInt hBanti hfx hfy hstepB

end Internal
end AllenderOQ3
