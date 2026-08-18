import AllenderOQ3.Internal.GeoWind
import AllenderOQ3.Internal.StartRotationLive
import AllenderOQ3.Internal.StartSuccBridge
import AllenderOQ3.Internal.ArcWordBlocks
import AllenderOQ3.Internal.LayerExtract
import AllenderOQ3.Internal.DirectCutLift
import Mathlib.Data.Finset.Sort

/-!
# G3: the geometric winding-one theorem (the crux)

A constant-free certified layer bijecting one top-free interval antichain
onto another induces start data that unrolls within a single winding: reading
the source starts once around the source circle, the output starts advance
weakly monotonically and complete exactly one turn.

Route (paper §4): the arcs emitted by the live part of each member form one
contiguous block of the common cyclic arc word
(`exists_arcWord_true_source_block`); blocks of antichain members are read in
the cyclic order of their starts; the common word is grouped target-major up
to one rotation (`commonArcWord`), and a true output start is located by its
member's block, so the output starts inherit the single cyclic winding
(`cyclic_merging_run`, `rotation_middle_eq` are available for segment
bookkeeping).
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

private lemma m1_enumeration (hw : 0 < w) (A : Finset (Config w))
  (hInt : ∀ y ∈ A, IsIntervalConfig y)
  (hanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
  (hNonempty : A.Nonempty) :
  ∃ (k : ℕ) (_ : 0 < k) (e : Fin k → Config w) (S : Fin k → ℕ),
    (∀ (i : Fin k), e i ∈ A) ∧
    (∀ z ∈ A, ∃ i, e i = z) ∧
    (∀ (i j : Fin k), i < j → S i < S j) ∧
    (∀ (i j : Fin k), S j < S i + w) ∧
    (∀ (i : Fin k), S i < w) ∧
    (∀ (i : Fin k), S i % w = ↑(startOf hw (e i))) := by
  let k := A.card
  have hk_pos : 0 < k := Finset.card_pos.mpr hNonempty
  let f := startOf hw
  have h_inj : Set.InjOn f A := startOf_injOn hw hInt hanti
  let s := A.image f
  have h_card : s.card = k := Finset.card_image_of_injOn h_inj
  let iso := Finset.orderIsoOfFin s h_card
  let e (i : Fin k) : Config w :=
    Classical.choose (Finset.mem_image.mp (iso i).2)
  have he (i : Fin k) : e i ∈ A ∧ f (e i) = ↑(iso i) :=
    Classical.choose_spec (Finset.mem_image.mp (iso i).2)
  let S (i : Fin k) : ℕ := ↑(iso i : Fin w)
  use k, hk_pos, e, S
  refine ⟨fun i => (he i).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hz_img : f z ∈ s := Finset.mem_image_of_mem f hz
    have ex_i : ∃ i, ↑(iso i) = f z := ⟨iso.symm ⟨f z, hz_img⟩, by simp⟩
    rcases ex_i with ⟨i, hi⟩
    use i
    have heq : f (e i) = f z := by rw [(he i).2, hi]
    exact h_inj (he i).1 hz heq
  · intro i j hij
    have h_lt : (iso i : Fin w) < (iso j : Fin w) := iso.strictMono hij
    exact h_lt
  · intro i j
    have hj_lt : S j < w := (iso j : Fin w).isLt
    have hi_ge : 0 ≤ S i := Nat.zero_le _
    omega
  · intro i
    exact (iso i : Fin w).isLt
  · intro i
    have h_mod : S i % w = S i := Nat.mod_eq_of_lt (iso i : Fin w).isLt
    rw [h_mod]
    have h_fe : f (e i) = ↑(iso i) := (he i).2
    have h_fe_val : (f (e i) : ℕ) = ↑(iso i : Fin w) := congrArg Fin.val h_fe
    rw [h_fe_val]

/-- **G3 (open, the geometric crux).** -/
theorem startWindingData_of_constantFreeMap (hw : 0 < w) {g : TransMonoid w}
    (hg : isConstantFreeMap w g) {A B : Finset (Config w)}
    (hA : ∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hB : ∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hAanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
    (hBanti : ∀ x ∈ B, ∀ y ∈ B, x ≤ y → x = y)
    (hbij : Set.BijOn (runTrans g) ↑A ↑B) :
    StartWindingData hw A (runTrans g) := by
  intro hA_nonempty
  have hA_Int : ∀ y ∈ A, IsIntervalConfig y := fun y hy => (hA y hy).1
  have hB_Int : ∀ y ∈ B, IsIntervalConfig y := fun y hy => (hB y hy).1
  rcases m1_enumeration hw A hA_Int hAanti hA_nonempty with
    ⟨k, hk, e, S, he_mem, he_surj, hS_mono, hS_bound, hS_lt, hS_mod⟩
  obtain ⟨F, hFper, hFmono, hFtrack⟩ :=
    exists_degree_one_lift_of_constantFreeMap_cut hw hg hA hB hbij
  have hS_eq : ∀ i, S i = (startOf hw (e i)).val := by
    intro i
    calc
      S i = S i % w := (Nat.mod_eq_of_lt (hS_lt i)).symm
      _ = (startOf hw (e i)).val := hS_mod i
  let T : Fin k → Nat := fun i => F (S i)
  have hTmod : ∀ i, T i % w = (startOf hw (runTrans g (e i))).val := by
    intro i
    dsimp [T]
    rw [hS_eq i]
    exact hFtrack (e i) (he_mem i)
  have hTmono : ∀ i j, i ≤ j → T i ≤ T j := by
    intro i j hij
    apply hFmono
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact (hS_mono i j hij).le
  have hstartinjB : Set.InjOn (startOf hw) ↑B :=
    startOf_injOn hw hB_Int hBanti
  have hTbound : ∀ i j, T j < T i + w := by
    intro i j
    have hle : T j ≤ T i + w := by
      dsimp [T]
      calc
        F (S j) ≤ F (S i + w) := hFmono (hS_bound i j).le
        _ = F (S i) + w := hFper (S i)
    by_contra hnlt
    have heq : T j = T i + w := by omega
    have hmod : T j % w = T i % w := by
      rw [heq, Nat.add_mod_right]
    have hstarts : startOf hw (runTrans g (e j)) =
        startOf hw (runTrans g (e i)) := by
      apply Fin.ext
      rw [← hTmod j, ← hTmod i]
      exact hmod
    have houtEq : runTrans g (e j) = runTrans g (e i) :=
      hstartinjB (hbij.mapsTo (he_mem j)) (hbij.mapsTo (he_mem i)) hstarts
    have hinEq : e j = e i :=
      hbij.injOn (he_mem j) (he_mem i) houtEq
    have hSeq : S j = S i := by
      rw [hS_eq j, hS_eq i, hinEq]
    dsimp [T] at heq
    rw [hSeq] at heq
    omega
  refine ⟨k, hk, e, S, T, he_mem, he_surj, hS_mono, hS_bound,
    hTmono, hTbound, hS_mod, ?_⟩
  exact hTmod

end Internal
end AllenderOQ3
