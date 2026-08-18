import AllenderOQ3.Internal.StartRank
import AllenderOQ3.Internal.ComponentLemma
import AllenderOQ3.Internal.IntervalCountBridge
import AllenderOQ3.Internal.AntichainRotationCore

/-!
# The antichain rotation geometry (Part B, B2)

The single geometric payload of the section: a permutation of a top-free
antichain of interval configurations realized by the constant-free submonoid
`NonCrossingCF w` acts as a *rotation* of the cyclic order of starts, i.e. it
shifts every start rank by a constant offset (`IsStartRotation`).

This file splits B2 into:

* **B2-core** `isStartRotationBetween_of_constantFreeLayer` — a *single*
  constant-free layer bijecting one top-free interval antichain onto another
  induces a relative start rotation between them.  This is the genuine
  geometric crux (paper §4 / plan 6c) and the only open obligation of Part B.
* **B2-word** `isStartRotation_of_mem_nonCrossingCF` — proved here, `sorry`-free,
  by induction on the constant-free generators of the word.  The intermediate
  images stay top-free interval antichains of the same cardinality (count is
  squeezed to `1` between the equal endpoints, `⊤` is excluded by endpoint
  fixing, the antichain is reflected by monotonicity), each generator step is a
  bijection, and the per-layer relative rotations compose with a fixed modulus
  `L.card`.

Everything above B2 (`startRotations_commute` in `StartRank.lean`, the
stratification glue in `IntervalRouteCF.lean`) consumes B2 as a black box.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- **B2-core (the section crux): a single constant-free layer rotates the starts.**
A constant-free layer `g` bijecting a top-free antichain of interval
configurations `A` onto another such antichain `B` induces a relative start
rotation `A → B` (a constant additive offset on the start rank in `ZMod A.card`).

Paper §4 / plan 6c: the arcs from an interval form a contiguous block of the
common arc word; the first-true-target map is weakly cyclic-order-preserving of
degree one, sending leading cuts to output starts; distinct starts force a
rotation.  Numerical anchor: zero exceptions over 14,238,180 instances on the
exact `w = 4` monoid. -/
theorem isStartRotationBetween_of_constantFreeLayer (hw : 0 < w) {g : TransMonoid w}
    (hg : isConstantFreeMap w g) {A B : Finset (Config w)}
    (hA : ∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hB : ∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hAanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
    (hBanti : ∀ x ∈ B, ∀ y ∈ B, x ≤ y → x = y)
    (hbij : Set.BijOn (runTrans g) ↑A ↑B) :
    IsStartRotationBetween hw A.card A B (runTrans g) := by
  exact startRotationBetween_of_cyclic_order_preservation hw hg hA hB hAanti hBanti hbij

/-- **B2-word.**  A word of `NonCrossingCF w` bijecting one top-free interval
antichain onto another is a relative start rotation between them.  Proved by
induction on the constant-free generators; the crux `B2-core` handles each
single layer. -/
theorem isStartRotationBetween_of_mem_nonCrossingCF (hw : 0 < w) {m : TransMonoid w}
    (hm : m ∈ NonCrossingCF w) :
    ∀ (A B : Finset (Config w)),
      (∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w) →
      (∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w) →
      (∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y) →
      (∀ x ∈ B, ∀ y ∈ B, x ≤ y → x = y) →
      Set.BijOn (runTrans m) ↑A ↑B →
      IsStartRotationBetween hw A.card A B (runTrans m) := by
  have hm' : m ∈ Submonoid.closure {f | isConstantFreeMap w f} := hm
  clear hm
  induction hm' using Submonoid.closure_induction with
  | mem g hg =>
      intro A B hA hB hAanti hBanti hbij
      exact isStartRotationBetween_of_constantFreeLayer hw hg hA hB hAanti hBanti hbij
  | one =>
      intro A B hA hB hAanti hBanti hbij
      -- `runTrans 1 = id`, so the bijection forces `A = B` and the offset is `0`.
      have hAB : (↑A : Set (Config w)) = ↑B := by
        apply Set.Subset.antisymm
        · intro a ha
          have h := hbij.1 ha
          rwa [runTrans_one] at h
        · intro b hb
          obtain ⟨a, ha, hab⟩ := hbij.2.2 hb
          rw [runTrans_one] at hab
          rwa [← hab]
      have hAB' : A = B := Finset.coe_injective hAB
      subst hAB'
      exact ⟨0, by intro y _; rw [runTrans_one, add_zero]⟩
  | mul x y hx hy IHx IHy =>
      intro A B hA hB hAanti hBanti hbij
      have hxCF : x ∈ NonCrossingCF w := hx
      have hyCF : y ∈ NonCrossingCF w := hy
      -- The intermediate image `C = runTrans x '' A`.
      have hxinj : Set.InjOn (runTrans x) ↑A := by
        intro a ha b hb hab
        apply hbij.2.1 ha hb
        rw [runTrans_mul, runTrans_mul, hab]
      have hCcoe : (↑(A.image (runTrans x)) : Set (Config w)) = runTrans x '' ↑A :=
        Finset.coe_image
      have hbijx : Set.BijOn (runTrans x) ↑A ↑(A.image (runTrans x)) := by
        rw [hCcoe]; exact hxinj.bijOn_image
      have hCcard : (A.image (runTrans x)).card = A.card := Finset.card_image_of_injOn hxinj
      -- `C` is a top-free antichain of interval configs.
      have hCint : ∀ z ∈ A.image (runTrans x), IsIntervalConfig z ∧ z ≠ topConfig w := by
        intro z hz
        rw [Finset.mem_image] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        have haA : a ∈ ↑A := Finset.mem_coe.mpr ha
        have ha1 : intervalCount a = 1 := intervalCount_eq_one_of_isIntervalConfig hw (hA a ha).1
        have hbmem : runTrans (x * y) a ∈ ↑B := hbij.1 haA
        have hb1 : intervalCount (runTrans (x * y) a) = 1 :=
          intervalCount_eq_one_of_isIntervalConfig hw (hB _ (Finset.mem_coe.mp hbmem)).1
        have hle1 : intervalCount (runTrans x a) ≤ intervalCount a :=
          intervalCount_le_of_mem_nonCrossingCF hxCF a
        have hle2 : intervalCount (runTrans (x * y) a) ≤ intervalCount (runTrans x a) := by
          have h := intervalCount_le_of_mem_nonCrossingCF hyCF (runTrans x a)
          rwa [← runTrans_mul] at h
        have hz1 : intervalCount (runTrans x a) = 1 := by omega
        refine ⟨isIntervalConfig_of_intervalCount_eq_one hw hz1, ?_⟩
        intro htop
        have hcontra : runTrans (x * y) a = topConfig w := by
          rw [runTrans_mul, htop, runTrans_topConfig_of_mem_nonCrossingCF hyCF]
        exact (hB _ (Finset.mem_coe.mp hbmem)).2 hcontra
      -- `C` is an antichain (monotonicity of the suffix reflects order into `B`).
      have hmony : Monotone (runTrans y) := monotone_of_mem_nonCrossingCF hyCF
      have hCanti : ∀ u ∈ A.image (runTrans x), ∀ v ∈ A.image (runTrans x),
          u ≤ v → u = v := by
        intro u hu v hv huv
        rw [Finset.mem_image] at hu hv
        obtain ⟨a, ha, rfl⟩ := hu
        obtain ⟨b, hb, rfl⟩ := hv
        have hle : runTrans y (runTrans x a) ≤ runTrans y (runTrans x b) := hmony huv
        have hbmemA : runTrans (x * y) a ∈ ↑B := hbij.1 (Finset.mem_coe.mpr ha)
        have hbmemB : runTrans (x * y) b ∈ ↑B := hbij.1 (Finset.mem_coe.mpr hb)
        have heqB : runTrans (x * y) a = runTrans (x * y) b := by
          apply hBanti _ (Finset.mem_coe.mp hbmemA) _ (Finset.mem_coe.mp hbmemB)
          rw [runTrans_mul, runTrans_mul]; exact hle
        have hab : a = b := hbij.2.1 (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) heqB
        rw [hab]
      -- `runTrans y` bijects `C` onto `B`.
      have hbijy : Set.BijOn (runTrans y) ↑(A.image (runTrans x)) ↑B := by
        refine ⟨?_, ?_, ?_⟩
        · intro u hu
          rw [hCcoe] at hu
          obtain ⟨a, ha, rfl⟩ := hu
          have h := hbij.1 ha
          rwa [runTrans_mul] at h
        · intro u hu v hv huv
          rw [hCcoe] at hu hv
          obtain ⟨a, ha, rfl⟩ := hu
          obtain ⟨b, hb, rfl⟩ := hv
          have hEq : runTrans (x * y) a = runTrans (x * y) b := by
            rw [runTrans_mul, runTrans_mul]; exact huv
          have hab : a = b := hbij.2.1 ha hb hEq
          rw [hab]
        · intro b hb
          obtain ⟨a, ha, hab⟩ := hbij.2.2 hb
          refine ⟨runTrans x a, ?_, ?_⟩
          · rw [hCcoe]; exact ⟨a, ha, rfl⟩
          · rw [← runTrans_mul]; exact hab
      -- Compose the per-layer rotations with the fixed modulus `A.card`.
      have hrotAC : IsStartRotationBetween hw A.card A (A.image (runTrans x)) (runTrans x) :=
        IHx A (A.image (runTrans x)) hA hCint hAanti hCanti hbijx
      have hrotCB : IsStartRotationBetween hw (A.image (runTrans x)).card
          (A.image (runTrans x)) B (runTrans y) :=
        IHy (A.image (runTrans x)) B hCint hB hCanti hBanti hbijy
      rw [hCcard] at hrotCB
      have hcomp := isStartRotationBetween_trans hw hrotAC hrotCB hbijx.1
      have hfun : (fun z => runTrans y (runTrans x z)) = runTrans (x * y) := by
        funext z; rw [runTrans_mul]
      rw [hfun] at hcomp
      exact hcomp

/-- **B2 (leaf-facing form): a constant-free word acts as a start rotation of `L`.** -/
theorem isStartRotation_of_mem_nonCrossingCF (hw : 0 < w) {m : TransMonoid w}
    (hm : m ∈ NonCrossingCF w) {L : Finset (Config w)}
    (hL : ∀ y ∈ L, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y)
    (hbij : Set.BijOn (runTrans m) ↑L ↑L) :
    IsStartRotation hw L (runTrans m) :=
  isStartRotation_of_between_self hw
    (isStartRotationBetween_of_mem_nonCrossingCF hw hm L L hL hL hanti hanti hbij)

end Internal
end AllenderOQ3
