import AllenderOQ3.Internal.OrbitCount

/-!
# Transporting counts of minimal representatives

`permCycleCount`, `componentCount` and friends are all defined as the number of
`rank`-minimal representatives of an equivalence relation.  This file provides a
general transport lemma: a bijection that matches two such relations matches the
counts of minimal representatives.
-/

set_option autoImplicit false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace AllenderOQ3.Internal

open Classical in
/-- The number of `rank`-minimal representatives of an equivalence relation is
invariant under a relation-preserving bijection. -/
theorem minRepSet_card_congr {α β : Type} [Fintype α] [Fintype β]
    {r : α → α → Prop} {s : β → β → Prop} (hr : Equivalence r) (hs : Equivalence s)
    (ra : α → Nat) (rb : β → Nat) (hra : Function.Injective ra)
    (hrb : Function.Injective rb) (e : α ≃ β)
    (he : ∀ x y, r x y ↔ s (e x) (e y)) :
    (Finset.univ.filter (fun x => ∀ y, r x y → ra x ≤ ra y)).card
      = (Finset.univ.filter (fun x => ∀ y, s x y → rb x ≤ rb y)).card := by
  classical
  refine Finset.card_bij
    (fun x _ => Classical.choose (exists_minRep hs rb (e x))) ?_ ?_ ?_
  · intro x _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Classical.choose_spec (exists_minRep hs rb (e x))).2⟩
  · intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have hsx := (Classical.choose_spec (exists_minRep hs rb (e x))).1
    have hsy := (Classical.choose_spec (exists_minRep hs rb (e y))).1
    have hxy' : Classical.choose (exists_minRep hs rb (e x))
        = Classical.choose (exists_minRep hs rb (e y)) := hxy
    rw [hxy'] at hsx
    have : s (e x) (e y) := hs.trans hsx (hs.symm hsy)
    exact minRep_unique hr ra hra ((he x y).mpr this) hx' hy'
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    refine ⟨Classical.choose (exists_minRep hr ra (e.symm y)), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Classical.choose_spec (exists_minRep hr ra (e.symm y))).2⟩
    · set x := Classical.choose (exists_minRep hr ra (e.symm y)) with hxdef
      have hrx : r (e.symm y) x := (Classical.choose_spec (exists_minRep hr ra (e.symm y))).1
      have hsx : s y (e x) := by
        have := (he (e.symm y) x).mp hrx
        rwa [Equiv.apply_symm_apply] at this
      have hmin := Classical.choose_spec (exists_minRep hs rb (e x))
      exact (minRep_unique hs rb hrb (hs.trans hsx hmin.1) hy' hmin.2).symm

/-- Variant of `minRepSet_card_congr` for an injection whose image is a union of
`s`-classes: the minimal representatives of `r` correspond to the minimal
representatives of `s` lying in the image. -/
theorem minRepSet_card_congr_inj {α β : Type} [Fintype α] [Fintype β]
    {r : α → α → Prop} {s : β → β → Prop} (hr : Equivalence r) (hs : Equivalence s)
    (ra : α → Nat) (rb : β → Nat) (hra : Function.Injective ra)
    (hrb : Function.Injective rb) (g : α → β)
    (hcompat : ∀ x y, r x y ↔ s (g x) (g y))
    (hclosed : ∀ (x : α) (v : β), s (g x) v → ∃ y, g y = v)
    [DecidablePred (fun x => ∀ y, r x y → ra x ≤ ra y)]
    [DecidablePred (fun u => (∃ x, g x = u) ∧ ∀ v, s u v → rb u ≤ rb v)] :
    (Finset.univ.filter (fun x => ∀ y, r x y → ra x ≤ ra y)).card
      = (Finset.univ.filter (fun u => (∃ x, g x = u) ∧ ∀ v, s u v → rb u ≤ rb v)).card := by
  classical
  refine Finset.card_bij
    (fun x _ => Classical.choose (exists_minRep hs rb (g x))) ?_ ?_ ?_
  · intro x _
    have hspec := Classical.choose_spec (exists_minRep hs rb (g x))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclosed x _ hspec.1, hspec.2⟩
  · intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have hsx := (Classical.choose_spec (exists_minRep hs rb (g x))).1
    have hsy := (Classical.choose_spec (exists_minRep hs rb (g y))).1
    have hxy' : Classical.choose (exists_minRep hs rb (g x))
        = Classical.choose (exists_minRep hs rb (g y)) := hxy
    rw [hxy'] at hsx
    exact minRep_unique hr ra hra ((hcompat x y).mpr (hs.trans hsx (hs.symm hsy))) hx' hy'
  · intro u hu
    obtain ⟨⟨x0, hx0⟩, hu'⟩ := (Finset.mem_filter.mp hu).2
    refine ⟨Classical.choose (exists_minRep hr ra x0), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Classical.choose_spec (exists_minRep hr ra x0)).2⟩
    · set x := Classical.choose (exists_minRep hr ra x0) with hxdef
      have hrx : r x0 x := (Classical.choose_spec (exists_minRep hr ra x0)).1
      have hsu : s u (g x) := by
        have := (hcompat x0 x).mp hrx
        rwa [hx0] at this
      have hmin := Classical.choose_spec (exists_minRep hs rb (g x))
      exact (minRep_unique hs rb hrb (hs.trans hsu hmin.1) hu' hmin.2).symm

/-- Forward-reachability under a permutation is an equivalence relation. -/
theorem permForwardReach_equiv {α : Type} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) : Equivalence (fun x y : α => ∃ k : Nat, (p ^ k) x = y) := by
  constructor
  · intro x; exact ⟨0, rfl⟩
  · intro x y hxy; exact perm_forwardReach_symm p hxy
  · rintro x y z ⟨k1, hk1⟩ ⟨k2, hk2⟩
    exact ⟨k2 + k1, by rw [pow_add, Equiv.Perm.mul_apply, hk1, hk2]⟩

/-- Conjugating a permutation by an equivalence commutes with taking powers. -/
theorem perm_conj_pow {α β : Type} (e : α ≃ β) (p : Equiv.Perm α) (k : Nat) (b : β) :
    ((e.symm.trans (p.trans e)) ^ k) b = e ((p ^ k) (e.symm b)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply, ih, Equiv.trans_apply,
      Equiv.symm_apply_apply]

/-- Cycle counts are invariant under conjugation. -/
theorem permCycleCount_conj {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (p : Equiv.Perm α) :
    permCycleCount (e.symm.trans (p.trans e)) = permCycleCount p := by
  classical
  unfold permCycleCount
  have hkey := minRepSet_card_congr
    (r := fun x y : β => ∃ k : Nat, ((e.symm.trans (p.trans e)) ^ k) x = y)
    (s := fun x y : α => ∃ k : Nat, (p ^ k) x = y)
    (permForwardReach_equiv (e.symm.trans (p.trans e))) (permForwardReach_equiv p)
    (fun x => (Fintype.equivFin β x).val) (fun x => (Fintype.equivFin α x).val)
    (fun x y h => (Fintype.equivFin β).injective (Fin.ext h))
    (fun x y h => (Fintype.equivFin α).injective (Fin.ext h))
    e.symm ?_
  · convert hkey using 2
  · intro x y
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [perm_conj_pow] at hk
      have := congrArg e.symm hk
      rwa [Equiv.symm_apply_apply] at this
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [perm_conj_pow]
      rw [hk]
      simp

end AllenderOQ3.Internal
