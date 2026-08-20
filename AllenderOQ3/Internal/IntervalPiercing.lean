import AllenderOQ3.Base

/-!
# Greedy piercing of a finite family of integer intervals

A pair `p : Nat × Nat` with `p.1 ≤ p.2` denotes the closed interval
`[p.1, p.2]`.  The classical greedy argument (repeatedly take the least right
endpoint) produces a set of pairwise disjoint intervals of the family together
with an equinumerous set of points hitting *every* interval of the family.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- The intervals coded by `J` are pairwise disjoint. -/
def PairwiseDisjointIntervals (J : Finset (Nat × Nat)) : Prop :=
  ∀ p ∈ J, ∀ q ∈ J, p ≠ q → p.2 < q.1 ∨ q.2 < p.1

/-- Greedy selection: a pairwise disjoint subfamily whose right endpoints
already pierce the whole family. -/
theorem greedy_disjoint_subfamily :
    ∀ (k : Nat) (I : Finset (Nat × Nat)), I.card ≤ k → (∀ p ∈ I, p.1 ≤ p.2) →
      ∃ J : Finset (Nat × Nat), J ⊆ I ∧ PairwiseDisjointIntervals J ∧
        ∀ p ∈ I, ∃ q ∈ J, p.1 ≤ q.2 ∧ q.2 ≤ p.2 := by
  intro k
  induction k with
  | zero =>
      intro I hcard _
      have hI0 : I = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hI0
      exact ⟨∅, Finset.Subset.refl _, by simp [PairwiseDisjointIntervals], by simp⟩
  | succ k ih =>
      intro I hcard hI
      rcases I.eq_empty_or_nonempty with rfl | hne
      · exact ⟨∅, Finset.Subset.refl _, by simp [PairwiseDisjointIntervals], by simp⟩
      obtain ⟨p₀, hp₀I, hmin⟩ := I.exists_min_image Prod.snd hne
      have hp₀le : p₀.1 ≤ p₀.2 := hI p₀ hp₀I
      set I' := I.filter (fun q => p₀.2 < q.1) with hI'def
      have hsub : I' ⊆ I := Finset.filter_subset _ _
      have hp₀notin : p₀ ∉ I' := by
        simp only [hI'def, Finset.mem_filter, not_and]
        intro _
        omega
      have hcard' : I'.card ≤ k := by
        have hlt : I'.card < I.card :=
          Finset.card_lt_card ⟨hsub, fun h => hp₀notin (h hp₀I)⟩
        omega
      obtain ⟨J', hJ'sub, hJ'disj, hJ'pierce⟩ :=
        ih I' hcard' (fun p hp => hI p (hsub hp))
      have hmemI' : ∀ q ∈ J', p₀.2 < q.1 := by
        intro q hq
        have := hJ'sub hq
        simp only [hI'def, Finset.mem_filter] at this
        exact this.2
      refine ⟨insert p₀ J', ?_, ?_, ?_⟩
      · exact Finset.insert_subset hp₀I (hJ'sub.trans hsub)
      · intro p hp q hq hpq
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · rcases Finset.mem_insert.mp hq with rfl | hq'
          · exact absurd rfl hpq
          · exact Or.inl (hmemI' q hq')
        · rcases Finset.mem_insert.mp hq with rfl | hq'
          · exact Or.inr (hmemI' p hp')
          · exact hJ'disj p hp' q hq' hpq
      · intro p hp
        by_cases hcase : p₀.2 < p.1
        · have hpI' : p ∈ I' := by
            simp only [hI'def, Finset.mem_filter]
            exact ⟨hp, hcase⟩
          obtain ⟨q, hqJ, hq1, hq2⟩ := hJ'pierce p hpI'
          exact ⟨q, Finset.mem_insert_of_mem hqJ, hq1, hq2⟩
        · refine ⟨p₀, Finset.mem_insert_self _ _, by omega, hmin p hp⟩

/-- Greedy interval piercing: a finite family of nonempty integer intervals has
a pairwise disjoint subfamily `J` and a piercing set `P` of the same size. -/
theorem greedy_pierce (I : Finset (Nat × Nat)) (hI : ∀ p ∈ I, p.1 ≤ p.2) :
    ∃ (P : Finset Nat) (J : Finset (Nat × Nat)),
      J ⊆ I ∧ (∀ p ∈ J, ∀ q ∈ J, p ≠ q → p.2 < q.1 ∨ q.2 < p.1) ∧
      P.card = J.card ∧ (∀ p ∈ I, ∃ x ∈ P, p.1 ≤ x ∧ x ≤ p.2) := by
  obtain ⟨J, hJsub, hJdisj, hJpierce⟩ :=
    greedy_disjoint_subfamily I.card I (Nat.le_refl _) hI
  refine ⟨J.image Prod.snd, J, hJsub, hJdisj, ?_, ?_⟩
  · refine Finset.card_image_of_injOn ?_
    intro p hp q hq hpq
    by_contra hne
    have hle : q.1 ≤ q.2 := hI q (hJsub hq)
    have hle' : p.1 ≤ p.2 := hI p (hJsub hp)
    rcases hJdisj p hp q hq hne with h | h <;> omega
  · intro p hp
    obtain ⟨q, hqJ, hq1, hq2⟩ := hJpierce p hp
    exact ⟨q.2, Finset.mem_image_of_mem _ hqJ, hq1, hq2⟩

end AllenderOQ3.Internal
