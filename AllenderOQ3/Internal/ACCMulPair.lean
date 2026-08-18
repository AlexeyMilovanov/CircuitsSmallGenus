import AllenderOQ3.Internal.ACCJoin
import AllenderOQ3.Internal.ACCLocal

/-!
# Recognising a product of two monoid-valued quantities

A reusable assembly gadget for the word problem: if the two factors `val₁ x` and
`val₂ x` of a product in a *finite* monoid `M` are recognised, value by value,
by `ACC[m]` circuits of depth `d` and size `s`, then the predicate
`val₁ x * val₂ x = h` is recognised in depth `max d 1 + 2` and size
`|M| ^ 2 * (2 * s + 2) + 1`.

The construction is guess-and-verify: a depth-two `OR`-of-`AND`s over the
`|M| ^ 2` pairs `(g₁, g₂)`, each branch checking `val₁ x = g₁`, `val₂ x = g₂`
and the constant `g₁ * g₂ = h`.

Applied with `val₁` and `val₂` the products of two consecutive windows of a
word (see `wordEnd_range'_split`), this is the step that lets a word be cut into
blocks: the value of the whole is recognised as soon as the values of the parts
are.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- **Guess-and-verify for a product of two factors.** -/
theorem exists_acc_mul_pair {n m : Nat} {M : Type} [Monoid M] [Fintype M]
    {d s : Nat} (val₁ val₂ : (Fin n → Bool) → M)
    (A : M → ACCCircuit n m) (hAwf : ∀ g, WellFormedACC (A g))
    (hAlay : ∀ g q, (A g).layer q ≤ d) (hAsz : ∀ g, (A g).gateCount ≤ s)
    (hAacc : ∀ g x, ACCAccepts (A g) x ↔ val₁ x = g)
    (B : M → ACCCircuit n m) (hBwf : ∀ g, WellFormedACC (B g))
    (hBlay : ∀ g q, (B g).layer q ≤ d) (hBsz : ∀ g, (B g).gateCount ≤ s)
    (hBacc : ∀ g x, ACCAccepts (B g) x ↔ val₂ x = g)
    (h : M) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max d 1 + 2) ∧
      a.gateCount ≤ Fintype.card M * Fintype.card M * (2 * s + 2) + 1 ∧
      (∀ x, ACCAccepts a x ↔ val₁ x * val₂ x = h) := by
  classical
  set K := Fintype.card (M × M) with hK
  set ee := Fintype.equivFin (M × M) with hee
  set blocks : (i : Fin K) → Fin 3 → ACCCircuit n m := fun i j =>
    if (j : Nat) = 0 then A (ee.symm i).1
    else if (j : Nat) = 1 then B (ee.symm i).2
    else accConst n m (decide ((ee.symm i).1 * (ee.symm i).2 = h)) with hblocks
  have hb0 : ∀ i, blocks i 0 = A (ee.symm i).1 := by intro i; rw [hblocks]; simp
  have hb1 : ∀ i, blocks i 1 = B (ee.symm i).2 := by intro i; rw [hblocks]; simp
  have hb2 : ∀ i, blocks i 2
      = accConst n m (decide ((ee.symm i).1 * (ee.symm i).2 = h)) := by
    intro i; rw [hblocks]; simp
  have hjcases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by
    intro j
    rcases (show (j : Nat) = 0 ∨ (j : Nat) = 1 ∨ (j : Nat) = 2 from by omega) with hj | hj | hj
    · exact Or.inl (Fin.ext (by simp [hj]))
    · exact Or.inr (Or.inl (Fin.ext (by simp [hj])))
    · exact Or.inr (Or.inr (Fin.ext (by simp [hj])))
  have hbwf : ∀ i j, WellFormedACC (blocks i j) := by
    intro i j
    rcases hjcases j with hj | hj | hj <;> subst hj
    · rw [hb0 i]; exact hAwf _
    · rw [hb1 i]; exact hBwf _
    · rw [hb2 i]; exact wellFormedACC_accConst n m _
  have hblay : ∀ i j (q : Fin (blocks i j).gateCount),
      (blocks i j).layer q ≤ max d 1 := by
    intro i j
    rcases hjcases j with hj | hj | hj <;> subst hj
    · rw [hb0 i]; exact fun q => le_trans (hAlay _ q) (le_max_left _ _)
    · rw [hb1 i]; exact fun q => le_trans (hBlay _ q) (le_max_left _ _)
    · rw [hb2 i]; intro q; rw [accConst_layer]; exact le_max_right _ _
  refine ⟨accOrAnd blocks (max d 1), wellFormedACC_accOrAnd hbwf hblay,
    accOrAnd_layer_le hblay, ?_, fun x => ?_⟩
  · -- size bound
    have hcard : K = Fintype.card M * Fintype.card M := by
      rw [hK, Fintype.card_prod]
    have hrow : ∀ i : Fin K, (∑ j, (blocks i j).gateCount) + 1 ≤ 2 * s + 2 := by
      intro i
      have h0 : (blocks i 0).gateCount ≤ s := by rw [hb0 i]; exact hAsz _
      have h1 : (blocks i 1).gateCount ≤ s := by rw [hb1 i]; exact hBsz _
      have h2 : (blocks i 2).gateCount = 1 := by rw [hb2 i]; exact accConst_gateCount n m _
      have hsum : ∑ j, (blocks i j).gateCount
          = (blocks i 0).gateCount + (blocks i 1).gateCount + (blocks i 2).gateCount := by
        simp [Fin.sum_univ_three]
      omega
    have hsum : ∑ i : Fin K, ((∑ j, (blocks i j).gateCount) + 1)
        ≤ ∑ _i : Fin K, (2 * s + 2) := Finset.sum_le_sum fun i _ => hrow i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hgc : (accOrAnd blocks (max d 1)).gateCount
        = (∑ i : Fin K, ((∑ j, (blocks i j).gateCount) + 1)) + 1 := rfl
    rw [hgc, ← hcard]
    omega
  · -- semantics
    rw [accAccepts_accOrAnd hbwf hblay x]
    constructor
    · rintro ⟨i, hi⟩
      have h0 := (hAacc _ x).mp (by rw [← hb0 i]; exact hi 0)
      have h1 := (hBacc _ x).mp (by rw [← hb1 i]; exact hi 1)
      have h2 := (accAccepts_accConst n m _ x).mp (by rw [← hb2 i]; exact hi 2)
      rw [h0, h1]
      exact of_decide_eq_true h2
    · intro hg
      refine ⟨ee (val₁ x, val₂ x), fun j => ?_⟩
      have hsymm : ee.symm (ee (val₁ x, val₂ x)) = (val₁ x, val₂ x) := ee.symm_apply_apply _
      rcases hjcases j with hj | hj | hj <;> subst hj
      · rw [hb0 _, hsymm]
        exact (hAacc _ x).mpr rfl
      · rw [hb1 _, hsymm]
        exact (hBacc _ x).mpr rfl
      · rw [hb2 _]
        refine (accAccepts_accConst n m _ x).mpr ?_
        rw [hsymm]
        exact decide_eq_true hg

end AllenderOQ3.Internal
