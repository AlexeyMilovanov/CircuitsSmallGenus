import AllenderOQ3.Internal.ACCJoin
import AllenderOQ3.Internal.ACCLocal

/-!
# Three reusable depth-two assembly gadgets

All three are thin wrappers around `accOrAnd`:

* `exists_acc_bigAnd` — the conjunction of a finite family of circuits;
* `exists_acc_orPair` — the disjunction of a finite family of *pairs* of
  circuits, each pair being conjoined;
* `exists_acc_letterPred` — from exact recognisers for the value `p x` of a
  letter in a finite type, a circuit deciding an arbitrary predicate of that
  value (the generalisation of `exists_acc_letterStep`, whose predicate is
  `fun g => gin * g = gout`).

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

variable {n m : Nat}

/-- **Conjunction of a finite family.** -/
theorem exists_acc_bigAnd {K d Sz : Nat} (f : Fin K → ACCCircuit n m)
    (hwf : ∀ i, WellFormedACC (f i)) (hlay : ∀ i q, (f i).layer q ≤ d)
    (hsz : ∀ i, (f i).gateCount ≤ Sz) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ d + 2) ∧
      a.gateCount ≤ K * Sz + 2 ∧
      (∀ x, ACCAccepts a x ↔ ∀ i, ACCAccepts (f i) x) := by
  classical
  set blocks : (i : Fin 1) → Fin K → ACCCircuit n m := fun _ i => f i with hblocks
  have hbwf : ∀ i j, WellFormedACC (blocks i j) := fun _ j => hwf j
  have hblay : ∀ i j (q : Fin (blocks i j).gateCount), (blocks i j).layer q ≤ d :=
    fun _ j q => hlay j q
  refine ⟨accOrAnd blocks d, wellFormedACC_accOrAnd hbwf hblay,
    accOrAnd_layer_le hblay, ?_, ?_⟩
  · simp only [accOrAnd_gateCount, hblocks]
    have hsum : (∑ i : Fin K, (f i).gateCount) ≤ K * Sz := by
      refine le_trans (Finset.sum_le_card_nsmul Finset.univ _ Sz (fun i _ => hsz i)) ?_
      simp
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    omega
  · intro x
    rw [accAccepts_accOrAnd hbwf hblay x]
    constructor
    · rintro ⟨_, hi⟩; exact hi
    · intro h; exact ⟨0, h⟩

/-- **Disjunction of a finite family of conjoined pairs.** -/
theorem exists_acc_orPair {K d S1 S2 : Nat} (f g : Fin K → ACCCircuit n m)
    (hwff : ∀ i, WellFormedACC (f i)) (hwfg : ∀ i, WellFormedACC (g i))
    (hlayf : ∀ i q, (f i).layer q ≤ d) (hlayg : ∀ i q, (g i).layer q ≤ d)
    (hszf : ∀ i, (f i).gateCount ≤ S1) (hszg : ∀ i, (g i).gateCount ≤ S2) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ d + 2) ∧
      a.gateCount ≤ K * (S1 + S2 + 1) + 1 ∧
      (∀ x, ACCAccepts a x ↔ ∃ i, ACCAccepts (f i) x ∧ ACCAccepts (g i) x) := by
  classical
  set blocks : (i : Fin K) → Fin 2 → ACCCircuit n m := fun i j =>
    if (j : Nat) = 0 then f i else g i with hblocks
  have hb0 : ∀ i, blocks i 0 = f i := by intro i; simp [hblocks]
  have hb1 : ∀ i, blocks i 1 = g i := by intro i; simp [hblocks]
  have hjcases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by
    intro j
    rcases (show (j : Nat) = 0 ∨ (j : Nat) = 1 from by omega) with hj | hj
    · exact Or.inl (Fin.ext (by simp [hj]))
    · exact Or.inr (Fin.ext (by simp [hj]))
  have hbwf : ∀ i j, WellFormedACC (blocks i j) := by
    intro i j
    rcases hjcases j with rfl | rfl
    · rw [hb0]; exact hwff i
    · rw [hb1]; exact hwfg i
  have hblay : ∀ i j (q : Fin (blocks i j).gateCount), (blocks i j).layer q ≤ d := by
    intro i j
    rcases hjcases j with rfl | rfl
    · rw [hb0]; exact hlayf i
    · rw [hb1]; exact hlayg i
  refine ⟨accOrAnd blocks d, wellFormedACC_accOrAnd hbwf hblay,
    accOrAnd_layer_le hblay, ?_, ?_⟩
  · simp only [accOrAnd_gateCount, Fin.sum_univ_two]
    have hinner : ∀ i : Fin K,
        (blocks i 0).gateCount + (blocks i 1).gateCount + 1 ≤ S1 + S2 + 1 := by
      intro i
      rw [hb0, hb1]
      have := hszf i
      have := hszg i
      omega
    have hsum : (∑ i : Fin K, ((blocks i 0).gateCount + (blocks i 1).gateCount + 1))
        ≤ K * (S1 + S2 + 1) := by
      refine le_trans (Finset.sum_le_card_nsmul Finset.univ _ _ (fun i _ => hinner i)) ?_
      simp
    omega
  · intro x
    rw [accAccepts_accOrAnd hbwf hblay x]
    constructor
    · rintro ⟨i, hi⟩
      have h0 := hi 0
      have h1 := hi 1
      rw [hb0] at h0
      rw [hb1] at h1
      exact ⟨i, h0, h1⟩
    · rintro ⟨i, h0, h1⟩
      refine ⟨i, fun j => ?_⟩
      rcases hjcases j with rfl | rfl
      · rw [hb0]; exact h0
      · rw [hb1]; exact h1

/-- **An arbitrary predicate of the value of a letter.**  From exact recognisers
`L g` for the value `p x` of a letter in a finite type one builds a circuit
accepting exactly the inputs whose letter value satisfies `P`. -/
theorem exists_acc_letterPred {G : Type} [Fintype G] {d Sz : Nat}
    (L : G → ACCCircuit n m) (p : (Fin n → Bool) → G) (P : G → Prop)
    (hwf : ∀ g, WellFormedACC (L g))
    (hlay : ∀ g q, (L g).layer q ≤ d)
    (hsz : ∀ g, (L g).gateCount ≤ Sz)
    (hacc : ∀ g x, ACCAccepts (L g) x ↔ p x = g) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max d 1 + 2) ∧
      a.gateCount ≤ Fintype.card G * (Sz + 2) + 1 ∧
      (∀ x, ACCAccepts a x ↔ P (p x)) := by
  classical
  set ee := Fintype.equivFin G with hee
  set outer : Fin (Fintype.card G) → Fin 1 → ACCCircuit n m := fun i _ =>
    if P (ee.symm i) then L (ee.symm i) else accConst n m false with houter
  have hout_pos : ∀ (i : Fin (Fintype.card G)) (j : Fin 1), P (ee.symm i) →
      outer i j = L (ee.symm i) := by
    intro i j hc
    simp only [houter, if_pos hc]
  have hout_neg : ∀ (i : Fin (Fintype.card G)) (j : Fin 1), ¬ P (ee.symm i) →
      outer i j = accConst n m false := by
    intro i j hc
    simp only [houter, if_neg hc]
  have hwf_out : ∀ i j, WellFormedACC (outer i j) := by
    intro i j
    by_cases hc : P (ee.symm i)
    · rw [hout_pos i j hc]; exact hwf _
    · rw [hout_neg i j hc]; exact wellFormedACC_accConst n m _
  have hlay_out : ∀ i j (q : Fin (outer i j).gateCount), (outer i j).layer q ≤ max d 1 := by
    intro i j
    by_cases hc : P (ee.symm i)
    · rw [hout_pos i j hc]
      exact fun q => le_trans (hlay _ q) (le_max_left _ _)
    · rw [hout_neg i j hc]
      intro q; rw [accConst_layer]; exact le_max_right _ _
  have hsz_out : ∀ i j, (outer i j).gateCount ≤ Sz + 1 := by
    intro i j
    by_cases hc : P (ee.symm i)
    · rw [hout_pos i j hc]; exact le_trans (hsz _) (by omega)
    · rw [hout_neg i j hc, accConst_gateCount]; omega
  refine ⟨accOrAnd outer (max d 1), wellFormedACC_accOrAnd hwf_out hlay_out,
    accOrAnd_layer_le hlay_out, ?_, ?_⟩
  · simp only [accOrAnd_gateCount]
    have hinner : ∀ i : Fin (Fintype.card G),
        (∑ j : Fin 1, (outer i j).gateCount) + 1 ≤ Sz + 2 := by
      intro i
      have hs : (∑ j : Fin 1, (outer i j).gateCount) ≤ Sz + 1 := by
        refine le_trans
          (Finset.sum_le_card_nsmul Finset.univ _ (Sz + 1) (fun j _ => hsz_out i j)) ?_
        simp
      omega
    have hsum : (∑ i : Fin (Fintype.card G), ((∑ j : Fin 1, (outer i j).gateCount) + 1))
        ≤ Fintype.card G * (Sz + 2) := by
      refine le_trans (Finset.sum_le_card_nsmul Finset.univ _ _ (fun i _ => hinner i)) ?_
      simp
    omega
  · intro x
    rw [accAccepts_accOrAnd hwf_out hlay_out x]
    constructor
    · rintro ⟨i, hi⟩
      have hacc0 := hi 0
      by_cases hc : P (ee.symm i)
      · rw [hout_pos i 0 hc] at hacc0
        rw [(hacc _ x).mp hacc0]
        exact hc
      · rw [hout_neg i 0 hc] at hacc0
        exact absurd ((accAccepts_accConst n m false x).mp hacc0) (by simp)
    · intro hx
      have hsymm : ee.symm (ee (p x)) = p x := ee.symm_apply_apply _
      have hc : P (ee.symm (ee (p x))) := by rw [hsymm]; exact hx
      refine ⟨ee (p x), fun j => ?_⟩
      rw [hout_pos _ j hc, hsymm]
      exact (hacc (p x) x).mpr rfl

end Internal
end AllenderOQ3
