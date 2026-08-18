import AllenderOQ3.Internal.ACCSumMod

/-!
# The word problem of a cyclic group is in `ACC0`

The base case of the Barrington--Thérien upper bound: if every letter of a word
is a power `g₀ ^ k i` of one fixed element of exponent `N`, and the exponents
are recognised position by position by small `ACC[m]` circuits with `N ∣ m`,
then the value of the product is recognised by an `ACC[m]` circuit of constant
depth and of size a constant multiple of the size of the exponent recognisers
times the length.

The product is `g₀ ^ (∑ k i)`, so this is `exists_acc_sumMod` followed by a
finite `OR` over the residues `v < N` with `g₀ ^ v` equal to the target.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- **The word problem of a cyclic group is in `ACC0`.** -/
theorem exists_acc_powWord {n m N : Nat} (hm : 0 < m) (hNm : N ∣ m)
    {G : Type} [Monoid G] (g0 : G) (hg0 : g0 ^ N = 1)
    {len size d : Nat}
    (k : Fin len → (Fin n → Bool) → Nat)
    (hk : ∀ i x, k i x < N)
    (rec : Fin len → Fin N → ACCCircuit n m)
    (hwf : ∀ i v, WellFormedACC (rec i v))
    (hlay : ∀ i v q, (rec i v).layer q ≤ d)
    (hsize : ∀ i v, (rec i v).gateCount ≤ size)
    (hacc : ∀ i v x, ACCAccepts (rec i v) x ↔ k i x = (v : Nat))
    (h : G) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max d 1 + 5) ∧
      a.gateCount ≤ N * (m ^ N * ((N + 1) * (len * size + m + 1) + 1) + 1 + 3) + 1 ∧
      (∀ x, ACCAccepts a x ↔ (List.ofFn fun i => g0 ^ k i x).prod = h) := by
  classical
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNm hm
  set S := m ^ N * ((N + 1) * (len * size + m + 1) + 1) + 1 with hS
  -- the powers of `g₀` only depend on the exponent modulo `N`
  have hpow : ∀ a : Nat, g0 ^ a = g0 ^ (a % N) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a N]
    rw [pow_add, pow_mul, hg0, one_pow, one_mul]
  choose A hAwf hAlay hAsize hAacc using fun v : Fin N =>
    exists_acc_sumMod hm hNm (val := fun i x => k i x) (fun i x => hk i x)
      rec hwf hlay hsize hacc ((v : Nat))
  set blocks : (v : Fin N) → Fin 2 → ACCCircuit n m := fun v j =>
    if (j : Nat) = 0 then A v else accConst n m (decide (g0 ^ (v : Nat) = h)) with hblocks
  have hb0 : ∀ v, blocks v 0 = A v := by intro v; rw [hblocks]; simp
  have hb1 : ∀ v, blocks v 1 = accConst n m (decide (g0 ^ (v : Nat) = h)) := by
    intro v; rw [hblocks]; simp
  have hjcases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by
    intro j
    rcases (show (j : Nat) = 0 ∨ (j : Nat) = 1 from by omega) with hj | hj
    · exact Or.inl (Fin.ext (by simp [hj]))
    · exact Or.inr (Fin.ext (by simp [hj]))
  have hbwf : ∀ v j, WellFormedACC (blocks v j) := by
    intro v j
    rcases hjcases j with hj | hj <;> subst hj
    · rw [hb0 v]; exact hAwf v
    · rw [hb1 v]; exact wellFormedACC_accConst n m _
  have hblay : ∀ v j (q : Fin (blocks v j).gateCount),
      (blocks v j).layer q ≤ max d 1 + 3 := by
    intro v j
    rcases hjcases j with hj | hj <;> subst hj
    · rw [hb0 v]; exact fun q => hAlay v q
    · rw [hb1 v]; intro q; rw [accConst_layer]; omega
  refine ⟨accOrAnd blocks (max d 1 + 3), wellFormedACC_accOrAnd hbwf hblay,
    accOrAnd_layer_le hblay, ?_, fun x => ?_⟩
  · -- size bound
    have hrow : ∀ v : Fin N, (∑ j, (blocks v j).gateCount) + 1 ≤ S + 3 := by
      intro v
      have h0 : (blocks v 0).gateCount ≤ S := by rw [hb0 v]; exact hAsize v
      have h1 : (blocks v 1).gateCount = 1 := by rw [hb1 v]; exact accConst_gateCount n m _
      have hsum : ∑ j, (blocks v j).gateCount
          = (blocks v 0).gateCount + (blocks v 1).gateCount := by
        simp [Fin.sum_univ_two]
      omega
    have hsum : ∑ v : Fin N, ((∑ j, (blocks v j).gateCount) + 1)
        ≤ ∑ _v : Fin N, (S + 3) := Finset.sum_le_sum fun v _ => hrow v
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hgc : (accOrAnd blocks (max d 1 + 3)).gateCount
        = (∑ v : Fin N, ((∑ j, (blocks v j).gateCount) + 1)) + 1 := rfl
    rw [hgc]
    exact Nat.add_le_add_right hsum 1
  · -- semantics
    have hlist : ∀ l : List Nat, (l.map fun t => g0 ^ t).prod = g0 ^ l.sum := by
      intro l
      induction l with
      | nil => simp
      | cons a t ih => simp [ih, pow_add]
    have hprod : (List.ofFn fun i => g0 ^ k i x).prod = g0 ^ (∑ i, k i x) := by
      have hmap : (List.ofFn fun i => g0 ^ k i x)
          = (List.ofFn fun i => k i x).map fun t => g0 ^ t := by
        rw [List.map_ofFn]
        rfl
      rw [hmap, hlist, List.sum_ofFn]
    rw [accAccepts_accOrAnd hbwf hblay x, hprod]
    constructor
    · rintro ⟨v, hv⟩
      have h0 := (hAacc v x).mp (by rw [← hb0 v]; exact hv 0)
      have h1 := (accAccepts_accConst n m _ x).mp (by rw [← hb1 v]; exact hv 1)
      have hmod : (∑ i, k i x) % N = (v : Nat) := by
        rw [h0, Nat.mod_eq_of_lt v.isLt]
      rw [hpow (∑ i, k i x), hmod]
      exact of_decide_eq_true h1
    · intro hx
      refine ⟨⟨(∑ i, k i x) % N, Nat.mod_lt _ hN⟩, fun j => ?_⟩
      rcases hjcases j with hj | hj <;> subst hj
      · rw [hb0 _]
        refine (hAacc _ x).mpr ?_
        simp
      · rw [hb1 _]
        refine (accAccepts_accConst n m _ x).mpr (decide_eq_true ?_)
        simpa using (hpow (∑ i, k i x)).symm.trans hx

end AllenderOQ3.Internal
