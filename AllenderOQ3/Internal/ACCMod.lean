import AllenderOQ3.Internal.ACCJoin
import AllenderOQ3.Internal.ACCLocal

namespace AllenderOQ3
namespace Internal

open Classical in
def accCountEq {n m k : Nat} (f : Fin k → ACCCircuit n m) (d : Nat) (r : Nat) : ACCCircuit n m :=
  let pad := (m - (r % m)) % m
  let f' : Fin (k + pad) → ACCCircuit n m := fun i =>
    if h : i.val < k then
      f ⟨i.val, h⟩
    else
      accConst n m true
  accJoin f' (max d 1) .modGate

open Classical in
/-- Every block of the padded family used by `accCountEq` is well formed. -/
theorem padCountEq_wellFormed {n m k r : Nat} {f : Fin k → ACCCircuit n m}
    (hf : ∀ i, WellFormedACC (f i)) :
    ∀ i : Fin (k + ((m - (r % m)) % m)),
      WellFormedACC (if h : i.val < k then f ⟨i.val, h⟩ else accConst n m true) := by
  intro i
  by_cases h : i.val < k
  · rw [dif_pos h]; exact hf _
  · rw [dif_neg h]; exact wellFormedACC_accConst n m true

open Classical in
/-- Every block of the padded family used by `accCountEq` has layers `≤ max d 1`. -/
theorem padCountEq_layer {n m k d r : Nat} {f : Fin k → ACCCircuit n m}
    (hd : ∀ (i : Fin k) (a : Fin (f i).gateCount), (f i).layer a ≤ d) :
    ∀ (i : Fin (k + ((m - (r % m)) % m)))
      (a : Fin (if h : i.val < k then f ⟨i.val, h⟩ else accConst n m true).gateCount),
      (if h : i.val < k then f ⟨i.val, h⟩ else accConst n m true).layer a ≤ max d 1 := by
  intro i
  by_cases h : i.val < k
  · have hE : (if h : i.val < k then f ⟨i.val, h⟩ else accConst n m true) = f ⟨i.val, h⟩ :=
      dif_pos h
    rw [hE]
    exact fun a => le_trans (hd _ a) (le_max_left _ _)
  · have hE : (if h : i.val < k then f ⟨i.val, h⟩ else accConst n m true) = accConst n m true :=
      dif_neg h
    rw [hE]
    exact fun a => by rw [accConst_layer]; exact le_max_right d 1

open Classical in
theorem wellFormedACC_accCountEq {n m k d r : Nat} {f : Fin k → ACCCircuit n m}
    (hf : ∀ i, WellFormedACC (f i))
    (hd : ∀ (i : Fin k) (a : Fin (f i).gateCount), (f i).layer a ≤ d) :
    WellFormedACC (accCountEq f d r) := by
  classical
  have hlit : ∀ (i : Fin n) (b : Bool), (ACCGate.modGate : ACCGate n m) ≠ .literal i b := by
    intro i b; simp
  have hnot : (ACCGate.modGate : ACCGate n m) ≠ .notGate := by simp
  exact wellFormedACC_accJoin (padCountEq_wellFormed hf) (padCountEq_layer hd) hlit hnot

open Classical in
theorem accCountEq_layer_le {n m k d r : Nat} {f : Fin k → ACCCircuit n m}
    (hd : ∀ (i : Fin k) (a : Fin (f i).gateCount), (f i).layer a ≤ d)
    (g : Fin (accCountEq f d r).gateCount) :
    (accCountEq f d r).layer g ≤ max d 1 + 1 := by
  classical
  exact accJoin_layer_le (padCountEq_layer hd) g

open Classical in
theorem accCountEq_gateCount {n m k d r : Nat} {f : Fin k → ACCCircuit n m} :
    (accCountEq f d r).gateCount = (∑ i : Fin k, (f i).gateCount) + ((m - (r % m)) % m) + 1 := by
  classical
  simp only [accCountEq, accJoin_gateCount]
  rw [Fin.sum_univ_add]
  congr 2
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.val_castAdd, i.isLt, dif_pos]
  · simp [accConst_gateCount]

/-- The padding constant `(m - r % m) % m` shifts a count into the residue `r % m`. -/
theorem pad_mod_eq_zero_iff {m C r : Nat} (hm : 0 < m) :
    (C + (m - r % m) % m) % m = 0 ↔ C % m = r % m := by
  have hs : r % m < m := Nat.mod_lt _ hm
  have hmm : ∀ a : Nat, a % m % m = a % m := fun a => Nat.mod_mod_of_dvd a (dvd_refl m)
  have hpad : (C + (m - r % m) % m) % m = (C + (m - r % m)) % m := by
    conv_lhs => rw [Nat.add_mod, hmm]
    rw [← Nat.add_mod]
  rw [hpad]
  have key : C + (m - r % m) + r % m = C + m := by omega
  have key2 : r % m + (m - r % m) = m := by omega
  constructor
  · intro h
    have h0 : Nat.ModEq m (C + (m - r % m)) 0 := by
      unfold Nat.ModEq; simpa using h
    have h2 := h0.add_right (r % m)
    unfold Nat.ModEq at h2
    rw [key, Nat.zero_add, Nat.add_mod_right, Nat.mod_eq_of_lt hs] at h2
    exact h2
  · intro h
    have h0 : Nat.ModEq m C (r % m) := by
      unfold Nat.ModEq; rw [h, hmm]
    have h2 := h0.add_right (m - r % m)
    unfold Nat.ModEq at h2
    rw [key2, Nat.mod_self] at h2
    exact h2

open Classical in
/-- The padded family has exactly `pad` more accepting blocks than the original. -/
theorem padCountEq_card {n m k r : Nat} {f : Fin k → ACCCircuit n m} (x : Fin n → Bool) :
    (Finset.univ.filter fun i : Fin (k + ((m - (r % m)) % m)) =>
        ACCAccepts (if h : i.val < k then f ⟨i.val, h⟩ else accConst n m true) x).card
      = (Finset.univ.filter fun i : Fin k => ACCAccepts (f i) x).card + ((m - (r % m)) % m) := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.val_castAdd, i.isLt, dif_pos, Fin.eta]
  · simp [accAccepts_accConst]

open Classical in
theorem accAccepts_accCountEq {n m k d r : Nat} {f : Fin k → ACCCircuit n m}
    (hm : 0 < m)
    (hf : ∀ i, WellFormedACC (f i))
    (hd : ∀ (i : Fin k) (a : Fin (f i).gateCount), (f i).layer a ≤ d)
    (x : Fin n → Bool) :
    ACCAccepts (accCountEq f d r) x ↔
      (Finset.univ.filter fun i => ACCAccepts (f i) x).card % m = r % m := by
  classical
  have h := accAccepts_accJoin_mod (n := n) (m := m) (k := k + ((m - (r % m)) % m))
    (f := fun i => if h : i.val < k then f ⟨i.val, h⟩ else accConst n m true)
    (d := max d 1) (padCountEq_wellFormed hf) (padCountEq_layer hd) x
  rw [padCountEq_card (r := r) x] at h
  rw [show (accCountEq f d r)
      = accJoin (fun i : Fin (k + ((m - (r % m)) % m)) =>
          if h : i.val < k then f ⟨i.val, h⟩ else accConst n m true) (max d 1) .modGate from rfl]
  rw [h, pad_mod_eq_zero_iff hm]

open Classical in
def accModIn {n m k : Nat} (f : Fin k → ACCCircuit n m) (d : Nat) (subset : Finset (Fin k)) (r : Nat) : ACCCircuit n m :=
  let f' : Fin k → ACCCircuit n m := fun i =>
    if i ∈ subset then
      f i
    else
      accConst n m false
  accCountEq f' d r

open Classical in
/-- The block family of `accModIn`, unfolded as a `accJoin` over the padded index set. -/
theorem accModIn_eq_accJoin {n m k d r : Nat} {subset : Finset (Fin k)}
    {f : Fin k → ACCCircuit n m} :
    accModIn f d subset r
      = accJoin (fun i : Fin (k + ((m - (r % m)) % m)) =>
          if h : i.val < k then
            (if (⟨i.val, h⟩ : Fin k) ∈ subset then f ⟨i.val, h⟩ else accConst n m false)
          else accConst n m true) (max d 1) .modGate := rfl

open Classical in
/-- Every block of the padded family used by `accModIn` is well formed. -/
theorem padModIn_wellFormed {n m k r : Nat} {subset : Finset (Fin k)}
    {f : Fin k → ACCCircuit n m} (hf : ∀ i ∈ subset, WellFormedACC (f i)) :
    ∀ i : Fin (k + ((m - (r % m)) % m)),
      WellFormedACC (if h : i.val < k then
          (if (⟨i.val, h⟩ : Fin k) ∈ subset then f ⟨i.val, h⟩ else accConst n m false)
        else accConst n m true) := by
  intro i
  by_cases h : i.val < k
  · rw [dif_pos h]
    by_cases hi : (⟨i.val, h⟩ : Fin k) ∈ subset
    · rw [if_pos hi]; exact hf _ hi
    · rw [if_neg hi]; exact wellFormedACC_accConst n m false
  · rw [dif_neg h]; exact wellFormedACC_accConst n m true

open Classical in
/-- Every block of the padded family used by `accModIn` has layers `≤ max d 1`. -/
theorem padModIn_layer {n m k d r : Nat} {subset : Finset (Fin k)}
    {f : Fin k → ACCCircuit n m}
    (hd : ∀ i ∈ subset, ∀ a : Fin (f i).gateCount, (f i).layer a ≤ d) :
    ∀ (i : Fin (k + ((m - (r % m)) % m)))
      (a : Fin (if h : i.val < k then
          (if (⟨i.val, h⟩ : Fin k) ∈ subset then f ⟨i.val, h⟩ else accConst n m false)
        else accConst n m true).gateCount),
      (if h : i.val < k then
          (if (⟨i.val, h⟩ : Fin k) ∈ subset then f ⟨i.val, h⟩ else accConst n m false)
        else accConst n m true).layer a ≤ max d 1 := by
  intro i
  by_cases h : i.val < k
  · by_cases hi : (⟨i.val, h⟩ : Fin k) ∈ subset
    · have hE : (if h : i.val < k then
            (if (⟨i.val, h⟩ : Fin k) ∈ subset then f ⟨i.val, h⟩ else accConst n m false)
          else accConst n m true) = f ⟨i.val, h⟩ := by
        rw [dif_pos h, if_pos hi]
      rw [hE]
      exact fun a => le_trans (hd _ hi a) (le_max_left _ _)
    · have hE : (if h : i.val < k then
            (if (⟨i.val, h⟩ : Fin k) ∈ subset then f ⟨i.val, h⟩ else accConst n m false)
          else accConst n m true) = accConst n m false := by
        rw [dif_pos h, if_neg hi]
      rw [hE]
      exact fun a => by rw [accConst_layer]; exact le_max_right d 1
  · have hE : (if h : i.val < k then
          (if (⟨i.val, h⟩ : Fin k) ∈ subset then f ⟨i.val, h⟩ else accConst n m false)
        else accConst n m true) = accConst n m true := dif_neg h
    rw [hE]
    exact fun a => by rw [accConst_layer]; exact le_max_right d 1

open Classical in
theorem wellFormedACC_accModIn {n m k d r : Nat} {subset : Finset (Fin k)} {f : Fin k → ACCCircuit n m}
    (hf : ∀ i ∈ subset, WellFormedACC (f i))
    (hd : ∀ i ∈ subset, ∀ a : Fin (f i).gateCount, (f i).layer a ≤ d) :
    WellFormedACC (accModIn f d subset r) := by
  classical
  have hlit : ∀ (i : Fin n) (b : Bool), (ACCGate.modGate : ACCGate n m) ≠ .literal i b := by
    intro i b; simp
  have hnot : (ACCGate.modGate : ACCGate n m) ≠ .notGate := by simp
  rw [accModIn_eq_accJoin (f := f) (d := d) (subset := subset) (r := r)]
  exact wellFormedACC_accJoin (padModIn_wellFormed hf) (padModIn_layer hd) hlit hnot

open Classical in
theorem accModIn_layer_le {n m k d r : Nat} {subset : Finset (Fin k)} {f : Fin k → ACCCircuit n m}
    (hd : ∀ i ∈ subset, ∀ a : Fin (f i).gateCount, (f i).layer a ≤ d)
    (g : Fin (accModIn f d subset r).gateCount) :
    (accModIn f d subset r).layer g ≤ max d 1 + 1 := by
  classical
  exact accJoin_layer_le (padModIn_layer (r := r) hd) g

open Classical in
/-- Summing a function that is `1` off a subset. -/
theorem sum_ite_mem_const {k : Nat} (s : Finset (Fin k)) (g : Fin k → Nat) :
    ∑ i : Fin k, (if i ∈ s then g i else 1) = (∑ i ∈ s, g i) + (k - s.card) := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.filter_univ_mem, Finset.sum_const, smul_eq_mul, mul_one]
  congr 1
  have hc : ({x | x ∉ s} : Finset (Fin k)) = sᶜ := by ext x; simp
  rw [hc, Finset.card_compl]
  simp

open Classical in
theorem accModIn_gateCount {n m k d r : Nat} {subset : Finset (Fin k)} {f : Fin k → ACCCircuit n m} :
    (accModIn f d subset r).gateCount = (∑ i ∈ subset, (f i).gateCount) + (k - subset.card) + ((m - (r % m)) % m) + 1 := by
  classical
  have hpt : ∀ i : Fin k, (if i ∈ subset then f i else accConst n m false).gateCount
      = if i ∈ subset then (f i).gateCount else 1 := by
    intro i; by_cases hi : i ∈ subset <;> simp [hi, accConst_gateCount]
  have hsum : (∑ i : Fin k, (if i ∈ subset then f i else accConst n m false).gateCount)
      = (∑ i ∈ subset, (f i).gateCount) + (k - subset.card) := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    exact sum_ite_mem_const subset _
  change (accCountEq (fun i => if i ∈ subset then f i else accConst n m false) d r).gateCount = _
  rw [accCountEq_gateCount, hsum]

open Classical in
/-- The padded `accModIn` family has exactly `pad` more accepting blocks than `f` on `subset`. -/
theorem padModIn_card {n m k r : Nat} {subset : Finset (Fin k)}
    {f : Fin k → ACCCircuit n m} (x : Fin n → Bool) :
    (Finset.univ.filter fun i : Fin (k + ((m - (r % m)) % m)) =>
        ACCAccepts (if h : i.val < k then
            (if (⟨i.val, h⟩ : Fin k) ∈ subset then f ⟨i.val, h⟩ else accConst n m false)
          else accConst n m true) x).card
      = (subset.filter fun i => ACCAccepts (f i) x).card + ((m - (r % m)) % m) := by
  classical
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  congr 1
  · have hpt : ∀ i : Fin k,
        (if ACCAccepts (if h : (Fin.castAdd ((m - (r % m)) % m) i).val < k then
            (if (⟨(Fin.castAdd ((m - (r % m)) % m) i).val, h⟩ : Fin k) ∈ subset then
              f ⟨(Fin.castAdd ((m - (r % m)) % m) i).val, h⟩ else accConst n m false)
          else accConst n m true) x then 1 else 0)
          = if i ∈ subset then (if ACCAccepts (f i) x then 1 else 0) else 0 := by
      intro i
      by_cases hi : i ∈ subset <;>
        simp [Fin.val_castAdd, i.isLt, hi, accAccepts_accConst]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_ite_mem, Finset.univ_inter]
  · simp [accAccepts_accConst]

open Classical in
theorem accAccepts_accModIn {n m k d r : Nat} {subset : Finset (Fin k)} {f : Fin k → ACCCircuit n m}
    (hm : 0 < m)
    (hf : ∀ i ∈ subset, WellFormedACC (f i))
    (hd : ∀ i ∈ subset, ∀ a : Fin (f i).gateCount, (f i).layer a ≤ d)
    (x : Fin n → Bool) :
    ACCAccepts (accModIn f d subset r) x ↔
      (subset.filter fun i => ACCAccepts (f i) x).card % m = r % m := by
  classical
  have h := accAccepts_accJoin_mod (padModIn_wellFormed (r := r) hf)
    (padModIn_layer (r := r) (d := d) hd) x
  rw [accModIn_eq_accJoin, h, padModIn_card x, pad_mod_eq_zero_iff hm]

end Internal
end AllenderOQ3
