import AllenderOQ3.Internal.ACCGadgets
import AllenderOQ3.Internal.ACCNot

/-!
# Constant thresholds are `ACC` (indeed `AC⁰`) computable

For a *constant* `j`, the predicate "at least `j` of the `len` given circuits
accept" is a disjunction, over the `len ^ j` injective tuples of positions, of a
conjunction of `j` of the circuits: constant depth and size polynomial in `len`
times the size of the given circuits.  Combined with negation this gives the
exact count "`j` of the circuits accept".

These are the counting gadgets that the word problem of a finite *commutative*
monoid needs beside the `MOD` gates of `ACCSumMod`: the exponent of a letter in
the product matters exactly, until it exceeds the index of the monoid, after
which only its residue modulo the period matters.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {n m : Nat}

/-- **A finite set has at least `j` elements iff it receives an injective tuple
of length `j`.** -/
theorem exists_injective_into_iff {len j : Nat} (S : Finset (Fin len)) :
    (∃ t : Fin j → Fin len, Function.Injective t ∧ ∀ k, t k ∈ S) ↔ j ≤ S.card := by
  classical
  constructor
  · rintro ⟨t, htinj, htmem⟩
    have hsub : (Finset.univ : Finset (Fin j)).image t ⊆ S := by
      intro y hy
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
      exact htmem k
    have hcard : ((Finset.univ : Finset (Fin j)).image t).card = j := by
      rw [Finset.card_image_of_injective _ htinj, Finset.card_univ, Fintype.card_fin]
    rw [← hcard]
    exact Finset.card_le_card hsub
  · intro hj
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hj
    set ee := T.equivFin with hee
    refine ⟨fun k => (ee.symm ⟨k.val, by rw [hTcard]; exact k.isLt⟩ : T), ?_, ?_⟩
    · intro k₁ k₂ h
      have h' : ee.symm ⟨k₁.val, by rw [hTcard]; exact k₁.isLt⟩
          = ee.symm ⟨k₂.val, by rw [hTcard]; exact k₂.isLt⟩ := Subtype.ext h
      have h'' := congrArg Fin.val (ee.symm.injective h')
      exact Fin.ext h''
    · intro k
      exact hTS (ee.symm ⟨k.val, by rw [hTcard]; exact k.isLt⟩).2

/-- **At least `j` of the circuits accept.** -/
theorem exists_acc_countGe {len d Sz j : Nat} (f : Fin len → ACCCircuit n m)
    (hwf : ∀ i, WellFormedACC (f i)) (hlay : ∀ i q, (f i).layer q ≤ d)
    (hsz : ∀ i, (f i).gateCount ≤ Sz) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ d + 4) ∧
      a.gateCount ≤ len ^ j * (j * Sz + 4) + 1 ∧
      (∀ x, ACCAccepts a x ↔
        j ≤ (Finset.univ.filter fun i : Fin len => ACCAccepts (f i) x).card) := by
  classical
  have hand : ∀ t : Fin j → Fin len, ∃ c : ACCCircuit n m,
      WellFormedACC c ∧ (∀ q, c.layer q ≤ d + 2) ∧ c.gateCount ≤ j * Sz + 2 ∧
      (∀ x, ACCAccepts c x ↔ ∀ k, ACCAccepts (f (t k)) x) := by
    intro t
    exact exists_acc_bigAnd (fun k => f (t k)) (fun k => hwf _) (fun k q => hlay _ q)
      (fun k => hsz _)
  choose AND hANDwf hANDlay hANDsz hANDacc using hand
  set K := Fintype.card (Fin j → Fin len) with hK
  set ee := Fintype.equivFin (Fin j → Fin len) with hee
  set inner : Fin K → ACCCircuit n m := fun i =>
    if Function.Injective (ee.symm i) then AND (ee.symm i) else accConst n m false with hinner
  have hinner_pos : ∀ i, Function.Injective (ee.symm i) → inner i = AND (ee.symm i) := by
    intro i hi
    simp only [hinner, if_pos hi]
  have hinner_neg : ∀ i, ¬ Function.Injective (ee.symm i) → inner i = accConst n m false := by
    intro i hi
    simp only [hinner, if_neg hi]
  have hinner_wf : ∀ i, WellFormedACC (inner i) := by
    intro i
    by_cases hi : Function.Injective (ee.symm i)
    · rw [hinner_pos i hi]; exact hANDwf _
    · rw [hinner_neg i hi]; exact wellFormedACC_accConst n m false
  have hinner_lay : ∀ i q, (inner i).layer q ≤ d + 2 := by
    intro i
    by_cases hi : Function.Injective (ee.symm i)
    · rw [hinner_pos i hi]; exact hANDlay _
    · rw [hinner_neg i hi]
      intro q
      rw [accConst_layer]
      omega
  have hinner_sz : ∀ i, (inner i).gateCount ≤ j * Sz + 2 := by
    intro i
    by_cases hi : Function.Injective (ee.symm i)
    · rw [hinner_pos i hi]; exact hANDsz _
    · rw [hinner_neg i hi, accConst_gateCount]
      omega
  obtain ⟨a, hawf, halay, hasz, haacc⟩ :=
    exists_acc_orPair (n := n) (m := m) (K := K) (d := d + 2)
      (S1 := j * Sz + 2) (S2 := 1)
      inner (fun _ => accConst n m true) hinner_wf
      (fun _ => wellFormedACC_accConst n m true) hinner_lay
      (fun _ q => by rw [accConst_layer]; omega)
      hinner_sz (fun _ => le_of_eq (accConst_gateCount n m true))
  have hKcard : K = len ^ j := by
    rw [hK]
    simp
  refine ⟨a, hawf, halay, ?_, ?_⟩
  · calc a.gateCount ≤ K * (j * Sz + 2 + 1 + 1) + 1 := hasz
      _ = len ^ j * (j * Sz + 4) + 1 := by rw [hKcard]
  · intro x
    rw [haacc x, ← exists_injective_into_iff
      (S := Finset.univ.filter fun i : Fin len => ACCAccepts (f i) x) (j := j)]
    constructor
    · rintro ⟨i, hi, -⟩
      by_cases hinj : Function.Injective (ee.symm i)
      · rw [hinner_pos i hinj, hANDacc _ x] at hi
        exact ⟨ee.symm i, hinj, fun k => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi k⟩⟩
      · rw [hinner_neg i hinj, accAccepts_accConst] at hi
        exact absurd hi (by simp)
    · rintro ⟨t, htinj, htmem⟩
      refine ⟨ee t, ?_, (accAccepts_accConst n m true x).mpr rfl⟩
      have hsymm : ee.symm (ee t) = t := ee.symm_apply_apply t
      have hinj' : Function.Injective (ee.symm (ee t)) := by rw [hsymm]; exact htinj
      rw [hinner_pos _ hinj', hANDacc _ x, hsymm]
      intro k
      exact (Finset.mem_filter.mp (htmem k)).2

/-- **Exactly `j` of the circuits accept.** -/
theorem exists_acc_countEq {len d Sz j : Nat} (f : Fin len → ACCCircuit n m)
    (hwf : ∀ i, WellFormedACC (f i)) (hlay : ∀ i q, (f i).layer q ≤ d)
    (hsz : ∀ i, (f i).gateCount ≤ Sz) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ d + 8) ∧
      a.gateCount
        ≤ 2 * (len ^ (j + 1) * ((j + 1) * Sz + 4) + len ^ j * (j * Sz + 4) + 2) + 2 ∧
      (∀ x, ACCAccepts a x ↔
        (Finset.univ.filter fun i : Fin len => ACCAccepts (f i) x).card = j) := by
  classical
  obtain ⟨a₁, h1wf, h1lay, h1sz, h1acc⟩ := exists_acc_countGe (j := j) f hwf hlay hsz
  obtain ⟨a₂, h2wf, h2lay, h2sz, h2acc⟩ := exists_acc_countGe (j := j + 1) f hwf hlay hsz
  -- the negation of "at least `j + 1`"
  set a₃ := accNot a₂ (d + 4) with ha₃
  have h3wf : WellFormedACC a₃ := wellFormedACC_accNot h2wf h2lay
  have h3lay : ∀ q, a₃.layer q ≤ d + 5 := by
    intro q
    have := accNot_layer_le (a := a₂) (d := d + 4) h2lay q
    omega
  have h3sz : a₃.gateCount ≤ len ^ (j + 1) * ((j + 1) * Sz + 4) + 2 := by
    rw [ha₃, accNot_gateCount]
    omega
  have h3acc : ∀ x, ACCAccepts a₃ x ↔ ¬ ACCAccepts a₂ x := by
    intro x
    exact accAccepts_accNot h2wf h2lay x
  -- conjoin
  set pair : Fin 2 → ACCCircuit n m := fun i => if (i : Nat) = 0 then a₁ else a₃ with hpair
  have hp0 : pair 0 = a₁ := by simp [hpair]
  have hp1 : pair 1 = a₃ := by simp [hpair]
  have hcases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
    intro i
    rcases (show (i : Nat) = 0 ∨ (i : Nat) = 1 from by omega) with hi | hi
    · exact Or.inl (Fin.ext (by simp [hi]))
    · exact Or.inr (Fin.ext (by simp [hi]))
  have hpwf : ∀ i, WellFormedACC (pair i) := by
    intro i
    rcases hcases i with rfl | rfl
    · rw [hp0]; exact h1wf
    · rw [hp1]; exact h3wf
  have hplay : ∀ i q, (pair i).layer q ≤ d + 5 := by
    intro i
    rcases hcases i with rfl | rfl
    · rw [hp0]; exact fun q => le_trans (h1lay q) (by omega)
    · rw [hp1]; exact h3lay
  have hpsz : ∀ i, (pair i).gateCount
      ≤ len ^ (j + 1) * ((j + 1) * Sz + 4) + len ^ j * (j * Sz + 4) + 2 := by
    intro i
    rcases hcases i with rfl | rfl
    · rw [hp0]; omega
    · rw [hp1]; omega
  obtain ⟨a, hawf, halay, hasz, haacc⟩ := exists_acc_bigAnd pair hpwf hplay hpsz
  refine ⟨a, hawf, fun q => le_trans (halay q) (by omega), ?_, ?_⟩
  · exact le_trans hasz (by omega)
  · intro x
    rw [haacc x]
    constructor
    · intro h
      have hge := (h1acc x).mp (by have := h 0; rwa [hp0] at this)
      have hlt := (h3acc x).mp (by have := h 1; rwa [hp1] at this)
      have hlt' : ¬ (j + 1 ≤ (Finset.univ.filter fun i : Fin len => ACCAccepts (f i) x).card) :=
        fun hc => hlt ((h2acc x).mpr hc)
      omega
    · intro h i
      rcases hcases i with rfl | rfl
      · rw [hp0]
        exact (h1acc x).mpr (by omega)
      · rw [hp1]
        refine (h3acc x).mpr (fun hc => ?_)
        have := (h2acc x).mp hc
        omega

end Internal
end AllenderOQ3
