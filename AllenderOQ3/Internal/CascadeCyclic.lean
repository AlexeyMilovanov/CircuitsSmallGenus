import AllenderOQ3.Internal.ACCCyclicWord
import AllenderOQ3.Internal.ACCJoin
import AllenderOQ3.Base

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3.Internal

variable {n m : Nat}

theorem cascade_cyclic_layer {N : Nat} (hm : 0 < m) (hNm : N ∣ m)
    {G : Type} [Monoid G] (g0 : G) (hg0 : g0 ^ N = 1)
    {len size_letter size_driver d : Nat}
    {L Y : Type} [Fintype L] [Fintype Y]
    (letter : Fin len → (Fin n → Bool) → L)
    (driver : Fin len → (Fin n → Bool) → Y)
    (kappa : L → Y → Fin N)
    (recLetter : Fin len → L → ACCCircuit n m)
    (recDriver : Fin len → Y → ACCCircuit n m)
    (hwfL : ∀ i l, WellFormedACC (recLetter i l))
    (hlayL : ∀ i l q, (recLetter i l).layer q ≤ d)
    (hsizeL : ∀ i l, (recLetter i l).gateCount ≤ size_letter)
    (haccL : ∀ i l x, ACCAccepts (recLetter i l) x ↔ letter i x = l)
    (hwfD : ∀ i y, WellFormedACC (recDriver i y))
    (hlayD : ∀ i y q, (recDriver i y).layer q ≤ d)
    (hsizeD : ∀ i y, (recDriver i y).gateCount ≤ size_driver)
    (haccD : ∀ i y x, ACCAccepts (recDriver i y) x ↔ driver i x = y)
    (h : G) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ q, a.layer q ≤ max (d + 2) 1 + 5) ∧
      a.gateCount ≤ N * (m ^ N * ((N + 1) * (len * ((Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1) + m + 1) + 1) + 1 + 3) + 1 ∧
      (∀ x, ACCAccepts a x ↔ (List.ofFn fun i => g0 ^ (kappa (letter i x) (driver i x)).val).prod = h) := by
  have h_rec : ∀ i v, ∃ c : ACCCircuit n m,
      WellFormedACC c ∧
      (∀ q, c.layer q ≤ d + 2) ∧
      c.gateCount ≤ (Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1 ∧
      (∀ x, ACCAccepts c x ↔ kappa (letter i x) (driver i x) = v) := by
    intro i v
    set pairs := (Finset.univ.filter (fun p : L × Y => kappa p.1 p.2 = v)).toList with hpairs
    set k := pairs.length with hk
    let g (j : Fin k) : Fin 2 → ACCCircuit n m :=
      Fin.cases (recLetter i (pairs.get (hk ▸ j)).1) (fun _ => recDriver i (pairs.get (hk ▸ j)).2)
    have hwf : ∀ j idx, WellFormedACC (g j idx) := by
      intro j idx
      refine Fin.cases ?_ ?_ idx
      · exact hwfL i _
      · intro _; exact hwfD i _
    have hlay : ∀ j idx q, (g j idx).layer q ≤ d := by
      intro j idx
      refine Fin.cases ?_ ?_ idx
      · intro q; exact hlayL i _ q
      · intro _ q; exact hlayD i _ q
    refine ⟨accOrAnd g d, wellFormedACC_accOrAnd hwf hlay, accOrAnd_layer_le hlay, ?_, ?_⟩
    · simp only [accOrAnd_gateCount, Fin.sum_univ_two, g]
      have : ∀ j, (g j 0).gateCount + (g j 1).gateCount + 1 ≤ size_letter + size_driver + 1 := by
        intro j
        exact Nat.add_le_add (Nat.add_le_add (hsizeL i _) (hsizeD i _)) (le_refl 1)
      have hsum : (∑ j : Fin k, ((g j 0).gateCount + (g j 1).gateCount + 1)) ≤ k * (size_letter + size_driver + 1) := by
        exact Finset.sum_le_card_nsmul Finset.univ _ _ (fun j _ => this j) |>.trans (by simp)
      calc (∑ j : Fin k, ((g j 0).gateCount + (g j 1).gateCount + 1)) + 1
        ≤ k * (size_letter + size_driver + 1) + 1 := Nat.add_le_add_right hsum 1
        _ ≤ (Fintype.card L * Fintype.card Y) * (size_letter + size_driver + 1) + 1 := by
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_right
          have hk_le : k ≤ (Finset.univ : Finset (L × Y)).card := by
            rw [hk, hpairs, Finset.length_toList]
            apply Finset.card_filter_le
          rwa [Finset.card_univ, Fintype.card_prod] at hk_le
    · intro x
      rw [accAccepts_accOrAnd hwf hlay]
      constructor
      · rintro ⟨j, hj⟩
        have hj0 := hj 0
        have hj1 := hj 1
        change ACCAccepts (recLetter i (pairs.get (hk ▸ j)).1) x at hj0
        change ACCAccepts (recDriver i (pairs.get (hk ▸ j)).2) x at hj1
        rw [haccL] at hj0
        rw [haccD] at hj1
        have hmem : pairs.get (hk ▸ j) ∈ pairs := by
          have hget : pairs.get (hk ▸ j) = pairs.get (hk ▸ j) := rfl
          exact List.mem_iff_get.mpr ⟨hk ▸ j, hget⟩
        have hmem' : pairs.get (hk ▸ j) ∈ (Finset.univ.filter (fun p : L × Y => kappa p.1 p.2 = v)).toList := hpairs ▸ hmem
        rw [Finset.mem_toList, Finset.mem_filter] at hmem'
        rw [hj0, hj1]
        exact hmem'.2
      · intro hval
        have hmem : (letter i x, driver i x) ∈ pairs := by
          have hmem' : (letter i x, driver i x) ∈ (Finset.univ.filter (fun p : L × Y => kappa p.1 p.2 = v)).toList := by
            rw [Finset.mem_toList, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hval⟩
          exact hpairs.symm ▸ hmem'
        obtain ⟨j, heq⟩ := List.mem_iff_get.mp hmem
        have hk_j : j.val < k := by rw [hk]; exact j.isLt
        refine ⟨⟨j.val, hk_j⟩, ?_⟩
        intro idx
        have heq' : pairs.get (hk ▸ ⟨j.val, hk_j⟩) = (letter i x, driver i x) := by
          have : (hk ▸ ⟨j.val, hk_j⟩ : Fin pairs.length) = j := Fin.ext rfl
          rw [this]
          exact heq
        have h0 : letter i x = (pairs.get (hk ▸ ⟨j.val, hk_j⟩)).1 := by rw [heq']
        have h1 : driver i x = (pairs.get (hk ▸ ⟨j.val, hk_j⟩)).2 := by rw [heq']
        refine Fin.cases ?_ ?_ idx
        · change ACCAccepts (recLetter i (pairs.get (hk ▸ ⟨j.val, hk_j⟩)).1) x
          rw [haccL]
          exact h0
        · intro _
          change ACCAccepts (recDriver i (pairs.get (hk ▸ ⟨j.val, hk_j⟩)).2) x
          rw [haccD]
          exact h1
  choose rec hrwf hrlay hrsz hracc using h_rec
  have hracc' : ∀ i v x, ACCAccepts (rec i v) x ↔ (kappa (letter i x) (driver i x)).val = v.val := by
    intro i v x
    rw [hracc i v x]
    exact ⟨fun h => h ▸ rfl, fun h => Fin.eq_of_val_eq h⟩
  exact exists_acc_powWord hm hNm g0 hg0 (k := fun i x => (kappa (letter i x) (driver i x)).val)
    (fun i x => (kappa (letter i x) (driver i x)).isLt)
    rec hrwf hrlay hrsz hracc' h

end AllenderOQ3.Internal
