import AllenderOQ3.Internal.CutStepChain
import AllenderOQ3.Internal.PlanarBlock

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# Glue lemmas for the final assembly (§10)

Three small toolkits used by `AllenderOQ3.conditional_of_bridge`:

* monotonicity and two-step composition of `ACCRealizes`;
* elementary polynomial-bound arithmetic (`const_mul_pow_le`, `pow_add_pow_le`),
  used to collapse the concrete size bounds of the assembled circuits into one
  fixed exponent;
* the gap/cut bookkeeping lemma `notMem_of_gap`, which turns the *open* gap
  condition of a cut sequence into the *closed* `P`-freeness that the planar
  block relation consumes.
-/

variable {n w : Nat}

/-! ## `ACCRealizes` toolkit -/

/-- Weakening the depth and size bounds of a realization. -/
theorem accRealizes_mono {M d d' G G' : Nat} {Q : (Fin n → Bool) → Prop}
    (hd : d ≤ d') (hG : G ≤ G') (h : ACCRealizes n M d G Q) :
    ACCRealizes n M d' G' Q := by
  obtain ⟨a, h1, h2, h3, h4⟩ := h
  exact ⟨a, h1, fun g => le_trans (h2 g) hd, le_trans h3 hG, h4⟩

/-- Two-step composition of realizations over the intermediate state. -/
theorem accRealizes_composeStates {M d G : Nat}
    (R R' : (Fin n → Bool) → State w → State w → Prop)
    (hR : ∀ s t : State w, ACCRealizes n M d G (fun x => R x s t))
    (hR' : ∀ s t : State w, ACCRealizes n M d G (fun x => R' x s t))
    (s u : State w) :
    ACCRealizes n M (d + 2) (2 ^ w * (2 * G + 1) + 1)
      (fun x => ∃ t : State w, R x s t ∧ R' x t u) := by
  classical
  choose a hawf had hasize hasem using hR
  choose b hbwf hbd hbsize hbsem using hR'
  refine ⟨accComposeTwo a b d s u,
    wellFormedACC_accComposeTwo a b d hawf hbwf had hbd s u,
    accComposeTwo_layer_le a b d had hbd s u, ?_, ?_⟩
  · rw [accComposeTwo_gateCount]
    have hcard : Fintype.card (State w) = 2 ^ w := by
      change Fintype.card (Fin w → Bool) = 2 ^ w
      simp
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (Fintype.card (State w)))),
        ((a s ((Fintype.equivFin (State w)).symm i)).gateCount +
          (b ((Fintype.equivFin (State w)).symm i) u).gateCount + 1) ≤ 2 * G + 1 := by
      intro i _
      have h1 := hasize s ((Fintype.equivFin (State w)).symm i)
      have h2 := hbsize ((Fintype.equivFin (State w)).symm i) u
      omega
    have hsum := Finset.sum_le_sum hterm
    have hconst : (∑ _i : Fin (Fintype.card (State w)), (2 * G + 1))
        = Fintype.card (State w) * (2 * G + 1) := by
      simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hconst] at hsum
    have hrw : Fintype.card (State w) * (2 * G + 1) = 2 ^ w * (2 * G + 1) := by rw [hcard]
    omega
  · intro x
    rw [accAccepts_accComposeTwo a b d hawf hbwf had hbd s u x]
    exact exists_congr fun t => and_congr (hasem s t x) (hbsem t u x)

/-! ## Polynomial bound arithmetic -/

/-- A constant multiple of a power is absorbed by raising the exponent. -/
theorem const_mul_pow_le {T : Nat} (hT : 2 ≤ T) (A F : Nat) : A * T ^ F ≤ T ^ (A + F) := by
  have h1 : A ≤ T ^ A := le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hT A)
  calc A * T ^ F ≤ T ^ A * T ^ F := Nat.mul_le_mul_right _ h1
    _ = T ^ (A + F) := (pow_add T A F).symm

/-- A sum of two powers is absorbed by one more in the exponent. -/
theorem pow_add_pow_le {T : Nat} (hT : 2 ≤ T) (a b : Nat) :
    T ^ a + T ^ b ≤ T ^ (max a b + 1) := by
  have ha : T ^ a ≤ T ^ max a b := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hb : T ^ b ≤ T ^ max a b := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have : T ^ (max a b + 1) = T ^ max a b * T := pow_succ T _
  have h2 : T ^ max a b * 2 ≤ T ^ max a b * T := Nat.mul_le_mul_left _ hT
  omega

/-- A gate count bounded by `(n+1)^σ` gives `S + 1 ≤ (n+1)^(σ+1)`. -/
theorem succ_le_pow_succ {T S σ : Nat} (hT : 2 ≤ T) (hS : S ≤ T ^ σ) : S + 1 ≤ T ^ (σ + 1) := by
  have h1 : T ^ σ * 2 ≤ T ^ σ * T := Nat.mul_le_mul_left _ hT
  have h2 : T ^ (σ + 1) = T ^ σ * T := pow_succ T σ
  have h3 : 1 ≤ T ^ σ := Nat.one_le_pow _ _ (by omega)
  omega

/-- The size exponent produced by the final assembly, before the §9 collapse:
an explicit `n`-independent exponent bounding the size of every relation circuit. -/
def assemblySizeExp (width M eB σ : Nat) : Nat :=
  2 + (2 ^ width + 3 +
    (max (10 * (2 * M + 2) + (σ + 1))
      ((2 * M + 2) + (σ + 1) * (eB + (2 * width + 1))) + 1))

/-! ## Gap bookkeeping -/

/-- A one-layer block run is exactly a one-step transition. -/
theorem reach_one_iff {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    (i : Nat) (s t : State w) : Reach idx x i 1 s t ↔ OneStep idx x i s t :=
  ⟨fun ⟨_, h, hu⟩ => hu ▸ h, fun h => ⟨t, h, rfl⟩⟩

/-- If the *open* interval `(p, q)` avoids `cutSet P` and `q ≥ p + 2`, then the *closed*
interval `[p, q - 1]` avoids `P` itself.  This is exactly the interface mismatch between
the §6 cut sequence and the §8 planar block relation. -/
theorem notMem_of_gap {P : Finset Nat} {p q : Nat} (hpq : p + 2 ≤ q)
    (h : ∀ l, p < l → l < q → l ∉ cutSet P) :
    ∀ i, p ≤ i → i ≤ q - 1 → i ∉ P := by
  intro i hpi hiq hmem
  rcases Nat.eq_or_lt_of_le hpi with rfl | hlt
  · exact h (p + 1) (by omega) (by omega) (mem_cutSet.mpr ⟨p, hmem, Or.inr rfl⟩)
  · exact h i hlt (by omega) (mem_cutSet.mpr ⟨i, hmem, Or.inl rfl⟩)

end AllenderOQ3.Internal
