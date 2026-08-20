import AllenderOQ3.Internal.ACCSemantics

set_option autoImplicit false
namespace AllenderOQ3.Internal

/-!
# A3: Small-n Truth Table ACC Circuit
Constructs a depth-2 DNF ACC circuit deciding any predicate on `Fin n → Bool`.
Handles the `n = 0` single-gate case explicitly.
-/

noncomputable def accTruthTable (n m : Nat) (P : (Fin n → Bool) → Prop)
  (dec : ∀ x, Decidable (P x)) : ACCCircuit n m :=
  match n with
  | 0 =>
    let x0 : Fin 0 → Bool := fun i => i.elim0
    { gateCount := 1
      output := ⟨0, by omega⟩
      kind := fun _ => match dec x0 with
        | isTrue _ => .andGate
        | isFalse _ => .orGate
      layer := fun _ => 1
      edge := fun _ _ => false }
  | n' + 1 =>
    { gateCount := 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) + 1
      output := ⟨2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool), by omega⟩
      kind := fun g =>
        if h1 : g.val < 2 * (n' + 1) then
          .literal ⟨g.val / 2, by omega⟩ (g.val % 2 = 1)
        else if h2 : g.val < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) then
          .andGate
        else
          .orGate
      layer := fun g =>
        if g.val < 2 * (n' + 1) then 0
        else if g.val < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) then 1
        else 2
      edge := fun u v =>
        if h1 : u.val < 2 * (n' + 1) ∧ 2 * (n' + 1) ≤ v.val ∧ v.val < 2 * (n' + 1) + Fintype.card
          (Fin (n' + 1) → Bool) then
          let val := (Fintype.equivFin (Fin (n' + 1) → Bool)).symm ⟨v.val - 2 * (n' + 1), by omega⟩
          let i : Fin (n' + 1) := ⟨u.val / 2, by omega⟩
          let isNeg := u.val % 2 = 1
          if isNeg then val i = false else val i = true
        else if h2 : 2 * (n' + 1) ≤ u.val ∧ u.val < 2 * (n' + 1) + Fintype.card
          (Fin (n' + 1) → Bool) ∧ v.val = 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) then
          let val := (Fintype.equivFin (Fin (n' + 1) → Bool)).symm ⟨u.val - 2 * (n' + 1), by omega⟩
          match dec val with
          | isTrue _ => true
          | isFalse _ => false
        else
          false }

theorem wellFormedACC_accTruthTable (n m : Nat) (P : (Fin n → Bool) → Prop)
  (dec : ∀ x, Decidable (P x)) :
    WellFormedACC (accTruthTable n m P dec) := by
  cases n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro u v h
      simp [accTruthTable] at h
    · intro g
      exact ⟨fun h => by simp [accTruthTable] at h, fun ⟨i, _, _⟩ => i.elim0⟩
    · intro g hg
      simp only [accTruthTable] at hg
      split at hg <;> simp at hg
  | succ n' =>
    refine ⟨?_, ?_, ?_⟩
    · intro u v h
      simp only [accTruthTable] at h ⊢
      split at h
      · rename_i h1
        obtain ⟨hu, hv1, hv2⟩ := h1
        split_ifs <;> omega
      · split at h
        · rename_i h2
          obtain ⟨hu1, hu2, hv⟩ := h2
          split_ifs <;> omega
        · simp at h
    · intro g
      simp only [accTruthTable]
      by_cases hg : g.val < 2 * (n' + 1)
      · rw [if_pos hg, dif_pos hg]
        exact ⟨fun _ => ⟨_, _, rfl⟩, fun _ => rfl⟩
      · rw [if_neg hg, dif_neg hg]
        split_ifs <;> simp
    · intro g hg
      simp only [accTruthTable] at hg
      split_ifs at hg

theorem evalACC_accTruthTable (n m : Nat) (P : (Fin n → Bool) → Prop) (dec : ∀ x, Decidable (P x))
  (x : Fin n → Bool) :
    evalACC (accTruthTable n m P dec) (wellFormedACC_accTruthTable n m P dec) x
      (accTruthTable n m P dec).output = decide (P x) := by
  cases n with
  | zero =>
    have hx : x = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
    have hV : ACCValuation (accTruthTable 0 m P dec) x
        (fun _ => @decide (P x) (dec x)) := by
      intro g
      simp only [accTruthTable]
      subst hx
      cases hd : dec (fun i : Fin 0 => i.elim0) with
      | isTrue h => simpa using h
      | isFalse h => simpa using h
    have heq := (accValuation_iff_eq_evalACC (wellFormedACC_accTruthTable 0 m P dec)).mp hV
    exact (congrFun heq (accTruthTable 0 m P dec).output).symm
  | succ n' =>
    let V : Fin (accTruthTable (n' + 1) m P dec).gateCount → Bool := fun g =>
      if h1 : g.val < 2 * (n' + 1) then
        (if g.val % 2 = 1 then !(x ⟨g.val / 2, by omega⟩) else x ⟨g.val / 2, by omega⟩)
      else if h2 : g.val < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) then
        decide (x = (Fintype.equivFin (Fin (n' + 1) → Bool)).symm ⟨g.val - 2 * (n' + 1), by omega⟩)
      else @decide (P x) (dec x)
    have hV : ACCValuation (accTruthTable (n' + 1) m P dec) x V := by
      intro g
      by_cases h1 : g.val < 2 * (n' + 1)
      · rw [show (accTruthTable (n' + 1) m P dec).kind g
          = .literal ⟨g.val / 2, by omega⟩ (g.val % 2 = 1) from by
          simp only [accTruthTable]; rw [dif_pos h1]]
        simp only [V, dif_pos h1]
        split <;> simp_all
      · by_cases h2 : g.val < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool)
        · rw [show (accTruthTable (n' + 1) m P dec).kind g = .andGate from by
            simp only [accTruthTable]; rw [dif_neg h1, dif_pos h2]]
          have hVg : V g = decide (x = (Fintype.equivFin (Fin (n' + 1) → Bool)).symm
              ⟨g.val - 2 * (n' + 1), by omega⟩) := by
            simp only [V, dif_neg h1, dif_pos h2]
          rw [hVg]
          constructor
          · intro hxv h hedge
            have hxeq := of_decide_eq_true hxv
            by_cases hh : h.val < 2 * (n' + 1)
            · simp only [accTruthTable] at hedge
              rw [dif_pos (show h.val < 2 * (n' + 1) ∧ 2 * (n' + 1) ≤ g.val ∧
                g.val < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) from ⟨hh, by omega, h2⟩)]
                  at hedge
              simp only [V, dif_pos hh]
              split at hedge
              · rename_i hodd
                rw [if_pos hodd]
                simp only [decide_eq_true_eq] at hedge
                rw [hxeq]
                simp [hedge]
              · rename_i hev
                rw [if_neg hev]
                simp only [decide_eq_true_eq] at hedge
                rw [hxeq]
                exact hedge
            · exfalso
              simp only [accTruthTable] at hedge
              rw [dif_neg (by tauto), dif_neg (by omega)] at hedge
              exact absurd hedge (by simp)
          · intro H
            simp only [decide_eq_true_eq]
            funext i
            have hi : i.val < n' + 1 := i.isLt
            by_cases hvi : (Fintype.equivFin (Fin (n' + 1) → Bool)).symm
                ⟨g.val - 2 * (n' + 1), by omega⟩ i = true
            · have hlt : 2 * i.val < (accTruthTable (n' + 1) m P dec).gateCount := by
                simp only [accTruthTable]; omega
              have hidx : (⟨2 * i.val / 2, by omega⟩ : Fin (n' + 1)) = i := by
                apply Fin.ext; change 2 * i.val / 2 = i.val; omega
              have hedge : (accTruthTable (n' + 1) m P dec).edge ⟨2 * i.val, hlt⟩ g = true := by
                simp only [accTruthTable]
                rw [dif_pos (show 2 * i.val < 2 * (n' + 1) ∧ 2 * (n' + 1) ≤ g.val ∧
                  g.val < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) from
                    ⟨by omega, by omega, h2⟩)]
                rw [if_neg (by omega)]
                simpa [hidx] using hvi
              have hVh := H ⟨2 * i.val, hlt⟩ hedge
              simp only [V, dif_pos (show (2 * i.val) < 2 * (n' + 1) by omega),
                if_neg (show ¬ (2 * i.val) % 2 = 1 by omega)] at hVh
              rw [hvi]
              rw [← hVh, hidx]
            · have hlt : 2 * i.val + 1 < (accTruthTable (n' + 1) m P dec).gateCount := by
                simp only [accTruthTable]; omega
              have hidx : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin (n' + 1)) = i := by
                apply Fin.ext; change (2 * i.val + 1) / 2 = i.val; omega
              have hedge : (accTruthTable (n' + 1) m P dec).edge ⟨2 * i.val + 1, hlt⟩ g = true := by
                simp only [accTruthTable]
                rw [dif_pos (show 2 * i.val + 1 < 2 * (n' + 1) ∧ 2 * (n' + 1) ≤ g.val ∧
                  g.val < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) from
                    ⟨by omega, by omega, h2⟩)]
                rw [if_pos (by omega)]
                simpa [hidx] using hvi
              have hVh := H ⟨2 * i.val + 1, hlt⟩ hedge
              simp only [V, dif_pos (show (2 * i.val + 1) < 2 * (n' + 1) by omega),
                if_pos (show (2 * i.val + 1) % 2 = 1 by omega)] at hVh
              simp only [Bool.not_eq_true'] at hVh
              rw [hidx] at hVh
              simp only [Bool.not_eq_true] at hvi
              rw [hvi, hVh]
        · rw [show (accTruthTable (n' + 1) m P dec).kind g = .orGate from by
            simp only [accTruthTable]; rw [dif_neg h1, dif_neg h2]]
          have hVg : V g = @decide (P x) (dec x) := by
            simp only [V, dif_neg h1, dif_neg h2]
          have hgv : g.val = 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) := by
            have hlt := g.isLt
            simp only [accTruthTable] at hlt
            omega
          rw [hVg]
          constructor
          · intro hp
            have hPx : P x := of_decide_eq_true hp
            have hex := (Fintype.equivFin (Fin (n' + 1) → Bool) x).isLt
            have hlt : 2 * (n' + 1) + (Fintype.equivFin (Fin (n' + 1) → Bool) x).val
                < (accTruthTable (n' + 1) m P dec).gateCount := by
              simp only [accTruthTable]; omega
            have hidx : (⟨2 * (n' + 1) + (Fintype.equivFin (Fin (n' + 1) → Bool) x).val
                - 2 * (n' + 1), by omega⟩ : Fin (Fintype.card (Fin (n' + 1) → Bool)))
                = Fintype.equivFin (Fin (n' + 1) → Bool) x := by
              apply Fin.ext
              change 2 * (n' + 1) + (Fintype.equivFin (Fin (n' + 1) → Bool) x).val - 2 * (n' + 1)
                = (Fintype.equivFin (Fin (n' + 1) → Bool) x).val
              omega
            have hval : (Fintype.equivFin (Fin (n' + 1) → Bool)).symm
                ⟨2 * (n' + 1) + (Fintype.equivFin (Fin (n' + 1) → Bool) x).val - 2 * (n' + 1),
                  by omega⟩ = x := by
              rw [hidx, Equiv.symm_apply_apply]
            refine ⟨⟨2 * (n' + 1) + (Fintype.equivFin (Fin (n' + 1) → Bool) x).val, hlt⟩, ?_, ?_⟩
            · simp only [accTruthTable]
              rw [dif_neg (by omega), dif_pos (show 2 * (n' + 1) ≤ 2 * (n' + 1) +
                (Fintype.equivFin (Fin (n' + 1) → Bool) x).val ∧
                2 * (n' + 1) + (Fintype.equivFin (Fin (n' + 1) → Bool) x).val
                  < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) ∧
                g.val = 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) from
                  ⟨by omega, by omega, hgv⟩)]
              cases hd : dec ((Fintype.equivFin (Fin (n' + 1) → Bool)).symm
                  ⟨2 * (n' + 1) + (Fintype.equivFin (Fin (n' + 1) → Bool) x).val - 2 * (n' + 1),
                    by omega⟩) with
              | isTrue _ => rfl
              | isFalse hno => exact absurd hPx (by rw [← hval]; exact hno)
            · simp only [V, dif_neg (show ¬ 2 * (n' + 1) +
                (Fintype.equivFin (Fin (n' + 1) → Bool) x).val < 2 * (n' + 1) by omega),
                dif_pos (show 2 * (n' + 1) + (Fintype.equivFin (Fin (n' + 1) → Bool) x).val
                  < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) by omega)]
              simp
          · rintro ⟨h, hedge, hVh⟩
            by_cases hh1 : h.val < 2 * (n' + 1)
            · exfalso
              simp only [accTruthTable] at hedge
              rw [dif_neg (by omega), dif_neg (by omega)] at hedge
              exact absurd hedge (by simp)
            · by_cases hh2 : h.val < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool)
              · simp only [accTruthTable] at hedge
                rw [dif_neg (by omega), dif_pos (show 2 * (n' + 1) ≤ h.val ∧
                  h.val < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) ∧
                  g.val = 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) from
                    ⟨by omega, hh2, hgv⟩)] at hedge
                simp only [V, dif_neg hh1, dif_pos hh2] at hVh
                have hxv : x = (Fintype.equivFin (Fin (n' + 1) → Bool)).symm
                    ⟨h.val - 2 * (n' + 1), by omega⟩ := of_decide_eq_true hVh
                cases hd : dec ((Fintype.equivFin (Fin (n' + 1) → Bool)).symm
                    ⟨h.val - 2 * (n' + 1), by omega⟩) with
                | isTrue hP => rw [hxv]; exact decide_eq_true hP
                | isFalse hno => rw [hd] at hedge; exact absurd hedge (by simp)
              · exfalso
                have hhlt := h.isLt
                simp only [accTruthTable] at hhlt
                have hhv : h.val = 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) := by omega
                simp only [accTruthTable] at hedge
                rw [dif_neg (by omega), dif_neg (by omega)] at hedge
                exact absurd hedge (by simp)
    have heq := (accValuation_iff_eq_evalACC
      (wellFormedACC_accTruthTable (n' + 1) m P dec)).mp hV
    have hout := congrFun heq (accTruthTable (n' + 1) m P dec).output
    rw [← hout]
    change V (accTruthTable (n' + 1) m P dec).output = _
    have h1 : ¬ ((accTruthTable (n' + 1) m P dec).output.val < 2 * (n' + 1)) := by
      change ¬ (2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool) < 2 * (n' + 1))
      omega
    have h2 : ¬ ((accTruthTable (n' + 1) m P dec).output.val
        < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool)) := by
      change ¬ (2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool)
        < 2 * (n' + 1) + Fintype.card (Fin (n' + 1) → Bool))
      omega
    simp only [V, dif_neg h1, dif_neg h2]


theorem accTruthTable_gateCount_zero (m : Nat) (P : (Fin 0 → Bool) → Prop)
    (dec : ∀ x, Decidable (P x)) : (accTruthTable 0 m P dec).gateCount = 1 := rfl

theorem accTruthTable_gateCount_succ (n' m : Nat) (P : (Fin (n' + 1) → Bool) → Prop)
    (dec : ∀ x, Decidable (P x)) :
    (accTruthTable (n' + 1) m P dec).gateCount = 2 * (n' + 1) + 2 ^ (n' + 1) + 1 := by
  simp [accTruthTable]

/-- **Small-`n` size bound.**  Below any fixed threshold `T` the truth-table
circuits have size `≤ (n + 1) ^ e` for one fixed exponent `e`, so they can be
used as the small-input part of a polynomial-size `ACC` family. -/
theorem accTruthTable_gateCount_le_pow (T : Nat) :
    ∃ e : Nat, ∀ (n : Nat), n < T → ∀ (m : Nat) (P : (Fin n → Bool) → Prop)
      (dec : ∀ x, Decidable (P x)), (accTruthTable n m P dec).gateCount ≤ (n + 1) ^ e := by
  refine ⟨2 * T + 2 ^ T + 1, ?_⟩
  intro n hn m P dec
  set K := 2 * T + 2 ^ T + 1 with hK
  cases n with
  | zero => simp [accTruthTable_gateCount_zero]
  | succ n' =>
      rw [accTruthTable_gateCount_succ]
      have hpow : 2 ^ (n' + 1) ≤ 2 ^ T := Nat.pow_le_pow_right (by omega) (by omega)
      have hsmall : 2 * (n' + 1) + 2 ^ (n' + 1) + 1 ≤ K + 1 := by omega
      have h2 : (2 : Nat) ^ K ≤ (n' + 1 + 1) ^ K :=
        Nat.pow_le_pow_left (by omega) K
      have h3 : K + 1 ≤ 2 ^ K := Nat.lt_two_pow_self
      omega

theorem accAccepts_accTruthTable (n m : Nat) (P : (Fin n → Bool) → Prop)
  (dec : ∀ x, Decidable (P x)) (x : Fin n → Bool) :
    ACCAccepts (accTruthTable n m P dec) x ↔ P x := by
  rw [accAccepts_iff (wellFormedACC_accTruthTable n m P dec) x,
    evalACC_accTruthTable n m P dec x, decide_eq_true_iff]

end AllenderOQ3.Internal
