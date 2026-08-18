import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.ModEq
import AllenderOQ3.Internal.GeoWind

/-!
# G5: winding data for at most two members (unconditional)

With at most two members, start data always unrolls within one winding: one
point is trivial, and for two points the second target lift is placed at
`T 0 + ((t2 + w - t1) % w)` (or equal), so no geometric input is needed (distinct starts are required: with a shared
start the strict source unrolling within one period is impossible).
This validates the interface and settles the base cases.
-/

set_option autoImplicit false
set_option linter.unusedTactic false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- **G5 (open).**  Winding data is automatic for `|A| ≤ 2`. -/
theorem startWindingData_of_card_le_two (hw : 0 < w)
    (A : Finset (Config w)) (f : Config w → Config w)
    (hcard : A.card ≤ 2)
    (hinj : ∀ x ∈ A, ∀ y ∈ A, startOf hw x = startOf hw y → x = y) :
    StartWindingData hw A f := by
  intro hne
  have hpos : 0 < A.card := Finset.card_pos.mpr hne
  have hcard2 : A.card = 1 ∨ A.card = 2 := by omega
  rcases hcard2 with hc | hc
  · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
    use 1, by decide, fun _ => z, fun _ => (startOf hw z).val, fun _ => (startOf hw (f z)).val
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; subst A; simp
    · intro z' hz'; subst A; simp at hz'; subst z'; exact ⟨0, rfl⟩
    · intro i j hij; exact False.elim (by have := i.isLt; have := j.isLt; omega)
    · intro i j; change (startOf hw z).val < (startOf hw z).val + w; omega
    · intro i j _; exact Nat.le_refl _
    · intro i j; change (startOf hw (f z)).val < (startOf hw (f z)).val + w; omega
    · intro i; change (startOf hw z).val % w = _; exact Nat.mod_eq_of_lt (startOf hw z).isLt
    · intro i; change (startOf hw (f z)).val % w = _; exact Nat.mod_eq_of_lt (startOf hw (f z)).isLt
  · obtain ⟨z1, z2, hz12, hz⟩ := Finset.card_eq_two.mp hc
    let a := (startOf hw z1).val
    let b := (startOf hw z2).val
    have ha_lt : a < w := (startOf hw z1).isLt
    have hb_lt : b < w := (startOf hw z2).isLt
    have hne_ab : a ≠ b := by
      intro h
      have : z1 = z2 := hinj _ (by simp [hz]) _ (by simp [hz]) (Fin.ext h)
      exact hz12 this
    have H1 : (a + ((b + w - a) % w)) % w = b := by
      rcases Nat.lt_trichotomy a b with hab | hab | hab
      · have step1 : b + w - a = w + (b - a) := by omega
        have step2 : (w + (b - a)) % w = (b - a) % w := Nat.add_mod_left w (b - a)
        have step3 : (b - a) % w = b - a := Nat.mod_eq_of_lt (by omega)
        have step4 : (b + w - a) % w = b - a := by rw [step1, step2, step3]
        have step5 : a + (b - a) = b := by omega
        rw [step4, step5, Nat.mod_eq_of_lt hb_lt]
      · omega
      · have step1 : b + w - a < w := by omega
        have step2 : (b + w - a) % w = b + w - a := Nat.mod_eq_of_lt step1
        have step3 : a + (b + w - a) = b + w := by omega
        have step4 : (b + w) % w = b % w := Nat.add_mod_right b w
        rw [step2, step3, step4, Nat.mod_eq_of_lt hb_lt]
    have H2 : 0 < (b + w - a) % w := by
      rcases Nat.lt_trichotomy a b with hab | hab | hab
      · have step1 : b + w - a = w + (b - a) := by omega
        have step2 : (w + (b - a)) % w = (b - a) % w := Nat.add_mod_left w (b - a)
        have step3 : (b - a) % w = b - a := Nat.mod_eq_of_lt (by omega)
        rw [step1, step2, step3]
        omega
      · omega
      · have step1 : b + w - a < w := by omega
        have step2 : (b + w - a) % w = b + w - a := Nat.mod_eq_of_lt step1
        rw [step2]
        omega
    let t1 := (startOf hw (f z1)).val
    let t2 := (startOf hw (f z2)).val
    have ht1_lt : t1 < w := (startOf hw (f z1)).isLt
    have ht2_lt : t2 < w := (startOf hw (f z2)).isLt
    have H3 : (t1 + ((t2 + w - t1) % w)) % w = t2 := by
      rcases Nat.lt_trichotomy t1 t2 with ht | ht | ht
      · have step1 : t2 + w - t1 = w + (t2 - t1) := by omega
        have step2 : (w + (t2 - t1)) % w = (t2 - t1) % w := Nat.add_mod_left w (t2 - t1)
        have step3 : (t2 - t1) % w = t2 - t1 := Nat.mod_eq_of_lt (by omega)
        have step4 : (t2 + w - t1) % w = t2 - t1 := by rw [step1, step2, step3]
        have step5 : t1 + (t2 - t1) = t2 := by omega
        rw [step4, step5, Nat.mod_eq_of_lt ht2_lt]
      · have step1 : t2 + w - t1 = w := by omega
        have step2 : w % w = 0 := Nat.mod_self w
        have step3 : t1 + 0 = t1 := by omega
        rw [step1, step2, step3, ht, Nat.mod_eq_of_lt ht2_lt]
      · have step1 : t2 + w - t1 < w := by omega
        have step2 : (t2 + w - t1) % w = t2 + w - t1 := Nat.mod_eq_of_lt step1
        have step3 : t1 + (t2 + w - t1) = t2 + w := by omega
        have step4 : (t2 + w) % w = t2 % w := Nat.add_mod_right t2 w
        rw [step2, step3, step4, Nat.mod_eq_of_lt ht2_lt]
    let e : Fin 2 → Config w := fun i => if i.val = 0 then z1 else z2
    let S : Fin 2 → Nat := fun i => if i.val = 0 then a else a + ((b + w - a) % w)
    let T : Fin 2 → Nat := fun i => if i.val = 0 then t1 else t1 + ((t2 + w - t1) % w)
    use 2, by decide, e, S, T
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [e, hz]
    · intro z' hz'; simp [hz] at hz'; rcases hz' with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · intro i j hij
      have h1 : i.val < 2 := i.isLt
      have h2 : j.val < 2 := j.isLt
      have h3 : i.val = 0 ∧ j.val = 1 := by omega
      have hi : i = 0 := Fin.ext h3.1
      have hj : j = 1 := Fin.ext h3.2
      subst i j
      change a < a + ((b + w - a) % w)
      omega
    · intro i j
      have h2 : (b + w - a) % w < w := Nat.mod_lt _ hw
      have hi : i.val < 2 := i.isLt
      have hj : j.val < 2 := j.isLt
      rcases (by omega : i.val = 0 ∨ i.val = 1) with h_i | h_i
      · rcases (by omega : j.val = 0 ∨ j.val = 1) with h_j | h_j
        · have : i = 0 := Fin.ext h_i; have : j = 0 := Fin.ext h_j; subst i j
          change a < a + w; omega
        · have : i = 0 := Fin.ext h_i; have : j = 1 := Fin.ext h_j; subst i j
          change a + ((b + w - a) % w) < a + w; omega
      · rcases (by omega : j.val = 0 ∨ j.val = 1) with h_j | h_j
        · have : i = 1 := Fin.ext h_i; have : j = 0 := Fin.ext h_j; subst i j
          change a < a + ((b + w - a) % w) + w; omega
        · have : i = 1 := Fin.ext h_i; have : j = 1 := Fin.ext h_j; subst i j
          change a + ((b + w - a) % w) < a + ((b + w - a) % w) + w; omega
    · intro i j hij
      have hi : i.val < 2 := i.isLt
      have hj : j.val < 2 := j.isLt
      rcases (by omega : i.val = 0 ∨ i.val = 1) with h_i | h_i
      · rcases (by omega : j.val = 0 ∨ j.val = 1) with h_j | h_j
        · have : i = 0 := Fin.ext h_i; have : j = 0 := Fin.ext h_j; subst i j
          change t1 ≤ t1; omega
        · have : i = 0 := Fin.ext h_i; have : j = 1 := Fin.ext h_j; subst i j
          change t1 ≤ t1 + ((t2 + w - t1) % w); omega
      · rcases (by omega : j.val = 0 ∨ j.val = 1) with h_j | h_j
        · have : i = 1 := Fin.ext h_i; have : j = 0 := Fin.ext h_j; subst i j
          exact False.elim (by omega)
        · have : i = 1 := Fin.ext h_i; have : j = 1 := Fin.ext h_j; subst i j
          change t1 + ((t2 + w - t1) % w) ≤ t1 + ((t2 + w - t1) % w); omega
    · intro i j
      have h2 : (t2 + w - t1) % w < w := Nat.mod_lt _ hw
      have hi : i.val < 2 := i.isLt
      have hj : j.val < 2 := j.isLt
      rcases (by omega : i.val = 0 ∨ i.val = 1) with h_i | h_i
      · rcases (by omega : j.val = 0 ∨ j.val = 1) with h_j | h_j
        · have : i = 0 := Fin.ext h_i; have : j = 0 := Fin.ext h_j; subst i j
          change t1 < t1 + w; omega
        · have : i = 0 := Fin.ext h_i; have : j = 1 := Fin.ext h_j; subst i j
          change t1 + ((t2 + w - t1) % w) < t1 + w; omega
      · rcases (by omega : j.val = 0 ∨ j.val = 1) with h_j | h_j
        · have : i = 1 := Fin.ext h_i; have : j = 0 := Fin.ext h_j; subst i j
          change t1 < t1 + ((t2 + w - t1) % w) + w; omega
        · have : i = 1 := Fin.ext h_i; have : j = 1 := Fin.ext h_j; subst i j
          change t1 + ((t2 + w - t1) % w) < t1 + ((t2 + w - t1) % w) + w; omega
    · intro i
      have hi : i.val < 2 := i.isLt
      rcases (by omega : i.val = 0 ∨ i.val = 1) with h_i | h_i
      · have : i = 0 := Fin.ext h_i; subst i
        change a % w = (startOf hw z1).val
        exact Nat.mod_eq_of_lt ha_lt
      · have : i = 1 := Fin.ext h_i; subst i
        change (a + ((b + w - a) % w)) % w = (startOf hw z2).val
        exact H1
    · intro i
      have hi : i.val < 2 := i.isLt
      rcases (by omega : i.val = 0 ∨ i.val = 1) with h_i | h_i
      · have : i = 0 := Fin.ext h_i; subst i
        change t1 % w = (startOf hw (f z1)).val
        exact Nat.mod_eq_of_lt ht1_lt
      · have : i = 1 := Fin.ext h_i; subst i
        change (t1 + ((t2 + w - t1) % w)) % w = (startOf hw (f z2)).val
        exact H3

end Internal
end AllenderOQ3
