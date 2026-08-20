import AllenderOQ3.Base

set_option autoImplicit false
set_option linter.style.induction false

namespace AllenderOQ3.Internal

theorem edge_layer_lt {n} {c : ADRCircuit n} (hc : WellFormedADR c)
    {u v : Fin c.gateCount} (h : c.edge u v = true) : c.layer u < c.layer v := by
  have h1 := hc.1 u v h
  omega

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem adrValuation_unique {n} {c : ADRCircuit n} (hc : WellFormedADR c)
    {x : Fin n → Bool} {v₁ v₂ : Fin c.gateCount → Bool}
    (h₁ : ADRValuation c x v₁) (h₂ : ADRValuation c x v₂) : v₁ = v₂ := by
  funext g
  have H_ind : ∀ l g, c.layer g = l → v₁ g = v₂ g := by
    intro l
    induction' l using Nat.strong_induction_on with l ih
    intro g h_layer
    have eq1 := h₁ g
    have eq2 := h₂ g
    cases hk : c.kind g
    · rename_i i b
      simp only [hk] at eq1 eq2
      rw [eq1, eq2]
    · simp only [hk] at eq1 eq2
      apply bool_eq_of_iff
      constructor
      · intro hv1
        rw [eq1] at hv1
        rw [eq2]
        intro h he
        have hlt := edge_layer_lt hc he
        rw [← ih (c.layer h) (by omega) h rfl]
        exact hv1 h he
      · intro hv2
        rw [eq2] at hv2
        rw [eq1]
        intro h he
        have hlt := edge_layer_lt hc he
        rw [ih (c.layer h) (by omega) h rfl]
        exact hv2 h he
    · simp only [hk] at eq1 eq2
      apply bool_eq_of_iff
      constructor
      · intro hv1
        rw [eq1] at hv1
        rcases hv1 with ⟨h, he, hvh⟩
        rw [eq2]
        use h
        refine ⟨he, ?_⟩
        have hlt := edge_layer_lt hc he
        rw [← ih (c.layer h) (by omega) h rfl]
        exact hvh
      · intro hv2
        rw [eq2] at hv2
        rcases hv2 with ⟨h, he, hvh⟩
        rw [eq1]
        use h
        refine ⟨he, ?_⟩
        have hlt := edge_layer_lt hc he
        rw [ih (c.layer h) (by omega) h rfl]
        exact hvh
  exact H_ind (c.layer g) g rfl

open Classical in
theorem adrValuation_exists_below {n} (c : ADRCircuit n) (hc : WellFormedADR c)
    (x : Fin n → Bool) (L : Nat) :
    ∃ v : Fin c.gateCount → Bool, ∀ g, c.layer g < L →
      (match c.kind g with
       | .literal i b => v g = (if b then !(x i) else x i)
       | .andGate => (v g = true ↔ ∀ h, c.edge h g = true → v h = true)
       | .orGate  => (v g = true ↔ ∃ h, c.edge h g = true ∧ v h = true)) := by
  induction' L with L ih
  · use fun _ => false
    intro g hg
    omega
  · rcases ih with ⟨v_old, h_old⟩
    let v_new : Fin c.gateCount → Bool := fun g => if c.layer g = L then
      match c.kind g with
      | .literal i b => (if b then !(x i) else x i)
      | .andGate => decide (∀ h, c.edge h g = true → v_old h = true)
      | .orGate  => decide (∃ h, c.edge h g = true ∧ v_old h = true)
      else v_old g
    use v_new
    intro g hg
    have heqv : ∀ h, c.edge h g = true → v_new h = v_old h := by
      intro h he
      have h_layer_h := edge_layer_lt hc he
      have h_neq_h : c.layer h ≠ L := by omega
      simp [v_new, h_neq_h]
    have h_cases : c.layer g < L ∨ c.layer g = L := by omega
    rcases h_cases with h_lt | h_eq
    · have h_neq : c.layer g ≠ L := by omega
      have hv : v_new g = v_old g := by simp [v_new, h_neq]
      have step := h_old g h_lt
      cases hk : c.kind g
      · simp only [hk] at step ⊢
        rw [hv, step]
      · simp only [hk] at step ⊢
        rw [hv]
        apply Iff.intro
        · intro h1 h he
          rw [heqv h he]
          exact step.mp h1 h he
        · intro h1
          apply step.mpr
          intro h he
          rw [← heqv h he]
          exact h1 h he
      · simp only [hk] at step ⊢
        rw [hv]
        apply Iff.intro
        · intro h1
          rcases step.mp h1 with ⟨h, he, hvh⟩
          use h
          refine ⟨he, ?_⟩
          rw [heqv h he]
          exact hvh
        · intro h1
          rcases h1 with ⟨h, he, hvh⟩
          apply step.mpr
          use h
          refine ⟨he, ?_⟩
          rw [← heqv h he]
          exact hvh
    · have hv : v_new g = match c.kind g with
          | .literal i b => (if b then !(x i) else x i)
          | .andGate => decide (∀ h, c.edge h g = true → v_old h = true)
          | .orGate  => decide (∃ h, c.edge h g = true ∧ v_old h = true) := by simp [v_new, h_eq]
      cases hk : c.kind g
      · simp only [hk] at hv ⊢
        rw [hv]
      · simp only [hk] at hv ⊢
        rw [hv]
        simp only [decide_eq_true_eq]
        apply Iff.intro
        · intro h1 h he
          rw [heqv h he]
          exact h1 h he
        · intro h1 h he
          rw [← heqv h he]
          exact h1 h he
      · simp only [hk] at hv ⊢
        rw [hv]
        simp only [decide_eq_true_eq]
        apply Iff.intro
        · intro h1
          rcases h1 with ⟨h, he, hvh⟩
          use h
          refine ⟨he, ?_⟩
          rw [heqv h he]
          exact hvh
        · intro h1
          rcases h1 with ⟨h, he, hvh⟩
          use h
          refine ⟨he, ?_⟩
          rw [← heqv h he]
          exact hvh

theorem adrValuation_exists {n} (c : ADRCircuit n) (hc : WellFormedADR c)
    (x : Fin n → Bool) : ∃ v : Fin c.gateCount → Bool, ADRValuation c x v := by
  have H := adrValuation_exists_below c hc x (Finset.univ.sup c.layer + 1)
  rcases H with ⟨v, hv⟩
  use v
  intro g
  have hlt : c.layer g < Finset.univ.sup c.layer + 1 := by
    have hle := Finset.le_sup (f := c.layer) (Finset.mem_univ g)
    omega
  exact hv g hlt

open Classical in
noncomputable def evalADR {n} (c : ADRCircuit n) (hc : WellFormedADR c)
    (x : Fin n → Bool) : Fin c.gateCount → Bool :=
  Classical.choose (adrValuation_exists c hc x)

theorem adrValuation_iff_eq_evalADR {n} {c : ADRCircuit n} (hc : WellFormedADR c)
    {x : Fin n → Bool} {v : Fin c.gateCount → Bool} :
    ADRValuation c x v ↔ v = evalADR c hc x := by
  constructor
  · intro hv
    have h_eval := Classical.choose_spec (adrValuation_exists c hc x)
    exact adrValuation_unique hc hv h_eval
  · intro heq
    rw [heq]
    exact Classical.choose_spec (adrValuation_exists c hc x)

theorem adrAccepts_iff {n} {c : ADRCircuit n} (hc : WellFormedADR c)
    (x : Fin n → Bool) : ADRAccepts c x ↔ evalADR c hc x c.output = true := by
  unfold ADRAccepts
  constructor
  · intro ⟨v, hv, hout⟩
    have heq := (adrValuation_iff_eq_evalADR hc).mp hv
    rw [heq] at hout
    exact hout
  · intro hout
    use evalADR c hc x
    refine ⟨Classical.choose_spec (adrValuation_exists c hc x), hout⟩

end AllenderOQ3.Internal
