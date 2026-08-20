import AllenderOQ3.Base

set_option autoImplicit false

/-!
# Monotone bijections of the Boolean cube

The configurations of a width-`w` layer form the Boolean cube `Fin w → Bool`.
A layer transition of an ADR circuit is built from `and`/`or` gates and
constants only, so it is a *monotone* self-map of the cube.

This file proves the one order-theoretic fact needed about such maps: a
monotone bijection of the cube is a permutation of coordinates
(`exists_coord_perm_of_monotone_bijective`).  The proof goes through the atoms
of the cube, which are the coordinate indicators `unitVec i`.
-/

namespace AllenderOQ3.Internal

variable {w : Nat}

/-- The indicator of a coordinate: the atoms of the Boolean cube. -/
def unitVec (i : Fin w) : Fin w → Bool := fun j => decide (j = i)

theorem unitVec_le_iff (i : Fin w) (t : Fin w → Bool) :
    unitVec i ≤ t ↔ t i = true := by
  constructor
  · intro h
    have h2 := h i
    simp only [unitVec, decide_true] at h2
    revert h2
    cases t i <;> simp
  · intro h j
    by_cases hj : j = i
    · subst hj; simp [unitVec, h]
    · simp [unitVec, hj]

theorem isAtom_bool_true : IsAtom (true : Bool) := by
  constructor
  · decide
  · intro b hb
    revert hb
    cases b <;> decide

theorem isAtom_unitVec (i : Fin w) : IsAtom (unitVec i) := by
  rw [Pi.isAtom_iff]
  refine ⟨i, ?_, ?_⟩
  · have h : unitVec i i = true := by simp [unitVec]
    rw [h]
    exact isAtom_bool_true
  · intro j hj
    simp [unitVec, hj]

theorem eq_unitVec_of_isAtom {a : Fin w → Bool} (ha : IsAtom a) :
    ∃ i, a = unitVec i := by
  rw [Pi.isAtom_iff] at ha
  obtain ⟨i, hi, hj⟩ := ha
  refine ⟨i, ?_⟩
  funext j
  by_cases h : j = i
  · subst h
    have hai : a j = true := by
      rcases hb : a j with _ | _
      · rw [hb] at hi
        exact absurd hi (by simp [IsAtom])
      · rfl
    simp [unitVec, hai]
  · have h2 := hj j h
    simp only [unitVec, h, decide_false]
    exact h2

theorem unitVec_injective : Function.Injective (unitVec (w := w)) := by
  intro i j h
  have h2 := congrFun h i
  simp only [unitVec, decide_eq_decide] at h2
  exact h2.mp trivial

/-- An order isomorphism of the Boolean cube permutes the coordinates. -/
theorem exists_coord_perm_of_orderIso (phi : (Fin w → Bool) ≃o (Fin w → Bool)) :
    ∃ sigma : Equiv.Perm (Fin w), ∀ s j, phi s j = s (sigma j) := by
  classical
  have hatom : ∀ i : Fin w, ∃ k, phi (unitVec i) = unitVec k := fun i =>
    eq_unitVec_of_isAtom ((phi.isAtom_iff (unitVec i)).mpr (isAtom_unitVec i))
  choose tau htau using hatom
  have hinj : Function.Injective tau := by
    intro i j h
    have h2 : phi (unitVec i) = phi (unitVec j) := by rw [htau i, htau j, h]
    exact unitVec_injective (phi.injective h2)
  let tauE : Equiv.Perm (Fin w) :=
    Equiv.ofBijective tau (Finite.injective_iff_bijective.mp hinj)
  have hkey : ∀ (s : Fin w → Bool) (i : Fin w), phi s (tau i) = s i := by
    intro s i
    have h1 : unitVec (tau i) ≤ phi s ↔ unitVec i ≤ s := by
      rw [← htau i, phi.le_iff_le]
    rw [unitVec_le_iff, unitVec_le_iff] at h1
    exact Bool.eq_iff_iff.mpr h1
  refine ⟨tauE.symm, fun s j => ?_⟩
  have h3 : tau (tauE.symm j) = j := tauE.apply_symm_apply j
  have h2 := hkey s (tauE.symm j)
  rw [h3] at h2
  exact h2

/-- A monotone bijection of a finite type has a monotone inverse as soon as
some power of it is the identity; on the Boolean cube this always happens. -/
theorem monotone_inv_of_monotone_bijective {f : (Fin w → Bool) → (Fin w → Bool)}
    (hmono : Monotone f) (hbij : Function.Bijective f) :
    Monotone (Function.surjInv hbij.2) := by
  classical
  -- some positive power of `f` is the identity
  obtain ⟨m, hm, hpow⟩ :
      ∃ m : Nat, 0 < m ∧ f^[m] = id := by
    let e : Equiv.Perm (Fin w → Bool) := Equiv.ofBijective f hbij
    refine ⟨orderOf e, orderOf_pos e, ?_⟩
    have h1 : e ^ orderOf e = 1 := pow_orderOf_eq_one e
    have h2 : ⇑(e ^ orderOf e) = f^[orderOf e] := by
      rw [Equiv.Perm.coe_pow]
      rfl
    rw [← h2, h1]
    rfl
  -- the inverse is the `(m-1)`-st power
  have hinv : Function.surjInv hbij.2 = f^[m - 1] := by
    funext y
    have h1 : f (Function.surjInv hbij.2 y) = y := Function.surjInv_eq hbij.2 y
    have h2 : f (f^[m-1] y) = y := by
      have : f^[m] y = y := by rw [hpow]; rfl
      calc f (f^[m-1] y) = f^[m-1+1] y := by
            rw [Function.iterate_succ_apply']
        _ = f^[m] y := by congr 1; omega
        _ = y := this
    exact hbij.1 (h1.trans h2.symm)
  rw [hinv]
  exact hmono.iterate _

/-- **A monotone bijection of the Boolean cube is a coordinate permutation.** -/
theorem exists_coord_perm_of_monotone_bijective {f : (Fin w → Bool) → (Fin w → Bool)}
    (hmono : Monotone f) (hbij : Function.Bijective f) :
    ∃ sigma : Equiv.Perm (Fin w), ∀ s j, f s j = s (sigma j) := by
  classical
  have hinvmono := monotone_inv_of_monotone_bijective hmono hbij
  let e : (Fin w → Bool) ≃ (Fin w → Bool) := Equiv.ofBijective f hbij
  have hsymm : ∀ y, e.symm y = Function.surjInv hbij.2 y := by
    intro y
    apply hbij.1
    rw [Function.surjInv_eq hbij.2 y]
    exact e.apply_symm_apply y
  have hle : ∀ a b : Fin w → Bool, e a ≤ e b ↔ a ≤ b := by
    intro a b
    constructor
    · intro h
      have h2 := hinvmono h
      rw [← hsymm, ← hsymm] at h2
      simpa [e] using h2
    · intro h
      exact hmono h
  let phi : (Fin w → Bool) ≃o (Fin w → Bool) := ⟨e, hle _ _⟩
  obtain ⟨sigma, hsig⟩ := exists_coord_perm_of_orderIso phi
  exact ⟨sigma, hsig⟩

end AllenderOQ3.Internal
