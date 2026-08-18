import AllenderOQ3.Internal.ResetWordACC

/-!
# The remaining Barrington–Thérien leaf at small width

`monoidWordACC_nonCrossing w` — the word problem of the incidence-constrained
monoid — is the last open leaf of the cylindrical simulation.  This file settles
it for `w = 0` and `w = 1`, unconditionally.

* at width `0` the transition monoid is a singleton;
* at width `1` every non-crossing map is monotone, and the only monotone maps of
  a one-bit configuration are the identity and the two constants, so
  `NonCrossing 1` *is* the reset submonoid, which is `L`-trivial
  (`monoidWordACC_resetSubmonoid`).

From width `2` on the monoid has non-trivial (cyclic) groups, so neither the
`R`-trivial nor the `L`-trivial analysis applies and the general holonomy
cascade is needed.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

/-! ## Width zero -/

instance : Subsingleton (Config 0) := by
  constructor
  intro a b
  funext i
  exact absurd i.isLt (by omega)

instance : Subsingleton (TransMonoid 0) := by
  constructor
  intro a b
  exact transMonoid_ext (fun x => Subsingleton.elim _ _)

/-- **The leaf at width zero.** -/
theorem monoidWordACC_nonCrossing_zero : MonoidWordACC (NonCrossing 0) := by
  haveI : Subsingleton (NonCrossing 0) := by
    constructor
    intro a b
    exact Subtype.ext (Subsingleton.elim _ _)
  exact monoidWordACC_of_subsingleton _

/-! ## Width one -/

/-- A one-bit configuration is constantly `false` or constantly `true`. -/
theorem config_one_cases (x : Config 1) :
    x = (fun _ => false) ∨ x = (fun _ => true) := by
  by_cases hx : x ⟨0, by omega⟩ = true
  · refine Or.inr (funext fun j => ?_)
    have hj : j = ⟨0, by omega⟩ := Subsingleton.elim _ _
    rw [hj, hx]
  · refine Or.inl (funext fun j => ?_)
    have hj : j = ⟨0, by omega⟩ := Subsingleton.elim _ _
    rw [hj]
    exact Bool.eq_false_iff.mpr hx

/-- A one-bit configuration with a `false` bit is the bottom configuration. -/
theorem config_one_eq_false {y : Config 1} (h : y ⟨0, by omega⟩ = false) :
    y = (fun _ => false) := by
  funext j
  have hj : j = ⟨0, by omega⟩ := Subsingleton.elim _ _
  rw [hj, h]

/-- A one-bit configuration with a `true` bit is the top configuration. -/
theorem config_one_eq_true {y : Config 1} (h : y ⟨0, by omega⟩ = true) :
    y = (fun _ => true) := by
  funext j
  have hj : j = ⟨0, by omega⟩ := Subsingleton.elim _ _
  rw [hj, h]

theorem config_one_bot_le_top :
    ((fun _ => false) : Config 1) ≤ (fun _ => true) := by
  intro j
  simp

/-- **Every monotone width-one transition is the identity or a reset.** -/
theorem mem_resetSubmonoid_of_monotone_one {m : TransMonoid 1}
    (hmono : Monotone (MulOpposite.unop m)) : m ∈ resetSubmonoid 1 := by
  classical
  have hrun : ∀ x : Config 1, runTrans m x = (MulOpposite.unop m) x := fun _ => rfl
  set b0 : Config 1 := runTrans m (fun _ => false) with hb0
  set b1 : Config 1 := runTrans m (fun _ => true) with hb1
  have hle : b0 ≤ b1 := by
    rw [hb0, hb1, hrun, hrun]
    exact hmono config_one_bot_le_top
  refine mem_resetSubmonoid_iff.mpr ?_
  by_cases h0 : b0 ⟨0, by omega⟩ = true
  · -- `b0` is the top configuration, hence so is `b1`
    have hb0t : b0 = (fun _ => true) := config_one_eq_true h0
    have h1 : b1 ⟨0, by omega⟩ = true := by
      have := hle ⟨0, by omega⟩
      rw [h0] at this
      exact Bool.le_iff_imp.mp this rfl
    have hb1t : b1 = (fun _ => true) := config_one_eq_true h1
    refine Or.inr ⟨fun _ => true, transMonoid_ext (fun x => ?_)⟩
    rcases config_one_cases x with rfl | rfl
    · rw [Holonomy.runTrans_constTrans, ← hb0, hb0t]
    · rw [Holonomy.runTrans_constTrans, ← hb1, hb1t]
  · have hb0f : b0 = (fun _ => false) := config_one_eq_false (Bool.eq_false_iff.mpr h0)
    by_cases h1 : b1 ⟨0, by omega⟩ = true
    · -- identity
      have hb1t : b1 = (fun _ => true) := config_one_eq_true h1
      refine Or.inl (transMonoid_ext (fun x => ?_))
      rcases config_one_cases x with rfl | rfl
      · rw [runTrans_one, ← hb0, hb0f]
      · rw [runTrans_one, ← hb1, hb1t]
    · -- constant `false`
      have hb1f : b1 = (fun _ => false) := config_one_eq_false (Bool.eq_false_iff.mpr h1)
      refine Or.inr ⟨fun _ => false, transMonoid_ext (fun x => ?_)⟩
      rcases config_one_cases x with rfl | rfl
      · rw [Holonomy.runTrans_constTrans, ← hb0, hb0f]
      · rw [Holonomy.runTrans_constTrans, ← hb1, hb1f]

/-- **At width one the incidence-constrained monoid is exactly the reset
submonoid.** -/
theorem nonCrossing_one_eq_resetSubmonoid : NonCrossing 1 = resetSubmonoid 1 := by
  refine le_antisymm ?_ resetSubmonoid_le_nonCrossing
  intro m hm
  exact mem_resetSubmonoid_of_monotone_one (monotone_of_mem_nonCrossing hm)

/-- **The leaf at width one.** -/
theorem monoidWordACC_nonCrossing_one : MonoidWordACC (NonCrossing 1) := by
  rw [nonCrossing_one_eq_resetSubmonoid]
  exact monoidWordACC_resetSubmonoid 1

end Internal
end AllenderOQ3
