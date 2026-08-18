import AllenderOQ3.Internal.NonCrossingShift

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# The unit group of the non-crossing submonoid is cyclic

Every element of `NonCrossing w` is monotone, and every *bijective* element is a
cyclic shift of coordinates (`nonCrossing_le_shiftSubmonoid`).  The underlying
configuration map of a unit is bijective, so the shift amount gives an injective
group homomorphism `(NonCrossing w)ˣ →* Multiplicative (ZMod w)`.  A group that
embeds in a cyclic group is cyclic.
-/

namespace AllenderOQ3.Internal

variable {w : Nat}

/-- The configuration map underlying a unit of `NonCrossing w` is a bijection. -/
theorem unit_unop_bijective (u : (NonCrossing w)ˣ) :
    Function.Bijective (MulOpposite.unop (u.val.val : TransMonoid w)) := by
  have h1 : (u.val.val : TransMonoid w) * (u.inv.val : TransMonoid w) = 1 :=
    congrArg Subtype.val u.val_inv
  have h2 : (u.inv.val : TransMonoid w) * (u.val.val : TransMonoid w) = 1 :=
    congrArg Subtype.val u.inv_val
  have hleft : ∀ s : Config w,
      MulOpposite.unop (u.inv.val : TransMonoid w)
        (MulOpposite.unop (u.val.val : TransMonoid w) s) = s := by
    intro s
    exact congrFun (congrArg MulOpposite.unop h1) s
  have hright : ∀ s : Config w,
      MulOpposite.unop (u.val.val : TransMonoid w)
        (MulOpposite.unop (u.inv.val : TransMonoid w) s) = s := by
    intro s
    exact congrFun (congrArg MulOpposite.unop h2) s
  exact ⟨Function.LeftInverse.injective hleft,
    fun s => ⟨MulOpposite.unop (u.inv.val : TransMonoid w) s, hright s⟩⟩

/-- The configuration map underlying a unit of `NonCrossing w` is a cyclic shift. -/
theorem unit_isShiftMap (u : (NonCrossing w)ˣ) :
    IsShiftMap w (MulOpposite.unop (u.val.val : TransMonoid w)) :=
  (nonCrossing_le_shiftSubmonoid w u.val.property).2 (unit_unop_bijective u)

/-- The shift amount of a unit of `NonCrossing w`. -/
noncomputable def unitShift (u : (NonCrossing w)ˣ) : Nat :=
  Classical.choose (unit_isShiftMap u)

theorem unitShift_spec (u : (NonCrossing w)ˣ) (s : Config w) (j : Fin w) :
    MulOpposite.unop (u.val.val : TransMonoid w) s j = s (finShift (unitShift u) j) :=
  Classical.choose_spec (unit_isShiftMap u) s j

/-- A shift amount is determined modulo `w` (for `w` positive). -/
theorem shift_amount_unique (hw : 0 < w) {f : Config w → Config w} {p q : Nat}
    (hp : ∀ s j, f s j = s (finShift p j)) (hq : ∀ s j, f s j = s (finShift q j)) :
    p % w = q % w := by
  set j0 : Fin w := ⟨0, hw⟩ with hj0
  have h1 : unitVec (finShift p j0) (finShift q j0) = true := by
    rw [← hq (unitVec (finShift p j0)) j0, hp (unitVec (finShift p j0)) j0]
    simp [unitVec]
  have h2 : finShift q j0 = finShift p j0 := by simpa [unitVec] using h1
  have hval : (finShift q j0).val = (finShift p j0).val := congrArg Fin.val h2
  simpa [finShift, hj0] using hval.symm

theorem finShift_congr {p q : Nat} (h : p % w = q % w) (j : Fin w) :
    finShift p j = finShift q j := by
  apply Fin.ext
  simp only [finShift]
  conv_lhs => rw [Nat.add_mod, h, ← Nat.add_mod]

/-- The shift amount is multiplicative. -/
theorem unitShift_mul (hw : 0 < w) (u v : (NonCrossing w)ˣ) :
    unitShift (u * v) % w = (unitShift v + unitShift u) % w := by
  refine shift_amount_unique hw (unitShift_spec (u * v)) ?_
  intro s j
  have hcomp : MulOpposite.unop ((u * v).val.val : TransMonoid w)
      = (MulOpposite.unop (v.val.val : TransMonoid w)) ∘
        (MulOpposite.unop (u.val.val : TransMonoid w)) := rfl
  rw [hcomp]
  simp only [Function.comp_apply]
  rw [unitShift_spec v, unitShift_spec u, finShift_finShift]

theorem unitShift_one (hw : 0 < w) : unitShift (1 : (NonCrossing w)ˣ) % w = 0 % w := by
  refine shift_amount_unique hw (unitShift_spec 1) ?_
  intro s j
  rw [finShift_zero]
  rfl

/-- The shift amount, as a group homomorphism into `ZMod w`. -/
noncomputable def unitShiftHom (hw : 0 < w) :
    (NonCrossing w)ˣ →* Multiplicative (ZMod w) where
  toFun u := Multiplicative.ofAdd ((unitShift u : Nat) : ZMod w)
  map_one' := by
    have h := unitShift_one (w := w) hw
    have : ((unitShift (1 : (NonCrossing w)ˣ) : Nat) : ZMod w) = ((0 : Nat) : ZMod w) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
    simp [this]
  map_mul' u v := by
    have h := unitShift_mul (w := w) hw u v
    have h2 : ((unitShift (u * v) : Nat) : ZMod w)
        = ((unitShift v + unitShift u : Nat) : ZMod w) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
    have h3 : ((unitShift (u * v) : Nat) : ZMod w)
        = ((unitShift u : Nat) : ZMod w) + ((unitShift v : Nat) : ZMod w) := by
      rw [h2, Nat.cast_add]
      ring
    simp only [← ofAdd_add]
    exact congrArg Multiplicative.ofAdd h3

theorem unitShiftHom_injective (hw : 0 < w) :
    Function.Injective (unitShiftHom (w := w) hw) := by
  intro u v huv
  have hcast : ((unitShift u : Nat) : ZMod w) = ((unitShift v : Nat) : ZMod w) :=
    congrArg Multiplicative.toAdd huv
  have hmod : unitShift u % w = unitShift v % w :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
  have hfun : MulOpposite.unop (u.val.val : TransMonoid w)
      = MulOpposite.unop (v.val.val : TransMonoid w) := by
    funext s
    funext j
    rw [unitShift_spec u, unitShift_spec v, finShift_congr hmod]
  have hval : (u.val.val : TransMonoid w) = (v.val.val : TransMonoid w) :=
    MulOpposite.unop_injective hfun
  exact Units.ext (Subtype.ext hval)

/-- **The unit group of the non-crossing submonoid is cyclic.** -/
theorem nonCrossing_units_cyclic (w : Nat) : IsCyclic (NonCrossing w)ˣ := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    have hsub : Subsingleton (Config 0) := by
      constructor
      intro a b
      funext j
      exact absurd j.isLt (by omega)
    have hsub2 : Subsingleton ((NonCrossing 0)ˣ) := by
      constructor
      intro a b
      refine Units.ext (Subtype.ext (MulOpposite.unop_injective ?_))
      funext s
      exact hsub.allEq _ _
    exact ⟨⟨1, fun h => ⟨0, by simp [hsub2.allEq 1 h]⟩⟩⟩
  · haveI : IsCyclic ((unitShiftHom (w := w) hw).range) := Subgroup.isCyclic _
    exact isCyclic_of_surjective
      (MonoidHom.ofInjective (unitShiftHom_injective hw)).symm.toMonoidHom
      (MonoidHom.ofInjective (unitShiftHom_injective hw)).symm.surjective

end AllenderOQ3.Internal
