import AllenderOQ3.Internal.NonCrossingCyclic

set_option autoImplicit false
set_option linter.unusedVariables false

namespace AllenderOQ3.Internal

/-
E2-b: cyclic subgroup structure.  The two statements below, as originally
written, do not typecheck: `NonCrossing w` is a `Submonoid`, so it carries
neither an integer power `HPow _ ℤ _` nor a `Group` instance (hence no
`Subgroup (NonCrossing w)`).  They are preserved verbatim here and restated
below over the unit group `(NonCrossing w)ˣ`, which is the intended object.

theorem nonCrossing_units_isCyclic (w : Nat) :
    ∃ g : NonCrossing w, ∀ h : (NonCrossing w)ˣ, ∃ k : ℤ, h.val = g ^ k := by
  sorry

theorem nonCrossing_subgroup_isCyclic (w : Nat) (H : Subgroup (NonCrossing w)) :
    ∃ g : NonCrossing w, ∀ h ∈ H, ∃ k : ℤ, h = g ^ k := by
  sorry
-/

/-- Corrected form of `nonCrossing_units_isCyclic`: the unit group of the
non-crossing submonoid is cyclic. -/
theorem nonCrossing_units_isCyclic (w : Nat) :
    ∃ g : (NonCrossing w)ˣ, ∀ h : (NonCrossing w)ˣ, ∃ k : ℤ, h = g ^ k := by
  haveI := nonCrossing_units_cyclic w
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (NonCrossing w)ˣ)
  refine ⟨g, fun h => ?_⟩
  obtain ⟨k, hk⟩ := hg h
  exact ⟨k, hk.symm⟩

/-- Corrected form of `nonCrossing_subgroup_isCyclic`: every subgroup of the
unit group of the non-crossing submonoid is cyclic. -/
theorem nonCrossing_subgroup_isCyclic (w : Nat) (H : Subgroup (NonCrossing w)ˣ) :
    ∃ g : (NonCrossing w)ˣ, ∀ h ∈ H, ∃ k : ℤ, h = g ^ k := by
  -- The generator of the whole unit group generates every element, a fortiori
  -- every element of `H`; no `Subgroup`-of-cyclic machinery is needed because
  -- the statement only requires containment in `zpowers` of a global generator.
  obtain ⟨g, hg⟩ := nonCrossing_units_isCyclic w
  exact ⟨g, fun h _ => hg h⟩

/-- Strengthened form of `nonCrossing_subgroup_isCyclic`: a generator of the
subgroup `H` can be taken *inside* `H`. -/
theorem nonCrossing_subgroup_isCyclic_strong (w : Nat) (H : Subgroup (NonCrossing w)ˣ) :
    ∃ g ∈ H, ∀ h ∈ H, ∃ k : ℤ, h = g ^ k := by
  haveI := nonCrossing_units_cyclic w
  haveI : IsCyclic H := Subgroup.isCyclic H
  obtain ⟨⟨g, hg⟩, hgen⟩ := IsCyclic.exists_generator (α := H)
  refine ⟨g, hg, fun h hh => ?_⟩
  obtain ⟨k, hk⟩ := hgen ⟨h, hh⟩
  exact ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩

end AllenderOQ3.Internal
