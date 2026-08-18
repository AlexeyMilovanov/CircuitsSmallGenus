import AllenderOQ3.Internal.NonCrossing

set_option autoImplicit false

open AllenderOQ3.Internal

/-- Conditional form: if the unit group of `NonCrossing w` is cyclic, then so is
every subgroup of it, with a generator taken *inside* the subgroup. -/
theorem nonCrossing_subgroup_isCyclic_from_units (w : Nat) (H : Subgroup (NonCrossing w)ˣ)
    (h_units : ∃ g : (NonCrossing w)ˣ, ∀ h : (NonCrossing w)ˣ, ∃ k : ℤ, h = g ^ k) :
    ∃ g ∈ H, ∀ h ∈ H, ∃ k : ℤ, h = g ^ k := by
  haveI : IsCyclic (NonCrossing w)ˣ := by
    obtain ⟨g, hg⟩ := h_units
    refine ⟨⟨g, fun h => ?_⟩⟩
    obtain ⟨k, hk⟩ := hg h
    exact ⟨k, hk.symm⟩
  haveI : IsCyclic H := Subgroup.isCyclic H
  obtain ⟨⟨g, hg⟩, hgen⟩ := IsCyclic.exists_generator (α := H)
  refine ⟨g, hg, fun h hh => ?_⟩
  obtain ⟨k, hk⟩ := hgen ⟨h, hh⟩
  refine ⟨k, ?_⟩
  have hval := congrArg Subtype.val hk
  simpa using hval.symm
