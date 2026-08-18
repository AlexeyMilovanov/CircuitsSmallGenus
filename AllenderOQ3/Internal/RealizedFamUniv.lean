import AllenderOQ3.Internal.RealizedOrderIso
import AllenderOQ3.Internal.HolonomyGroups

set_option autoImplicit false

/-!
# The holonomy group of the full family is cyclic

The heart lemma H2 (`IsCyclic (realizedFamSubgroup 𝒜)`) at the top of the
holonomy tower, i.e. for the family `𝒜` of *all* sets of configurations.

A permutation of the full family that is realized by `m ∈ NonCrossing w` moves
singletons to singletons injectively, so `runTrans m` is a bijection of the
configuration space; by `isUnit_of_bijOn_univ` the element `m` is then a unit of
`NonCrossing w`.  Consequently the realized family permutations are exactly the
image of the (cyclic, `nonCrossing_units_cyclic`) unit group under the
image-action homomorphism, and a homomorphic image of a cyclic group is cyclic.

Everything here is `sorry`-free.
-/

namespace AllenderOQ3
namespace Internal
namespace Holonomy

attribute [local instance] Classical.propDecidable

variable {w : Nat}

theorem imageOf_singleton (m : TransMonoid w) (x : Config w) :
    ImageOf m {x} = {runTrans m x} := by
  simp [ImageOf]

/-- **A realized permutation of the full family comes from a unit.**  Singletons
are moved to singletons, so the implementing element is injective, hence
bijective, on configurations. -/
theorem isUnit_of_realizedFamPerm_univ
    {e : Equiv.Perm {A // A ∈ (Finset.univ : Finset (Finset (Config w)))}}
    (h : RealizedFamPerm (Finset.univ : Finset (Finset (Config w))) e) :
    ∃ u : (NonCrossing w)ˣ,
      ∀ A : {A // A ∈ (Finset.univ : Finset (Finset (Config w)))},
        (e A).val = ImageOf ((u : (NonCrossing w)ˣ) : TransMonoid w) A.val := by
  obtain ⟨m, hm, hr⟩ := h
  have hinj : Function.Injective (runTrans m) := by
    intro x y hxy
    have hx := hr ⟨{x}, Finset.mem_univ _⟩
    have hy := hr ⟨{y}, Finset.mem_univ _⟩
    rw [imageOf_singleton] at hx hy
    have heq : e ⟨{x}, Finset.mem_univ _⟩ = e ⟨{y}, Finset.mem_univ _⟩ := by
      refine Subtype.ext ?_
      rw [hx, hy, hxy]
    have h2 := e.injective heq
    have h3 : ({x} : Finset (Config w)) = {y} := congrArg Subtype.val h2
    exact Finset.singleton_injective h3
  have hbij : Function.Bijective (runTrans m) := Finite.injective_iff_bijective.mp hinj
  have hb : Set.BijOn (runTrans m) ↑(Finset.univ : Finset (Config w))
      ↑(Finset.univ : Finset (Config w)) := by
    refine ⟨fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _), fun a _ b _ hab => hinj hab, ?_⟩
    intro y _
    obtain ⟨x, hx⟩ := hbij.2 y
    exact ⟨x, Finset.mem_coe.mpr (Finset.mem_univ _), hx⟩
  obtain ⟨u, hu⟩ := isUnit_of_bijOn_univ hm hb
  refine ⟨u, fun A => ?_⟩
  have hval : ((u : (NonCrossing w)ˣ) : TransMonoid w) = m := by rw [hu]
  rw [hval]
  exact hr A

/-- The permutation of the family of *all* configuration sets induced by a unit
of `NonCrossing w`, through its inverse (so that the assignment is
multiplicative). -/
noncomputable def unitFamPerm (u : (NonCrossing w)ˣ) :
    Equiv.Perm {A // A ∈ (Finset.univ : Finset (Finset (Config w)))} where
  toFun A := ⟨ImageOf ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) A.val, Finset.mem_univ _⟩
  invFun A := ⟨ImageOf ((u : (NonCrossing w)ˣ) : TransMonoid w) A.val, Finset.mem_univ _⟩
  left_inv A := by
    refine Subtype.ext ?_
    change ImageOf ((u : (NonCrossing w)ˣ) : TransMonoid w)
      (ImageOf ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) A.val) = A.val
    rw [← imageOf_mul]
    have hmul : ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) *
        ((u : (NonCrossing w)ˣ) : TransMonoid w) = 1 := by
      rw [← Submonoid.coe_mul, u.inv_mul, OneMemClass.coe_one]
    rw [hmul, imageOf_one]
  right_inv A := by
    refine Subtype.ext ?_
    change ImageOf ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w)
      (ImageOf ((u : (NonCrossing w)ˣ) : TransMonoid w) A.val) = A.val
    rw [← imageOf_mul]
    have hmul : ((u : (NonCrossing w)ˣ) : TransMonoid w) *
        ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) = 1 := by
      rw [← Submonoid.coe_mul, u.mul_inv, OneMemClass.coe_one]
    rw [hmul, imageOf_one]

@[simp] theorem unitFamPerm_apply (u : (NonCrossing w)ˣ)
    (A : {A // A ∈ (Finset.univ : Finset (Finset (Config w)))}) :
    (unitFamPerm u A).val = ImageOf ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) A.val := rfl

/-- `unitFamPerm` as a group homomorphism. -/
noncomputable def unitFamPermHom :
    (NonCrossing w)ˣ →* Equiv.Perm {A // A ∈ (Finset.univ : Finset (Finset (Config w)))} where
  toFun := unitFamPerm
  map_one' := by
    refine Equiv.ext (fun A => Subtype.ext ?_)
    rw [unitFamPerm_apply]
    simp [imageOf_one]
  map_mul' u v := by
    refine Equiv.ext (fun A => Subtype.ext ?_)
    rw [unitFamPerm_apply]
    have hinv : ((u * v)⁻¹ : (NonCrossing w)ˣ) = v⁻¹ * u⁻¹ := mul_inv_rev u v
    rw [hinv]
    have hcoe : ((v⁻¹ * u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) =
        ((v⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) *
          ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) := by
      simp
    rw [hcoe, imageOf_mul]
    rfl

/-- **The realized permutations of the full family are exactly the image
actions of units of `NonCrossing w`.** -/
theorem realizedFamSubgroup_univ_eq_range :
    realizedFamSubgroup (Finset.univ : Finset (Finset (Config w)))
      = (unitFamPermHom (w := w)).range := by
  ext e
  constructor
  · intro he
    obtain ⟨u, hu⟩ := isUnit_of_realizedFamPerm_univ (mem_realizedFamSubgroup.mp he)
    refine ⟨u⁻¹, ?_⟩
    refine Equiv.ext (fun A => Subtype.ext ?_)
    change (unitFamPerm u⁻¹ A).val = (e A).val
    rw [unitFamPerm_apply, hu A, inv_inv]
  · rintro ⟨u, rfl⟩
    refine mem_realizedFamSubgroup.mpr
      ⟨((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w), ?_, fun A => rfl⟩
    exact ((u⁻¹ : (NonCrossing w)ˣ) : NonCrossing w).2

/-- **The heart lemma H2 for the full family of configuration sets.** -/
theorem isCyclic_realizedFamSubgroup_univ :
    IsCyclic (realizedFamSubgroup (Finset.univ : Finset (Finset (Config w)))) := by
  haveI := nonCrossing_units_cyclic w
  rw [realizedFamSubgroup_univ_eq_range]
  exact isCyclic_of_surjective (unitFamPermHom (w := w)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

end Holonomy
end Internal
end AllenderOQ3
