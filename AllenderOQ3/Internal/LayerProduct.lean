import AllenderOQ3.Internal.LayerRestriction

/-!
# The layer-product embedding of realized permutation groups

The min-layering partitions any finite set `S` of configurations into
antichain layers, and realized permutations preserve every layer
(`realizedPerm_mem_minLayer`).  Restriction to the `j`-th layer is therefore a
group homomorphism

  `resHomAt S j : realizedSubgroup S →* realizedSubgroup (minLayer S j)`,

and the combined map into the product over all layers is *injective*, because
the layers cover `S` (`perm_eq_of_forall_minLayer`).

This survives the failure of the interval route (`IntervalReduction`,
`LayerRestriction` obstruction headers): no interval structure and no rigidity
is used — only the order-automorphism property of realized permutations.

Main consequence (`realizedSubgroup_comm_of_antichains`): **if realized
permutation groups of antichains are commutative, the realized permutation
group of every `S` is commutative.**  In particular cyclicity for antichains
(`AntichainsCyclic`) already gives commutativity everywhere
(`realizedSubgroup_comm_of_antichains_cyclic`).  Commutative holonomy groups
are all the Barrington–Thérien cascade needs (`monoidWordACC_of_comm`), so
this reduction re-anchors the heart-lemma programme after the loss of the
interval route.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## Restriction to an arbitrary layer -/

/-- The underlying map of the restriction of a realized permutation to the
`j`-th antichain layer. -/
noncomputable def resFunAt {T : Finset (Config w)} {e : Equiv.Perm {x // x ∈ T}}
    (he : RealizedPerm T e) (j : Nat) (y : {y // y ∈ minLayer T j}) :
    {y // y ∈ minLayer T j} :=
  ⟨(e ⟨y.val, minLayer_subset j y.2⟩).val,
    realizedPerm_mem_minLayer he (x := ⟨y.val, minLayer_subset j y.2⟩) y.2⟩

theorem resFunAt_injective {T : Finset (Config w)} {e : Equiv.Perm {x // x ∈ T}}
    (he : RealizedPerm T e) (j : Nat) : Function.Injective (resFunAt he j) := by
  intro a b hab
  have h1 : (resFunAt he j a).val = (resFunAt he j b).val := Subtype.ext_iff.mp hab
  have h2 : e ⟨a.val, minLayer_subset j a.2⟩ = e ⟨b.val, minLayer_subset j b.2⟩ :=
    Subtype.ext h1
  have h3 := Subtype.ext_iff.mp (e.injective h2)
  exact Subtype.ext h3

/-- Restriction of a realized permutation to the `j`-th layer. -/
noncomputable def resPermAt {T : Finset (Config w)} {e : Equiv.Perm {x // x ∈ T}}
    (he : RealizedPerm T e) (j : Nat) : Equiv.Perm {y // y ∈ minLayer T j} :=
  Equiv.ofBijective (resFunAt he j)
    (Finite.injective_iff_bijective.mp (resFunAt_injective he j))

theorem resPermAt_realized {T : Finset (Config w)} {e : Equiv.Perm {x // x ∈ T}}
    (he : RealizedPerm T e) (j : Nat) :
    RealizedPerm (minLayer T j) (resPermAt he j) := by
  obtain ⟨m, hm, hr⟩ := he
  exact ⟨m, hm, fun y => hr ⟨y.val, minLayer_subset j y.2⟩⟩

/-- The restriction homomorphism to the `j`-th layer. -/
noncomputable def resHomAt (T : Finset (Config w)) (j : Nat) :
    realizedSubgroup T →* realizedSubgroup (minLayer T j) :=
  MonoidHom.mk'
    (fun φ => ⟨resPermAt (mem_realizedSubgroup.mp φ.2) j,
      mem_realizedSubgroup.mpr (resPermAt_realized _ j)⟩)
    (by
      intro a b
      apply Subtype.ext
      apply Equiv.ext
      intro y
      apply Subtype.ext
      have h1 : ((resPermAt (mem_realizedSubgroup.mp (a * b).2) j) y).val
          = ((a.1 * b.1) ⟨y.val, minLayer_subset j y.2⟩).val := rfl
      have h2 : ((a.1 * b.1) ⟨y.val, minLayer_subset j y.2⟩).val
          = (a.1 (b.1 ⟨y.val, minLayer_subset j y.2⟩)).val := rfl
      have h3 : b.1 ⟨y.val, minLayer_subset j y.2⟩
          = ⟨((resPermAt (mem_realizedSubgroup.mp b.2) j) y).val,
              minLayer_subset j ((resPermAt (mem_realizedSubgroup.mp b.2) j) y).2⟩ :=
        Subtype.ext rfl
      rw [h1, h2, h3]
      rfl)

@[simp] theorem resHomAt_apply_val (T : Finset (Config w)) (j : Nat)
    (φ : realizedSubgroup T) (y : {y // y ∈ minLayer T j}) :
    (((resHomAt T j) φ).1 y).val = (φ.1 ⟨y.val, minLayer_subset j y.2⟩).val := rfl

/-- **Joint injectivity**: an element restricting to the identity on every
layer is the identity. -/
theorem eq_one_of_forall_resHomAt {T : Finset (Config w)} {φ : realizedSubgroup T}
    (h : ∀ j : Nat, (resHomAt T j) φ = 1) : φ = 1 := by
  apply Subtype.ext
  refine perm_eq_of_forall_minLayer (f := 1) ?_
  intro j x hx
  have h1 : ((resHomAt T j) φ).1 ⟨x.val, hx⟩ = ⟨x.val, hx⟩ := by
    rw [h j]
    rfl
  have h2 := Subtype.ext_iff.mp h1
  exact Subtype.ext h2

/-! ## Commutativity descends from antichains to everything -/

/-- Realized permutation groups of antichains are commutative. -/
def AntichainsCommute (w : Nat) : Prop :=
  ∀ L : Finset (Config w), (∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) →
    ∀ a b : realizedSubgroup L, a * b = b * a

/-- Realized permutation groups of antichains are cyclic (empirically
supported by the exact certified model at `w ≤ 4`, all subset sizes ≤ 5). -/
def AntichainsCyclic (w : Nat) : Prop :=
  ∀ L : Finset (Config w), (∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) →
    IsCyclic (realizedSubgroup L)

/-- **Commutativity of all realized permutation groups follows from the
antichain case.** -/
theorem realizedSubgroup_comm_of_antichains (hcomm : AntichainsCommute w)
    (S : Finset (Config w)) (a b : realizedSubgroup S) : a * b = b * a := by
  have hkey : ∀ j : Nat, (resHomAt S j) (a * b) = (resHomAt S j) (b * a) := by
    intro j
    have hL : ∀ x ∈ minLayer S j, ∀ y ∈ minLayer S j, x ≤ y → x = y := by
      intro x hx y hy hle
      exact minLayer_antichain j hx hy hle
    have h1 : (resHomAt S j) (a * b) = (resHomAt S j) a * (resHomAt S j) b :=
      map_mul _ a b
    have h2 : (resHomAt S j) (b * a) = (resHomAt S j) b * (resHomAt S j) a :=
      map_mul _ b a
    rw [h1, h2, hcomm (minLayer S j) hL ((resHomAt S j) a) ((resHomAt S j) b)]
  have hone : ∀ j : Nat, (resHomAt S j) ((a * b) * (b * a)⁻¹) = 1 := by
    intro j
    rw [map_mul, map_inv, hkey j, mul_inv_cancel]
  have h := eq_one_of_forall_resHomAt hone
  have h2 : (a * b) * (b * a)⁻¹ * (b * a) = 1 * (b * a) := by rw [h]
  rwa [inv_mul_cancel_right, one_mul] at h2

/-- Cyclic groups are commutative, so antichain cyclicity is enough. -/
theorem antichainsCommute_of_cyclic (hcyc : AntichainsCyclic w) :
    AntichainsCommute w := by
  intro L hL a b
  haveI := hcyc L hL
  letI := IsCyclic.commGroup (α := realizedSubgroup L)
  exact mul_comm a b

/-- **The heart-lemma programme after the interval obstructions**: antichain
cyclicity gives commutativity of every realized permutation group. -/
theorem realizedSubgroup_comm_of_antichains_cyclic (hcyc : AntichainsCyclic w)
    (S : Finset (Config w)) (a b : realizedSubgroup S) : a * b = b * a :=
  realizedSubgroup_comm_of_antichains (antichainsCommute_of_cyclic hcyc) S a b

end Internal
end AllenderOQ3
