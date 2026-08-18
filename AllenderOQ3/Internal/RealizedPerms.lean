import AllenderOQ3.Internal.LocalizedCyclicity

set_option autoImplicit false

/-!
# The realized-permutation subgroup of a set of configurations

The heart lemma H1 (docs/HMV_ALGEBRA_NOTES.md, section 4; machine-verified for
the fully enumerated monoids at `w = 2, 3`) says: for every finite set `S` of
configurations, the permutations of `S` realized by elements of `NonCrossing w`
form a *cyclic* group.

This file pins the formal interface.  `RealizedPerm S e` says the permutation
`e` of the subtype `{x // x ∈ S}` is implemented by some element of
`NonCrossing w`; `realizedSubgroup S` packages the realized permutations as a
subgroup of `Equiv.Perm {x // x ∈ S}` — closure under inverses is where
finiteness enters (the inverse is a positive power of the element, realized by
the corresponding power of the implementing monoid element).  The heart lemma
then reads `IsCyclic (realizedSubgroup S)`; everything in this file is proved,
the cyclicity itself is the remaining geometric content (HMV L9–L11 for
generators plus composition).

Everything here is `sorry`-free.
-/

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- The permutation `e` of `S` is realized by an element of `NonCrossing w`. -/
def RealizedPerm (S : Finset (Config w)) (e : Equiv.Perm {x // x ∈ S}) : Prop :=
  ∃ m ∈ NonCrossing w, ∀ x : {x // x ∈ S}, (e x).val = runTrans m x.val

theorem realizedPerm_one (S : Finset (Config w)) :
    RealizedPerm S (1 : Equiv.Perm {x // x ∈ S}) :=
  ⟨1, Submonoid.one_mem _, fun _ => rfl⟩

/-- Realized permutations compose: first `e₁` (via `m₁`), then `e₂` (via `m₂`)
realizes `e₂ * e₁` via the time-ordered product `m₁ * m₂`. -/
theorem RealizedPerm.mul {S : Finset (Config w)} {e₁ e₂ : Equiv.Perm {x // x ∈ S}}
    (h₁ : RealizedPerm S e₁) (h₂ : RealizedPerm S e₂) :
    RealizedPerm S (e₂ * e₁) := by
  obtain ⟨m₁, hm₁, hr₁⟩ := h₁
  obtain ⟨m₂, hm₂, hr₂⟩ := h₂
  refine ⟨m₁ * m₂, Submonoid.mul_mem _ hm₁ hm₂, fun x => ?_⟩
  have h1 : ((e₂ * e₁) x).val = (e₂ (e₁ x)).val := rfl
  rw [h1, hr₂ (e₁ x), hr₁ x, runTrans_mul]

/-- Realized permutations are closed under powers. -/
theorem RealizedPerm.pow {S : Finset (Config w)} {e : Equiv.Perm {x // x ∈ S}}
    (h : RealizedPerm S e) : ∀ j : Nat, RealizedPerm S (e ^ j) := by
  intro j
  induction j with
  | zero =>
    have h0 : e ^ 0 = 1 := pow_zero e
    rw [h0]
    exact realizedPerm_one S
  | succ j ih =>
    have h1 : e ^ (j + 1) = e ^ j * e := pow_succ e j
    rw [h1]
    exact RealizedPerm.mul h ih

/-- **Closure under inverses.**  The inverse of a realized permutation is
realized: `e⁻¹` is the `(K-1)`-st power of `e` where `K` is the cardinality of
the ambient permutation group (`pow_card_eq_one`), so it is realized by the
corresponding power of the implementing element.  This is where finiteness
substitutes for the missing monoid inverses. -/
theorem RealizedPerm.inv {S : Finset (Config w)} {e : Equiv.Perm {x // x ∈ S}}
    (h : RealizedPerm S e) : RealizedPerm S e⁻¹ := by
  classical
  haveI : Nonempty (Equiv.Perm {x // x ∈ S}) := ⟨1⟩
  set K := Fintype.card (Equiv.Perm {x // x ∈ S}) with hK
  have hKpos : 0 < K := Fintype.card_pos
  have hstep : e ^ (K - 1) * e = 1 := by
    have hcard : e ^ K = 1 := pow_card_eq_one
    have hK1 : K - 1 + 1 = K := Nat.succ_pred_eq_of_pos hKpos
    calc e ^ (K - 1) * e = e ^ (K - 1 + 1) := (pow_succ e (K - 1)).symm
      _ = e ^ K := by rw [hK1]
      _ = 1 := hcard
  have h2 : e ^ (K - 1) = e⁻¹ := mul_eq_one_iff_eq_inv.mp hstep
  rw [← h2]
  exact RealizedPerm.pow h (K - 1)

open Classical in
/-- **The realized permutations of `S` form a subgroup of `Perm S`.**  The
heart lemma H1 is the statement `IsCyclic (realizedSubgroup S)`. -/
noncomputable def realizedSubgroup (S : Finset (Config w)) :
    Subgroup (Equiv.Perm {x // x ∈ S}) where
  carrier := {e | RealizedPerm S e}
  one_mem' := realizedPerm_one S
  mul_mem' := by
    intro a b ha hb
    exact RealizedPerm.mul hb ha
  inv_mem' := by
    intro a ha
    exact RealizedPerm.inv ha

theorem mem_realizedSubgroup {S : Finset (Config w)} {e : Equiv.Perm {x // x ∈ S}} :
    e ∈ realizedSubgroup S ↔ RealizedPerm S e := Iff.rfl

/-- A realized permutation is implemented by a monoid element that self-bijects
`S`. -/
theorem bijOn_of_realizedPerm {S : Finset (Config w)} {e : Equiv.Perm {x // x ∈ S}}
    (h : RealizedPerm S e) :
    ∃ m ∈ NonCrossing w, Set.BijOn (runTrans m) ↑S ↑S ∧
      ∀ x : {x // x ∈ S}, (e x).val = runTrans m x.val := by
  obtain ⟨m, hm, hr⟩ := h
  refine ⟨m, hm, ⟨?_, ?_, ?_⟩, hr⟩
  · intro x hx
    have hx' : x ∈ S := Finset.mem_coe.mp hx
    have := hr ⟨x, hx'⟩
    rw [← this]
    exact Finset.mem_coe.mpr (e ⟨x, hx'⟩).2
  · intro a ha b hb hab
    have ha' : a ∈ S := Finset.mem_coe.mp ha
    have hb' : b ∈ S := Finset.mem_coe.mp hb
    have hea : (e ⟨a, ha'⟩).val = runTrans m a := hr ⟨a, ha'⟩
    have heb : (e ⟨b, hb'⟩).val = runTrans m b := hr ⟨b, hb'⟩
    have : e ⟨a, ha'⟩ = e ⟨b, hb'⟩ := by
      apply Subtype.ext
      rw [hea, heb, hab]
    have h2 : (⟨a, ha'⟩ : {x // x ∈ S}) = ⟨b, hb'⟩ := e.injective this
    exact congrArg Subtype.val h2
  · intro y hy
    have hy' : y ∈ S := Finset.mem_coe.mp hy
    refine ⟨(e.symm ⟨y, hy'⟩).val, Finset.mem_coe.mpr (e.symm ⟨y, hy'⟩).2, ?_⟩
    have := hr (e.symm ⟨y, hy'⟩)
    rw [← this, Equiv.apply_symm_apply]

/-- **Realized permutations respect the min-layering**: the implementing
element permutes every antichain layer of `S`, so `e` maps the members of
`minLayer S j` to members of `minLayer S j`. -/
theorem realizedPerm_mem_minLayer {S : Finset (Config w)} {e : Equiv.Perm {x // x ∈ S}}
    (h : RealizedPerm S e) {j : Nat} {x : {x // x ∈ S}}
    (hx : x.val ∈ minLayer S j) : (e x).val ∈ minLayer S j := by
  obtain ⟨m, hm, hb, hr⟩ := bijOn_of_realizedPerm h
  have hmono : Monotone (runTrans m) := monotone_of_mem_nonCrossing hm
  have hlayer := (bijOn_layerRest hmono hb j).2
  have hmem : runTrans m x.val ∈ ↑(minLayer S j) :=
    hlayer.mapsTo (Finset.mem_coe.mpr hx)
  rw [hr x]
  exact Finset.mem_coe.mp hmem

/-- **Determinacy reduction**: two permutations of `S` that agree on every
antichain layer of the min-layering are equal — the layers cover `S`
(`exists_mem_minLayer`).  Together with `realizedPerm_mem_minLayer` this
reduces the heart lemma H1 to the geometric statements about the layer
actions: it suffices to control realized permutations layer by layer. -/
theorem perm_eq_of_forall_minLayer {S : Finset (Config w)}
    {e f : Equiv.Perm {x // x ∈ S}}
    (h : ∀ (j : Nat) (x : {x // x ∈ S}), x.val ∈ minLayer S j → e x = f x) :
    e = f := by
  apply Equiv.ext
  intro x
  obtain ⟨j, _, hj⟩ := exists_mem_minLayer x.2
  exact h j x hj

/- The former heart lemma H1 (`isCyclic_realizedSubgroup`) is RETIRED
(2026-08-18): the local-divisor route (`docs/LOCAL_DIVISOR_PLAN.md`) needs
only the abelianness of the local groups of `NonCrossing w`
(`localUnitsCommute_nonCrossing` in `LocalDivisorRoute.lean`), not cyclicity
of arbitrary stabilizer restrictions.  The `realizedSubgroup` machinery of
this file remains in use through `LayerProduct.lean`. -/

end Internal
end AllenderOQ3
