import AllenderOQ3.Internal.HolonomySkeleton

set_option autoImplicit false

/-!
# Realized permutations of set families — the holonomy-group interface

Second file of the E2-c assembly (docs/ASSEMBLY_DESIGN.md, section 4, item 2).
The holonomy groups of the tower act on *families* of configuration sets
(bricks); this file provides their formal home, in exact analogy with
`RealizedPerms.lean` one level down:

* `RealizedFamPerm 𝒜 e` — the permutation `e` of the family `𝒜` is implemented
  by an element of `NonCrossing w` acting by images;
* `realizedFamSubgroup 𝒜` — the realized permutations form a subgroup of
  `Equiv.Perm {A // A ∈ 𝒜}` (inverses again via the positive-power trick);
* `bijOn_of_reachEquiv` — a witness of mutual reachability acts bijectively
  (cardinalities agree, so image-onto forces injectivity on the source).

The heart lemma H2 is the statement `IsCyclic (realizedFamSubgroup 𝒜)` for
brick families (machine-verified for the enumerated monoids at `w = 2, 3`);
its proof is the localized HMV geometry (E2-b) and is not part of this file.

Everything here is `sorry`-free.
-/

namespace AllenderOQ3
namespace Internal
namespace Holonomy

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-- The permutation `e` of the family `𝒜` is realized by an element of
`NonCrossing w` acting by images. -/
def RealizedFamPerm (𝒜 : Finset (Finset (Config w)))
    (e : Equiv.Perm {A // A ∈ 𝒜}) : Prop :=
  ∃ m ∈ NonCrossing w, ∀ A : {A // A ∈ 𝒜}, (e A).val = ImageOf m A.val

theorem realizedFamPerm_one (𝒜 : Finset (Finset (Config w))) :
    RealizedFamPerm 𝒜 (1 : Equiv.Perm {A // A ∈ 𝒜}) :=
  ⟨1, Submonoid.one_mem _, fun A => (imageOf_one A.val).symm⟩

/-- Realized family permutations compose in time order. -/
theorem RealizedFamPerm.mul {𝒜 : Finset (Finset (Config w))}
    {e₁ e₂ : Equiv.Perm {A // A ∈ 𝒜}}
    (h₁ : RealizedFamPerm 𝒜 e₁) (h₂ : RealizedFamPerm 𝒜 e₂) :
    RealizedFamPerm 𝒜 (e₂ * e₁) := by
  obtain ⟨m₁, hm₁, hr₁⟩ := h₁
  obtain ⟨m₂, hm₂, hr₂⟩ := h₂
  refine ⟨m₁ * m₂, Submonoid.mul_mem _ hm₁ hm₂, fun A => ?_⟩
  have h1 : ((e₂ * e₁) A).val = (e₂ (e₁ A)).val := rfl
  rw [h1, hr₂ (e₁ A), hr₁ A, imageOf_mul]

theorem RealizedFamPerm.pow {𝒜 : Finset (Finset (Config w))}
    {e : Equiv.Perm {A // A ∈ 𝒜}} (h : RealizedFamPerm 𝒜 e) :
    ∀ j : Nat, RealizedFamPerm 𝒜 (e ^ j) := by
  intro j
  induction j with
  | zero =>
    have h0 : e ^ 0 = 1 := pow_zero e
    rw [h0]
    exact realizedFamPerm_one 𝒜
  | succ j ih =>
    have h1 : e ^ (j + 1) = e ^ j * e := pow_succ e j
    rw [h1]
    exact RealizedFamPerm.mul h ih

theorem RealizedFamPerm.inv {𝒜 : Finset (Finset (Config w))}
    {e : Equiv.Perm {A // A ∈ 𝒜}} (h : RealizedFamPerm 𝒜 e) :
    RealizedFamPerm 𝒜 e⁻¹ := by
  classical
  haveI : Nonempty (Equiv.Perm {A // A ∈ 𝒜}) := ⟨1⟩
  set K := Fintype.card (Equiv.Perm {A // A ∈ 𝒜}) with hK
  have hKpos : 0 < K := Fintype.card_pos
  have hstep : e ^ (K - 1) * e = 1 := by
    have hcard : e ^ K = 1 := pow_card_eq_one
    have hK1 : K - 1 + 1 = K := Nat.succ_pred_eq_of_pos hKpos
    calc e ^ (K - 1) * e = e ^ (K - 1 + 1) := (pow_succ e (K - 1)).symm
      _ = e ^ K := by rw [hK1]
      _ = 1 := hcard
  have h2 : e ^ (K - 1) = e⁻¹ := mul_eq_one_iff_eq_inv.mp hstep
  rw [← h2]
  exact RealizedFamPerm.pow h (K - 1)

open Classical in
/-- **The realized permutations of a family form a subgroup.**  The heart
lemma H2 is `IsCyclic (realizedFamSubgroup 𝒜)` for the brick families of the
holonomy tower. -/
noncomputable def realizedFamSubgroup (𝒜 : Finset (Finset (Config w))) :
    Subgroup (Equiv.Perm {A // A ∈ 𝒜}) where
  carrier := {e | RealizedFamPerm 𝒜 e}
  one_mem' := realizedFamPerm_one 𝒜
  mul_mem' := by
    intro a b ha hb
    exact RealizedFamPerm.mul hb ha
  inv_mem' := by
    intro a ha
    exact RealizedFamPerm.inv ha

theorem mem_realizedFamSubgroup {𝒜 : Finset (Finset (Config w))}
    {e : Equiv.Perm {A // A ∈ 𝒜}} :
    e ∈ realizedFamSubgroup 𝒜 ↔ RealizedFamPerm 𝒜 e := Iff.rfl

/-- **A witness of mutual reachability acts bijectively**: if `T = ImageOf m S`
and `S` is reachable back from `T`, then `runTrans m` is a bijection from `S`
onto `T` — cardinalities agree, so the image map is injective on `S`.  These
bijections are the groupoid edges the holonomy alignment coordinates ride
on. -/
theorem bijOn_of_reachEquiv {S T : Finset (Config w)} {m : TransMonoid w}
    (hm : m ∈ NonCrossing w) (hT : T = ImageOf m S) (hback : Reach T S) :
    Set.BijOn (runTrans m) ↑S ↑T := by
  classical
  have hcardST : S.card = T.card :=
    card_eq_of_reachEquiv ⟨⟨m, hm, hT⟩, hback⟩
  have hcardim : (S.image (runTrans m)).card = S.card := by
    have h1 : S.image (runTrans m) = T := by
      rw [hT]
      rfl
    rw [h1, hcardST]
  have hinj : Set.InjOn (runTrans m) ↑S :=
    Finset.injOn_of_card_image_eq hcardim
  refine ⟨?_, hinj, ?_⟩
  · intro x hx
    have hx' : x ∈ S := Finset.mem_coe.mp hx
    have : runTrans m x ∈ T := by
      rw [hT]
      exact Finset.mem_image_of_mem _ hx'
    exact Finset.mem_coe.mpr this
  · intro y hy
    have hy' : y ∈ T := Finset.mem_coe.mp hy
    rw [hT] at hy'
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy'
    exact ⟨x, Finset.mem_coe.mpr hx, hxy⟩

end Holonomy
end Internal
end AllenderOQ3
