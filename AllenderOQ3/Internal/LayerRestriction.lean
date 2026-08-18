import AllenderOQ3.Internal.RealizedOrderIso

/-!
# Restriction of realized permutations to the minimal layer — **OBSTRUCTED**

The second stage of the localized HMV analysis: the realized permutation group
of a set `T` embeds, by restriction, into the realized permutation group of
the minimal antichain layer of `T`, *provided* `T` is layer-rigid
(`LayerRigid T`: a realized permutation fixing the minimal layer pointwise is
the identity — HMV's "`f` is completely described by its restriction to
`\mathcal I_1`").  `isCyclic_realizedSubgroup_of_layer` is `sorry`-free and
remains valid as a per-`T` implication.

**However, layer rigidity FAILS for `NonCrossing w` from `w = 4` on**
(2026-08-17, exact certified-layer model, `docs/EXACT_MODEL_NOTES.md`): on
`T = {0001, 0111, 1011, 1101}` — a family of interval configurations with
minimal layer `{0001}` — the exact monoid realizes both three-cycles of the
upper layer `{0111, 1011, 1101}` fixing `0001`, so two distinct realized
permutations agree on the minimal layer.  (The realized group there is still
cyclic, `Z₃`.)  HMV's Proposition 13 rigidity argument does not localize to
our monoid; the file is kept as the precise record of the failure point.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-- **Layer rigidity**: a realized permutation of `T` fixing the minimal layer
pointwise is the identity. -/
def LayerRigid (T : Finset (Config w)) : Prop :=
  ∀ e : Equiv.Perm {x // x ∈ T}, RealizedPerm T e →
    (∀ x : {x // x ∈ T}, x.val ∈ minLayer T 0 → e x = x) → e = 1

/-! ## The restriction homomorphism -/

/-- The underlying map of the restriction of a realized permutation to the
minimal layer. -/
noncomputable def resFun {T : Finset (Config w)} {e : Equiv.Perm {x // x ∈ T}}
    (he : RealizedPerm T e) (y : {y // y ∈ minLayer T 0}) :
    {y // y ∈ minLayer T 0} :=
  ⟨(e ⟨y.val, minLayer_subset 0 y.2⟩).val,
    realizedPerm_mem_minLayer he (x := ⟨y.val, minLayer_subset 0 y.2⟩) y.2⟩

theorem resFun_injective {T : Finset (Config w)} {e : Equiv.Perm {x // x ∈ T}}
    (he : RealizedPerm T e) : Function.Injective (resFun he) := by
  intro a b hab
  have h1 : (resFun he a).val = (resFun he b).val := Subtype.ext_iff.mp hab
  have h2 : e ⟨a.val, minLayer_subset 0 a.2⟩ = e ⟨b.val, minLayer_subset 0 b.2⟩ :=
    Subtype.ext h1
  have h3 := Subtype.ext_iff.mp (e.injective h2)
  exact Subtype.ext h3

/-- The restriction of a realized permutation of `T` to the minimal layer, as a
permutation of the layer. -/
noncomputable def resPerm {T : Finset (Config w)} {e : Equiv.Perm {x // x ∈ T}}
    (he : RealizedPerm T e) : Equiv.Perm {y // y ∈ minLayer T 0} :=
  Equiv.ofBijective (resFun he)
    (Finite.injective_iff_bijective.mp (resFun_injective he))

@[simp] theorem resPerm_apply {T : Finset (Config w)} {e : Equiv.Perm {x // x ∈ T}}
    (he : RealizedPerm T e) (y : {y // y ∈ minLayer T 0}) :
    ((resPerm he) y).val = (e ⟨y.val, minLayer_subset 0 y.2⟩).val := rfl

/-- The restriction is realized on the layer (by the same monoid element). -/
theorem resPerm_realized {T : Finset (Config w)} {e : Equiv.Perm {x // x ∈ T}}
    (he : RealizedPerm T e) : RealizedPerm (minLayer T 0) (resPerm he) := by
  obtain ⟨m, hm, hr⟩ := he
  exact ⟨m, hm, fun y => hr ⟨y.val, minLayer_subset 0 y.2⟩⟩

/-- The restriction homomorphism from the realized subgroup of `T` into the
realized subgroup of its minimal layer. -/
noncomputable def resHom (T : Finset (Config w)) :
    realizedSubgroup T →* realizedSubgroup (minLayer T 0) :=
  MonoidHom.mk'
    (fun φ => ⟨resPerm (mem_realizedSubgroup.mp φ.2),
      mem_realizedSubgroup.mpr (resPerm_realized _)⟩)
    (by
      intro a b
      apply Subtype.ext
      apply Equiv.ext
      intro y
      apply Subtype.ext
      have h1 : ((resPerm (mem_realizedSubgroup.mp (a * b).2)) y).val
          = ((a.1 * b.1) ⟨y.val, minLayer_subset 0 y.2⟩).val := rfl
      have h2 : ((a.1 * b.1) ⟨y.val, minLayer_subset 0 y.2⟩).val
          = (a.1 (b.1 ⟨y.val, minLayer_subset 0 y.2⟩)).val := rfl
      have h3 : b.1 ⟨y.val, minLayer_subset 0 y.2⟩
          = ⟨((resPerm (mem_realizedSubgroup.mp b.2)) y).val,
              minLayer_subset 0 ((resPerm (mem_realizedSubgroup.mp b.2)) y).2⟩ :=
        Subtype.ext rfl
      rw [h1, h2, h3]
      rfl)

/-- **Rigidity makes the restriction injective.** -/
theorem resHom_injective {T : Finset (Config w)} (hrig : LayerRigid T) :
    Function.Injective (resHom T) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  apply Subtype.ext
  apply hrig φ.1 (mem_realizedSubgroup.mp φ.2)
  intro x hx
  have h1 : ((resHom T) φ).1 ⟨x.val, hx⟩ = ⟨x.val, hx⟩ := by
    rw [hφ]
    rfl
  have h2 := Subtype.ext_iff.mp h1
  exact Subtype.ext h2

/-! ## H1 from the layer and rigidity -/

/-- **H1 for `T` follows from H1 for its minimal layer plus rigidity.** -/
theorem isCyclic_realizedSubgroup_of_layer (T : Finset (Config w))
    (hlayer : IsCyclic (realizedSubgroup (minLayer T 0)))
    (hrig : LayerRigid T) : IsCyclic (realizedSubgroup T) := by
  haveI := hlayer
  haveI h1 : IsCyclic ((resHom T).range) := Subgroup.isCyclic _
  have hinj := resHom_injective hrig
  exact isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom
    (MonoidHom.ofInjective hinj).symm.surjective

end Internal
end AllenderOQ3
