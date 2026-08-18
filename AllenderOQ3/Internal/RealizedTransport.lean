import AllenderOQ3.Internal.RealizedFamUniv

set_option autoImplicit false

/-!
# Transporting the heart lemma along mutual reachability

H1 (`IsCyclic (realizedSubgroup S)`) only depends on the mutual-reachability
class of `S`.  If `T` is the image of `S` under `m ∈ NonCrossing w` and `S` is
the image of `T` under `m' ∈ NonCrossing w`, then `runTrans m` is a bijection
`S → T` and `runTrans m'` a bijection `T → S` (`bijOn_of_reachEquiv`), and
conjugation by the first one carries the realized permutations of `S` *onto*
those of `T`.

The subtlety is that the two bijections are not inverse to each other: their
composite is a permutation `β` of `T`, itself realized (by `m' * m`).  The
sandwich `σ ∘ g ∘ τ` is therefore `conj(g) * β` rather than `conj(g)`, and
`conj(g)` is recovered as `(σ ∘ g ∘ τ) * β⁻¹`, which lies in the (subgroup of)
realized permutations of `T`.  Surjectivity follows because `conj` composed with
the reverse transport is conjugation by `β`, an inner automorphism of the
realized group of `T`.

So H1 has to be proved for only one representative of each mutual-reachability
class.  (Note this gives nothing new at the top: a set mutually reachable with
the full configuration set has the same cardinality, hence *is* the full set.)

Everything here is `sorry`-free.
-/

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

section Transport

variable {S T : Finset (Config w)} {m m' : TransMonoid w}

/-- The bijection of subtypes induced by a transition mapping `S` bijectively
onto `T`. -/
noncomputable def bijEquiv (hb : Set.BijOn (runTrans m) ↑S ↑T) :
    {x // x ∈ S} ≃ {x // x ∈ T} :=
  Equiv.ofBijective
    (fun x => ⟨runTrans m x.val, Finset.mem_coe.mp (hb.mapsTo (Finset.mem_coe.mpr x.2))⟩)
    (by
      constructor
      · intro a b hab
        have h : runTrans m a.val = runTrans m b.val := congrArg Subtype.val hab
        exact Subtype.ext
          (hb.injOn (Finset.mem_coe.mpr a.2) (Finset.mem_coe.mpr b.2) h)
      · intro y
        obtain ⟨x, hx, hxy⟩ := hb.surjOn (Finset.mem_coe.mpr y.2)
        exact ⟨⟨x, Finset.mem_coe.mp hx⟩, Subtype.ext hxy⟩)

@[simp] theorem bijEquiv_apply (hb : Set.BijOn (runTrans m) ↑S ↑T) (x : {x // x ∈ S}) :
    (bijEquiv hb x).val = runTrans m x.val := rfl

/-- The sandwich `σ ∘ g ∘ τ` of a realized permutation of `S` is a realized
permutation of `T`. -/
theorem realizedPerm_sandwich (hm : m ∈ NonCrossing w) (hm' : m' ∈ NonCrossing w)
    (hσ : Set.BijOn (runTrans m) ↑S ↑T) (hτ : Set.BijOn (runTrans m') ↑T ↑S)
    {g : Equiv.Perm {x // x ∈ S}} (hg : RealizedPerm S g) :
    RealizedPerm T ((bijEquiv hτ).trans (g.trans (bijEquiv hσ))) := by
  obtain ⟨n, hn, hr⟩ := hg
  refine ⟨m' * n * m, Submonoid.mul_mem _ (Submonoid.mul_mem _ hm' hn) hm, fun t => ?_⟩
  change runTrans m (g (bijEquiv hτ t)).val = runTrans (m' * n * m) t.val
  rw [hr (bijEquiv hτ t), bijEquiv_apply]
  simp [runTrans_mul]

/-- The composite of the two transport bijections is a realized permutation of
`T`. -/
theorem realizedPerm_beta (hm : m ∈ NonCrossing w) (hm' : m' ∈ NonCrossing w)
    (hσ : Set.BijOn (runTrans m) ↑S ↑T) (hτ : Set.BijOn (runTrans m') ↑T ↑S) :
    RealizedPerm T ((bijEquiv hτ).trans (bijEquiv hσ)) := by
  refine ⟨m' * m, Submonoid.mul_mem _ hm' hm, fun t => ?_⟩
  change runTrans m (bijEquiv hτ t).val = runTrans (m' * m) t.val
  rw [bijEquiv_apply]
  simp [runTrans_mul]

/-- The sandwich factors as the conjugate times the composite bijection. -/
theorem sandwich_eq_permCongr_mul (hσ : Set.BijOn (runTrans m) ↑S ↑T)
    (hτ : Set.BijOn (runTrans m') ↑T ↑S) (g : Equiv.Perm {x // x ∈ S}) :
    (bijEquiv hτ).trans (g.trans (bijEquiv hσ))
      = (bijEquiv hσ).permCongr g * (bijEquiv hτ).trans (bijEquiv hσ) := by
  refine Equiv.ext (fun t => ?_)
  simp [Equiv.permCongr_apply]

/-- **Conjugation by the transport bijection sends realized permutations of `S`
to realized permutations of `T`.** -/
theorem realizedPerm_permCongr (hm : m ∈ NonCrossing w) (hm' : m' ∈ NonCrossing w)
    (hσ : Set.BijOn (runTrans m) ↑S ↑T) (hτ : Set.BijOn (runTrans m') ↑T ↑S)
    {g : Equiv.Perm {x // x ∈ S}} (hg : RealizedPerm S g) :
    RealizedPerm T ((bijEquiv hσ).permCongr g) := by
  have hsand := realizedPerm_sandwich hm hm' hσ hτ hg
  have hbeta := realizedPerm_beta hm hm' hσ hτ
  have hfac := sandwich_eq_permCongr_mul hσ hτ g
  have hconj : (bijEquiv hσ).permCongr g
      = ((bijEquiv hτ).trans (g.trans (bijEquiv hσ)))
        * ((bijEquiv hτ).trans (bijEquiv hσ))⁻¹ :=
    eq_mul_inv_of_mul_eq hfac.symm
  rw [hconj]
  exact (realizedSubgroup T).mul_mem hsand ((realizedSubgroup T).inv_mem hbeta)

/-- Conjugation by the transport bijection, as a homomorphism of the realized
groups. -/
noncomputable def transportHom (hm : m ∈ NonCrossing w) (hm' : m' ∈ NonCrossing w)
    (hσ : Set.BijOn (runTrans m) ↑S ↑T) (hτ : Set.BijOn (runTrans m') ↑T ↑S) :
    realizedSubgroup S →* realizedSubgroup T where
  toFun g := ⟨(bijEquiv hσ).permCongr g.val,
    realizedPerm_permCongr hm hm' hσ hτ (mem_realizedSubgroup.mp g.2)⟩
  map_one' := by
    refine Subtype.ext ?_
    refine Equiv.ext (fun t => ?_)
    simp [Equiv.permCongr_apply]
  map_mul' a b := by
    refine Subtype.ext ?_
    refine Equiv.ext (fun t => ?_)
    simp [Equiv.permCongr_apply]

/-- Conjugation by an equivalence of `T` with itself is conjugation in the
permutation group. -/
theorem permCongr_self (b x : Equiv.Perm {x // x ∈ T}) :
    b.permCongr x = b * x * b⁻¹ := by
  refine Equiv.ext (fun t => ?_)
  simp

/-- Transport composed with the reverse transport is conjugation by the
composite bijection. -/
theorem permCongr_trans_apply (hσ : Set.BijOn (runTrans m) ↑S ↑T)
    (hτ : Set.BijOn (runTrans m') ↑T ↑S) (x : Equiv.Perm {x // x ∈ T}) :
    (bijEquiv hσ).permCongr ((bijEquiv hτ).permCongr x)
      = ((bijEquiv hτ).trans (bijEquiv hσ)).permCongr x := by
  refine Equiv.ext (fun t => ?_)
  simp [Equiv.permCongr_apply]

/-- **The transport homomorphism is surjective.** -/
theorem transportHom_surjective (hm : m ∈ NonCrossing w) (hm' : m' ∈ NonCrossing w)
    (hσ : Set.BijOn (runTrans m) ↑S ↑T) (hτ : Set.BijOn (runTrans m') ↑T ↑S) :
    Function.Surjective (transportHom hm hm' hσ hτ) := by
  intro e
  set b : Equiv.Perm {x // x ∈ T} := (bijEquiv hτ).trans (bijEquiv hσ) with hb
  have hbmem : b ∈ realizedSubgroup T := realizedPerm_beta hm hm' hσ hτ
  have hxmem : b⁻¹ * e.val * b ∈ realizedSubgroup T :=
    (realizedSubgroup T).mul_mem
      ((realizedSubgroup T).mul_mem ((realizedSubgroup T).inv_mem hbmem) e.2) hbmem
  refine ⟨⟨(bijEquiv hτ).permCongr (b⁻¹ * e.val * b),
    realizedPerm_permCongr hm' hm hτ hσ hxmem⟩, ?_⟩
  refine Subtype.ext ?_
  change (bijEquiv hσ).permCongr ((bijEquiv hτ).permCongr (b⁻¹ * e.val * b)) = e.val
  rw [permCongr_trans_apply hσ hτ, ← hb, permCongr_self]
  group

end Transport

/-- **The heart lemma H1 only depends on the mutual-reachability class.** -/
theorem isCyclic_realizedSubgroup_of_reachEquiv {S T : Finset (Config w)}
    (h : Holonomy.ReachEquiv S T) (hS : IsCyclic (realizedSubgroup S)) :
    IsCyclic (realizedSubgroup T) := by
  obtain ⟨⟨m, hm, hT⟩, hback⟩ := h
  obtain ⟨m', hm', hSim⟩ := hback
  have hσ : Set.BijOn (runTrans m) ↑S ↑T :=
    Holonomy.bijOn_of_reachEquiv hm hT ⟨m', hm', hSim⟩
  have hτ : Set.BijOn (runTrans m') ↑T ↑S :=
    Holonomy.bijOn_of_reachEquiv hm' hSim ⟨m, hm, hT⟩
  haveI := hS
  exact isCyclic_of_surjective (transportHom hm hm' hσ hτ)
    (transportHom_surjective hm hm' hσ hτ)

end Internal
end AllenderOQ3
