import AllenderOQ3.Internal.RealizedPerms
import AllenderOQ3.Internal.NonCrossingCyclic

set_option autoImplicit false

/-!
# Realized permutations are order automorphisms

Continuation of `LocalizedCyclicity.lean` and `RealizedPerms.lean`, on the way to
the heart lemma H1 (`IsCyclic (realizedSubgroup S)`).

A monotone self-map of a poset that restricts to a bijection of a finite set `S`
not only *preserves* the order on `S`, it *reflects* it: the inverse bijection is
a positive iterate of the map (`exists_iterate_eq_id_on`), hence monotone as
well.  So every realized permutation of `S` is an order automorphism of the
subposet induced on `S`, and it preserves the minimal-antichain layering of `S`
in both directions.

Two consequences are recorded:

* `realizedPerm_mem_minLayer_iff` — layer membership is an equivalence, not just
  an implication (the implication is `realizedPerm_mem_minLayer`);
* `realizedSubgroup_eq_bot_of_chain` / `isCyclic_realizedSubgroup_of_chain` —
  H1 holds outright when the configurations of `S` are pairwise comparable: each
  antichain layer of a chain is a singleton, so the only realized permutation is
  the identity.

Everything here is `sorry`-free.
-/

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

section Ordered

variable {alpha : Type} [PartialOrder alpha]

/-- **A monotone self-bijection of a finite set reflects the order on it.**
Some positive iterate `f^[k]` is the identity on `S`, so the monotone map
`f^[k-1]` inverts `f` on `S`. -/
theorem le_of_monotone_bijOn {f : alpha → alpha} {S : Finset alpha}
    (hmono : Monotone f) (hb : Set.BijOn f ↑S ↑S) {x y : alpha}
    (hx : x ∈ S) (hy : y ∈ S) (hle : f x ≤ f y) : x ≤ y := by
  obtain ⟨k, hk, hid⟩ := exists_iterate_eq_id_on f S hb
  have hk1 : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
  have hstep : ∀ z ∈ S, f^[k - 1] (f z) = z := by
    intro z hz
    calc f^[k - 1] (f z) = f^[k - 1 + 1] z := (Function.iterate_succ_apply f (k - 1) z).symm
      _ = f^[k] z := by rw [hk1]
      _ = z := hid z hz
  have h := (hmono.iterate (k - 1)) hle
  rwa [hstep x hx, hstep y hy] at h

/-- A monotone self-bijection of a finite set is an order isomorphism of the
induced subposet. -/
theorem monotone_bijOn_le_iff {f : alpha → alpha} {S : Finset alpha}
    (hmono : Monotone f) (hb : Set.BijOn f ↑S ↑S) {x y : alpha}
    (hx : x ∈ S) (hy : y ∈ S) : f x ≤ f y ↔ x ≤ y :=
  ⟨le_of_monotone_bijOn hmono hb hx hy, fun h => hmono h⟩

/-- Every remainder of the min-layering is contained in `S`. -/
theorem layerRest_subset {S : Finset alpha} : ∀ j, layerRest S j ⊆ S := by
  intro j
  induction j with
  | zero => exact fun x hx => hx
  | succ j ih => exact fun x hx => ih (Finset.mem_sdiff.mp hx).1

/-- Every antichain layer of the min-layering is contained in `S`. -/
theorem minLayer_subset {S : Finset alpha} (j : Nat) : minLayer S j ⊆ S :=
  fun _ hx => layerRest_subset j (minIn_subset hx)

/-- **In a chain every antichain layer is a singleton**: two members of the same
layer of a totally ordered `S` are equal. -/
theorem minLayer_subsingleton_of_chain {S : Finset alpha}
    (hchain : ∀ x ∈ S, ∀ y ∈ S, x ≤ y ∨ y ≤ x) (j : Nat) {x y : alpha}
    (hx : x ∈ minLayer S j) (hy : y ∈ minLayer S j) : x = y := by
  rcases hchain x (minLayer_subset j hx) y (minLayer_subset j hy) with h | h
  · exact minLayer_antichain j hx hy h
  · exact (minLayer_antichain j hy hx h).symm

end Ordered

variable {w : Nat}

/-- **Realized permutations are order automorphisms of `S`.** -/
theorem realizedPerm_le_iff {S : Finset (Config w)} {e : Equiv.Perm {x // x ∈ S}}
    (h : RealizedPerm S e) (x y : {x // x ∈ S}) :
    (e x).val ≤ (e y).val ↔ x.val ≤ y.val := by
  obtain ⟨m, hm, hb, hr⟩ := bijOn_of_realizedPerm h
  have hmono : Monotone (runTrans m) := monotone_of_mem_nonCrossing hm
  rw [hr x, hr y]
  exact monotone_bijOn_le_iff hmono hb x.2 y.2

/-- **Layer membership is preserved in both directions** by a realized
permutation: the inverse permutation is realized too. -/
theorem realizedPerm_mem_minLayer_iff {S : Finset (Config w)}
    {e : Equiv.Perm {x // x ∈ S}} (h : RealizedPerm S e) {j : Nat}
    {x : {x // x ∈ S}} : (e x).val ∈ minLayer S j ↔ x.val ∈ minLayer S j := by
  refine ⟨fun hx => ?_, fun hx => realizedPerm_mem_minLayer h hx⟩
  have hinv := realizedPerm_mem_minLayer (RealizedPerm.inv h) (x := e x) hx
  have hxx : e⁻¹ (e x) = x := by simp
  rwa [hxx] at hinv

/-- **H1 for chains.**  If the configurations of `S` are pairwise comparable then
the only permutation of `S` realized by `NonCrossing w` is the identity: each
antichain layer of `S` is a singleton and realized permutations preserve the
layering. -/
theorem realizedSubgroup_eq_bot_of_chain {S : Finset (Config w)}
    (hchain : ∀ x ∈ S, ∀ y ∈ S, x ≤ y ∨ y ≤ x) :
    realizedSubgroup S = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr ?_
  intro e he
  refine perm_eq_of_forall_minLayer (f := 1) ?_
  intro j x hx
  have hex : (e x).val ∈ minLayer S j :=
    realizedPerm_mem_minLayer (mem_realizedSubgroup.mp he) hx
  exact Subtype.ext (minLayer_subsingleton_of_chain hchain j hex hx)

/-- **The heart lemma H1 in the totally ordered case.** -/
theorem isCyclic_realizedSubgroup_of_chain {S : Finset (Config w)}
    (hchain : ∀ x ∈ S, ∀ y ∈ S, x ≤ y ∨ y ≤ x) :
    IsCyclic (realizedSubgroup S) := by
  rw [realizedSubgroup_eq_bot_of_chain hchain]
  infer_instance

/-! ### H1 at the top of the holonomy tower: `S = univ` -/

/-- Powers of a transition act by iteration. -/
theorem runTrans_pow (m : TransMonoid w) :
    ∀ (k : Nat) (x : Config w), runTrans (m ^ k) x = (runTrans m)^[k] x := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, runTrans_mul, ih x, Function.iterate_succ_apply']

/-- **An element of `NonCrossing w` acting bijectively on *all* configurations is
a unit.**  Some positive power acts as the identity on every configuration, hence
is the identity of the monoid. -/
theorem isUnit_of_bijOn_univ {m : TransMonoid w} (hm : m ∈ NonCrossing w)
    (hb : Set.BijOn (runTrans m) ↑(Finset.univ : Finset (Config w))
      ↑(Finset.univ : Finset (Config w))) :
    IsUnit (⟨m, hm⟩ : NonCrossing w) := by
  obtain ⟨k, hk, hid⟩ := exists_iterate_eq_id_on (runTrans m) Finset.univ hb
  refine IsUnit.of_pow_eq_one (n := k) ?_ (Nat.pos_iff_ne_zero.mp hk)
  refine Subtype.ext ?_
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  refine transMonoid_ext (fun x => ?_)
  rw [runTrans_pow m k x, hid x (Finset.mem_univ x)]
  rfl

/-- The permutation of the set of *all* configurations induced by a unit of
`NonCrossing w`.  The unit is used through its inverse, so that the assignment
is multiplicative (`runTrans` is anti-multiplicative). -/
noncomputable def unitPerm (u : (NonCrossing w)ˣ) :
    Equiv.Perm {x // x ∈ (Finset.univ : Finset (Config w))} where
  toFun x := ⟨runTrans ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) x.val, Finset.mem_univ _⟩
  invFun x := ⟨runTrans ((u : (NonCrossing w)ˣ) : TransMonoid w) x.val, Finset.mem_univ _⟩
  left_inv x := by
    refine Subtype.ext ?_
    change runTrans ((u : (NonCrossing w)ˣ) : TransMonoid w)
      (runTrans ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) x.val) = x.val
    rw [← runTrans_mul]
    have hmul : ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) *
        ((u : (NonCrossing w)ˣ) : TransMonoid w) = 1 := by
      rw [← Submonoid.coe_mul, u.inv_mul, OneMemClass.coe_one]
    rw [hmul]
    rfl
  right_inv x := by
    refine Subtype.ext ?_
    change runTrans ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w)
      (runTrans ((u : (NonCrossing w)ˣ) : TransMonoid w) x.val) = x.val
    rw [← runTrans_mul]
    have hmul : ((u : (NonCrossing w)ˣ) : TransMonoid w) *
        ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) = 1 := by
      rw [← Submonoid.coe_mul, u.mul_inv, OneMemClass.coe_one]
    rw [hmul]
    rfl

@[simp] theorem unitPerm_apply (u : (NonCrossing w)ˣ)
    (x : {x // x ∈ (Finset.univ : Finset (Config w))}) :
    (unitPerm u x).val = runTrans ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) x.val := rfl

/-- `unitPerm` as a group homomorphism. -/
noncomputable def unitPermHom :
    (NonCrossing w)ˣ →* Equiv.Perm {x // x ∈ (Finset.univ : Finset (Config w))} where
  toFun := unitPerm
  map_one' := by
    refine Equiv.ext (fun x => Subtype.ext ?_)
    rw [unitPerm_apply]
    simp
  map_mul' u v := by
    refine Equiv.ext (fun x => Subtype.ext ?_)
    rw [unitPerm_apply]
    have hinv : ((u * v)⁻¹ : (NonCrossing w)ˣ) = v⁻¹ * u⁻¹ := mul_inv_rev u v
    rw [hinv]
    have hcoe : ((v⁻¹ * u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) =
        ((v⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) *
          ((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w) := by
      simp
    rw [hcoe, runTrans_mul]
    rfl

/-- **The realized permutations of the full configuration set are exactly the
permutations induced by units of `NonCrossing w`.** -/
theorem realizedSubgroup_univ_eq_range :
    realizedSubgroup (Finset.univ : Finset (Config w)) = (unitPermHom (w := w)).range := by
  ext e
  constructor
  · intro he
    obtain ⟨m, hm, hb, hr⟩ := bijOn_of_realizedPerm (mem_realizedSubgroup.mp he)
    obtain ⟨u, hu⟩ := isUnit_of_bijOn_univ hm hb
    refine ⟨u⁻¹, ?_⟩
    refine Equiv.ext (fun x => Subtype.ext ?_)
    change (unitPerm u⁻¹ x).val = (e x).val
    rw [unitPerm_apply, hr x, inv_inv]
    have : ((u : (NonCrossing w)ˣ) : TransMonoid w) = m := by
      rw [hu]
    rw [this]
  · rintro ⟨u, rfl⟩
    refine mem_realizedSubgroup.mpr ⟨((u⁻¹ : (NonCrossing w)ˣ) : TransMonoid w), ?_, fun x => rfl⟩
    exact ((u⁻¹ : (NonCrossing w)ˣ) : NonCrossing w).2

/-- **The heart lemma H1 for the full configuration set.**  Every permutation of
all configurations realized by `NonCrossing w` comes from a unit, and the unit
group is cyclic (`nonCrossing_units_cyclic`). -/
theorem isCyclic_realizedSubgroup_univ :
    IsCyclic (realizedSubgroup (Finset.univ : Finset (Config w))) := by
  haveI := nonCrossing_units_cyclic w
  rw [realizedSubgroup_univ_eq_range]
  exact isCyclic_of_surjective (unitPermHom (w := w)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

end Internal
end AllenderOQ3
