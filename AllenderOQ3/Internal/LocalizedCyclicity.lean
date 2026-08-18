import AllenderOQ3.Internal.NonCrossingUnits

set_option autoImplicit false

/-!
# Localized cyclicity, step 1: monotone bijections preserve minimal elements

First bricks of the heart lemma H1 (docs/HMV_ALGEBRA_NOTES.md, section 4): the
localized analogue of HMV Lemma 12 and the antichain layering skeleton of HMV
Proposition 13.

A monotone self-map of a partial order that restricts to a bijection of a
finite set `S` permutes the minimal elements of `S`.  Monotonicity of the
*inverse* bijection is not available (a monotone bijection between subsets of
a poset need not reflect the order), so the downward step of HMV's argument is
replaced by finiteness: some positive iterate of the map is the identity on
`S` (`exists_iterate_eq_id_on`), and the `(k-1)`-st iterate serves as the
missing monotone inverse.

Everything here is `sorry`-free.
-/

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

section Plain

variable {alpha : Type}

/-- **Some positive iterate of a self-bijection of a finite set is the identity
on it.**  The bijection generates a finite cyclic subgroup of the permutations
of `S`; the group order does the job. -/
theorem exists_iterate_eq_id_on (f : alpha → alpha) (S : Finset alpha)
    (hb : Set.BijOn f ↑S ↑S) : ∃ k : Nat, 0 < k ∧ ∀ x ∈ S, f^[k] x = x := by
  classical
  set g : {a // a ∈ S} → {a // a ∈ S} :=
    fun x => ⟨f x.1, Finset.mem_coe.mp (hb.mapsTo (Finset.mem_coe.mpr x.2))⟩ with hgdef
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 : f a.1 = f b.1 := congrArg Subtype.val hab
    exact Subtype.ext
      (hb.injOn (Finset.mem_coe.mpr a.2) (Finset.mem_coe.mpr b.2) h1)
  have hgbij : Function.Bijective g := Finite.injective_iff_bijective.mp hginj
  set e : Equiv.Perm {a // a ∈ S} := Equiv.ofBijective g hgbij with hedef
  have hne : Nonempty (Equiv.Perm {a // a ∈ S}) := ⟨1⟩
  refine ⟨Fintype.card (Equiv.Perm {a // a ∈ S}), Fintype.card_pos, ?_⟩
  have hval : ∀ (i : Nat) (x : {a // a ∈ S}), ((e ^ i) x).1 = f^[i] x.1 := by
    intro i
    induction i with
    | zero =>
      intro x
      simp
    | succ i ih =>
      intro x
      have h1 : (e ^ (i + 1)) x = (e ^ i) (e x) := by
        rw [pow_succ]
        rfl
      have h2 : e x = g x := rfl
      rw [h1, ih (e x), h2, hgdef]
      simp [Function.iterate_succ_apply]
  intro x hx
  have h := hval (Fintype.card (Equiv.Perm {a // a ∈ S})) ⟨x, hx⟩
  rw [pow_card_eq_one] at h
  exact h.symm

/-- A self-bijection of `S` that also self-bijects a subset `T ⊆ S` restricts
to a self-bijection of the difference `S \ T`.  (Pure set combinatorics — no
order structure.) -/
theorem bijOn_sdiff {f : alpha → alpha} {S T : Finset alpha}
    (hb : Set.BijOn f ↑S ↑S) (hbT : Set.BijOn f ↑T ↑T) (hTS : T ⊆ S) :
    Set.BijOn f ↑(S \ T) ↑(S \ T) := by
  have hmap : Set.MapsTo f ↑(S \ T) ↑(S \ T) := by
    intro x hx
    obtain ⟨hxS, hxT⟩ := Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)
    have hfxS : f x ∈ S := Finset.mem_coe.mp (hb.mapsTo (Finset.mem_coe.mpr hxS))
    refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hfxS, fun hfxT => ?_⟩)
    obtain ⟨y, hyT, hyx⟩ := hbT.surjOn (Finset.mem_coe.mpr hfxT)
    have hyS : y ∈ S := hTS (Finset.mem_coe.mp hyT)
    have hyeq : y = x :=
      hb.injOn (Finset.mem_coe.mpr hyS) (Finset.mem_coe.mpr hxS) hyx
    exact hxT (hyeq ▸ Finset.mem_coe.mp hyT)
  have hinj : Set.InjOn f ↑(S \ T) := by
    intro a ha b hb2 hab
    have haS : a ∈ S := (Finset.mem_sdiff.mp (Finset.mem_coe.mp ha)).1
    have hbS : b ∈ S := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hb2)).1
    exact hb.injOn (Finset.mem_coe.mpr haS) (Finset.mem_coe.mpr hbS) hab
  refine ⟨hmap, hinj, ?_⟩
  intro y hy
  obtain ⟨hyS, hyT⟩ := Finset.mem_sdiff.mp (Finset.mem_coe.mp hy)
  obtain ⟨x, hxS, hxy⟩ := hb.surjOn (Finset.mem_coe.mpr hyS)
  refine ⟨x, Finset.mem_coe.mpr
    (Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp hxS, fun hxT => ?_⟩), hxy⟩
  have hfxT : f x ∈ T := Finset.mem_coe.mp (hbT.mapsTo (Finset.mem_coe.mpr hxT))
  rw [hxy] at hfxT
  exact hyT hfxT

end Plain

section Ordered

variable {alpha : Type} [PartialOrder alpha]

/-- `x` is a minimal member of the finite set `S`. -/
def MinIn (S : Finset alpha) (x : alpha) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, y ≤ x → y = x

/-- The minimal members of `S`, as a finset. -/
noncomputable def minIn (S : Finset alpha) : Finset alpha :=
  S.filter (fun x => ∀ y ∈ S, y ≤ x → y = x)

theorem mem_minIn {S : Finset alpha} {x : alpha} : x ∈ minIn S ↔ MinIn S x := by
  simp [minIn, MinIn, Finset.mem_filter]

theorem minIn_subset {S : Finset alpha} : minIn S ⊆ S := Finset.filter_subset _ _

/-- Nonempty finite sets have a minimal member. -/
theorem minIn_nonempty {S : Finset alpha} (hS : S.Nonempty) : (minIn S).Nonempty := by
  obtain ⟨m, hm⟩ := S.exists_minimal hS
  exact ⟨m, mem_minIn.mpr ⟨hm.1, fun y hy hle => le_antisymm hle (hm.2 hy hle)⟩⟩

/-- **Monotone bijections of a finite set preserve minimality** (localized HMV
Lemma 12).  If `z < f x` witnessed non-minimality of `f x`, then applying the
monotone map `f^[k-1]` (where `f^[k]` is the identity on `S`) would produce a
member of `S` strictly below `x`. -/
theorem minIn_image {f : alpha → alpha} (hmono : Monotone f) {S : Finset alpha}
    (hb : Set.BijOn f ↑S ↑S) {x : alpha} (hx : MinIn S x) : MinIn S (f x) := by
  obtain ⟨hxS, hxmin⟩ := hx
  have hfxS : f x ∈ S := Finset.mem_coe.mp (hb.mapsTo (Finset.mem_coe.mpr hxS))
  refine ⟨hfxS, ?_⟩
  intro y hyS hyle
  by_contra hne
  obtain ⟨k, hk, hid⟩ := exists_iterate_eq_id_on f S hb
  have hmts : Set.MapsTo (f^[k - 1]) ↑S ↑S := hb.mapsTo.iterate (k - 1)
  have hzS : f^[k - 1] y ∈ S := Finset.mem_coe.mp (hmts (Finset.mem_coe.mpr hyS))
  have hk1 : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
  have hfk : f^[k - 1] (f x) = x := by
    have hidx : f^[k] x = x := hid x hxS
    calc f^[k - 1] (f x) = f^[k - 1 + 1] x := (Function.iterate_succ_apply f (k - 1) x).symm
      _ = f^[k] x := by rw [hk1]
      _ = x := hidx
  have hle : f^[k - 1] y ≤ x := by
    have hstep := (hmono.iterate (k - 1)) hyle
    rwa [hfk] at hstep
  have hzx : f^[k - 1] y = x := hxmin _ hzS hle
  have hcontra : f^[k] y = f x := by
    calc f^[k] y = f^[k - 1 + 1] y := by rw [hk1]
      _ = f (f^[k - 1] y) := Function.iterate_succ_apply' f (k - 1) y
      _ = f x := by rw [hzx]
  rw [hid y hyS] at hcontra
  exact hne hcontra

/-- **A monotone bijection of `S` restricts to a bijection of the minimal
members of `S`.**  Injectivity restricts; surjectivity follows by counting. -/
theorem bijOn_minIn {f : alpha → alpha} (hmono : Monotone f) {S : Finset alpha}
    (hb : Set.BijOn f ↑S ↑S) : Set.BijOn f ↑(minIn S) ↑(minIn S) := by
  have hmap : Set.MapsTo f ↑(minIn S) ↑(minIn S) := by
    intro x hx
    exact Finset.mem_coe.mpr
      (mem_minIn.mpr (minIn_image hmono hb (mem_minIn.mp (Finset.mem_coe.mp hx))))
  have hinj : Set.InjOn f ↑(minIn S) := by
    intro a ha b hb2 hab
    have haS : a ∈ S := (mem_minIn.mp (Finset.mem_coe.mp ha)).1
    have hbS : b ∈ S := (mem_minIn.mp (Finset.mem_coe.mp hb2)).1
    exact hb.injOn (Finset.mem_coe.mpr haS) (Finset.mem_coe.mpr hbS) hab
  refine ⟨hmap, hinj, ?_⟩
  have himg : (minIn S).image f ⊆ minIn S := by
    intro y hy
    obtain ⟨x, hxm, rfl⟩ := Finset.mem_image.mp hy
    exact mem_minIn.mpr (minIn_image hmono hb (mem_minIn.mp hxm))
  have hcard : ((minIn S).image f).card = (minIn S).card :=
    Finset.card_image_of_injOn hinj
  have heq : (minIn S).image f = minIn S :=
    Finset.eq_of_subset_of_card_le himg (le_of_eq hcard.symm)
  intro y hy
  have hymem : y ∈ (minIn S).image f := by
    rw [heq]
    exact Finset.mem_coe.mp hy
  obtain ⟨x, hxm, hxy⟩ := Finset.mem_image.mp hymem
  exact ⟨x, Finset.mem_coe.mpr hxm, hxy⟩

/-- The iterated remainders of the minimal-antichain layering of `S`:
`layerRest S 0 = S`, and each step removes the current minimal members. -/
noncomputable def layerRest (S : Finset alpha) : Nat → Finset alpha
  | 0 => S
  | j + 1 => layerRest S j \ minIn (layerRest S j)

/-- The `j`-th antichain layer of `S` (HMV's `I_j`, localized). -/
noncomputable def minLayer (S : Finset alpha) (j : Nat) : Finset alpha :=
  minIn (layerRest S j)

/-- **A monotone self-bijection of `S` self-bijects every remainder and every
antichain layer of the min-layering** — the localized skeleton of HMV
Proposition 13.  Induction on the layer index, alternating `bijOn_minIn` and
`bijOn_sdiff`. -/
theorem bijOn_layerRest {f : alpha → alpha} (hmono : Monotone f) {S : Finset alpha}
    (hb : Set.BijOn f ↑S ↑S) :
    ∀ j, Set.BijOn f ↑(layerRest S j) ↑(layerRest S j) ∧
      Set.BijOn f ↑(minLayer S j) ↑(minLayer S j) := by
  intro j
  induction j with
  | zero => exact ⟨hb, bijOn_minIn hmono hb⟩
  | succ j ih =>
    have hrest : Set.BijOn f ↑(layerRest S (j + 1)) ↑(layerRest S (j + 1)) :=
      bijOn_sdiff ih.1 ih.2 minIn_subset
    exact ⟨hrest, bijOn_minIn hmono hrest⟩

/-- Each layer of the min-layering is an antichain. -/
theorem minLayer_antichain {S : Finset alpha} (j : Nat) {x y : alpha}
    (hx : x ∈ minLayer S j) (hy : y ∈ minLayer S j) (hxy : x ≤ y) : x = y := by
  have hxm := mem_minIn.mp hx
  have hym := mem_minIn.mp hy
  exact hym.2 x hxm.1 hxy

/-- The remainders strictly shrink while nonempty. -/
theorem layerRest_card_lt {S : Finset alpha} {j : Nat}
    (h : (layerRest S j).Nonempty) :
    (layerRest S (j + 1)).card < (layerRest S j).card := by
  have hne := minIn_nonempty h
  obtain ⟨m, hm⟩ := hne
  have hsub : layerRest S (j + 1) ⊆ layerRest S j := Finset.sdiff_subset
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.mpr ?_)
  exact ⟨m, minIn_subset hm, by
    intro hmem
    exact (Finset.mem_sdiff.mp hmem).2 hm⟩

/-- **The min-layering exhausts `S`**: every member of `S` lies in some
antichain layer with index below `S.card`. -/
theorem exists_mem_minLayer {S : Finset alpha} {x : alpha} (hx : x ∈ S) :
    ∃ j < S.card, x ∈ minLayer S j := by
  by_contra hcon
  push_neg at hcon
  have hmem : ∀ j ≤ S.card, x ∈ layerRest S j := by
    intro j
    induction j with
    | zero => intro _; exact hx
    | succ j ih =>
      intro hj
      have hxj : x ∈ layerRest S j := ih (Nat.le_of_succ_le hj)
      refine Finset.mem_sdiff.mpr ⟨hxj, fun hmin => ?_⟩
      exact hcon j (Nat.lt_of_succ_le hj) hmin
  have hcard : ∀ j ≤ S.card, (layerRest S j).card ≤ S.card - j := by
    intro j
    induction j with
    | zero => intro _; simp [layerRest]
    | succ j ih =>
      intro hj
      have hlt : (layerRest S (j + 1)).card < (layerRest S j).card :=
        layerRest_card_lt ⟨x, hmem j (Nat.le_of_succ_le hj)⟩
      have := ih (Nat.le_of_succ_le hj)
      omega
  have h1 : x ∈ layerRest S S.card := hmem S.card (le_refl _)
  have h2 : (layerRest S S.card).card ≤ 0 := by
    have := hcard S.card (le_refl _)
    omega
  have h3 : layerRest S S.card = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp h2)
  rw [h3] at h1
  simp at h1

/-- The heart-lemma instantiation: an element of `NonCrossing w` acting
bijectively on a finite set of configurations permutes its minimal members —
and hence every antichain layer of the min-layering. -/
theorem bijOn_minIn_of_mem_nonCrossing {w : Nat} {g : TransMonoid w}
    (hg : g ∈ NonCrossing w) {S : Finset (Config w)}
    (hb : Set.BijOn (runTrans g) ↑S ↑S) :
    Set.BijOn (runTrans g) ↑(minIn S) ↑(minIn S) :=
  bijOn_minIn (monotone_of_mem_nonCrossing hg) hb

end Ordered

end Internal
end AllenderOQ3
