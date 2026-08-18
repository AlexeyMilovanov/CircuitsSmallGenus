import AllenderOQ3.Internal.IntervalPieces
import AllenderOQ3.Internal.RealizedPerms

/-!
# Reduction of the heart lemma H1 to interval families — **OBSTRUCTED**

This file reduces the heart lemma H1 (`IsCyclic (realizedSubgroup S)`) to two
geometric cores, mirroring Proposition 13 of Hansen–Miltersen–Vinay: their
step "`f` is completely described by its restriction to the intervals of
`Im e`" is `isCyclic_realizedSubgroup_of_cores` below, and the cores isolate
their Lemmas 9–11.  Everything in this file is `sorry`-free and remains valid
as an implication.

**However, core A is FALSE for `NonCrossing w` from `w = 4` on** (established
2026-08-17 on the exact certified-layer model, `docs/EXACT_MODEL_NOTES.md`):
the four-letter word

  `rot 3 ; dup 0→1 ; dup 1→2 ; set position 1 := 0`

of certified layers (a rotation, two adjacent duplications, one partial
constant) maps `0001 ↔ 1010` — an involution of `S = {0001, 1010}` exchanging
a one-block configuration with a two-block one.  For `x = 0001` the pieces of
the image are `{1000, 0010}` while the image of the pieces is `{1010}`, so
`StabIntervalAction 4` fails.  The mechanism: a coordinate discarded into a
constant frees a wire of the cylinder, and the freed width allows duplications
to carry a block across the cut — HMV's Lemma 9 has no analogue once literal
gates are present.  The interval route CANNOT prove H1 for this monoid; any
H1 proof must use a different invariant.  This file is kept as the precise
record of where and why the route fails (its hypotheses also remain provable
for the constant-free HMV submonoid).
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## The interval family of a set of configurations -/

open Classical in
/-- All pieces of all members of `S`. -/
noncomputable def intervalFamily (S : Finset (Config w)) : Finset (Config w) :=
  S.biUnion intervalsOf

theorem mem_intervalFamily {S : Finset (Config w)} {y : Config w} :
    y ∈ intervalFamily S ↔ ∃ x ∈ S, y ∈ intervalsOf x := by
  simp [intervalFamily]

theorem isIntervalConfig_of_mem_intervalFamily {S : Finset (Config w)} {y : Config w}
    (h : y ∈ intervalFamily S) : IsIntervalConfig y := by
  obtain ⟨x, -, hy⟩ := mem_intervalFamily.mp h
  exact isIntervalConfig_of_mem_intervalsOf hy

/-! ## The two geometric cores -/

/-- **Core A (interval-wise action along stabilized sets).**  If `m` maps `S`
bijectively onto itself then the pieces of the image of every member are the
images of its pieces. -/
def StabIntervalAction (w : Nat) : Prop :=
  ∀ (S : Finset (Config w)) (m : TransMonoid w), m ∈ NonCrossing w →
    Set.BijOn (runTrans m) ↑S ↑S →
    ∀ x ∈ S, intervalsOf (runTrans m x) = (intervalsOf x).image (runTrans m)

/-- **Core B (H1 on interval families).**  The realized permutation group of a
set of interval configurations is cyclic. -/
def IntervalSetsCyclic (w : Nat) : Prop :=
  ∀ T : Finset (Config w), (∀ y ∈ T, IsIntervalConfig y) →
    IsCyclic (realizedSubgroup T)

/-! ## Stabilizers permute the interval family -/

/-- A self-map of a finite set with full image is a bijection of it. -/
theorem bijOn_of_image_eq {A : Finset (Config w)} {f : Config w → Config w}
    (h : A.image f = A) : Set.BijOn f ↑A ↑A := by
  have hinj : Set.InjOn f ↑A := Finset.injOn_of_card_image_eq (by rw [h])
  refine ⟨?_, hinj, ?_⟩
  · intro a ha
    have hmem : f a ∈ A.image f := Finset.mem_image_of_mem f (Finset.mem_coe.mp ha)
    rw [h] at hmem
    exact Finset.mem_coe.mpr hmem
  · intro b hb
    have hb' : b ∈ A.image f := by
      rw [h]
      exact Finset.mem_coe.mp hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb'
    exact ⟨a, Finset.mem_coe.mpr ha, rfl⟩

/-- An `S`-stabilizing element maps the interval family onto itself. -/
theorem image_intervalFamily (hA : StabIntervalAction w) {S : Finset (Config w)}
    {m : TransMonoid w} (hm : m ∈ NonCrossing w)
    (hb : Set.BijOn (runTrans m) ↑S ↑S) :
    (intervalFamily S).image (runTrans m) = intervalFamily S := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, hyx⟩ := mem_intervalFamily.mp hy
    have himg := hA S m hm hb x hx
    have hmem : runTrans m y ∈ intervalsOf (runTrans m x) := by
      rw [himg]
      exact Finset.mem_image_of_mem _ hyx
    refine mem_intervalFamily.mpr ⟨runTrans m x, ?_, hmem⟩
    exact Finset.mem_coe.mp (hb.mapsTo (Finset.mem_coe.mpr hx))
  · intro z hz
    obtain ⟨x', hx', hz'⟩ := mem_intervalFamily.mp hz
    obtain ⟨x, hxS, hxeq⟩ := hb.surjOn (Finset.mem_coe.mpr hx')
    have hx : x ∈ S := Finset.mem_coe.mp hxS
    have himg := hA S m hm hb x hx
    rw [← hxeq, himg] at hz'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz'
    exact Finset.mem_image_of_mem _ (mem_intervalFamily.mpr ⟨x, hx, hy⟩)

/-- An `S`-stabilizing element permutes the interval family. -/
theorem bijOn_intervalFamily (hA : StabIntervalAction w) {S : Finset (Config w)}
    {m : TransMonoid w} (hm : m ∈ NonCrossing w)
    (hb : Set.BijOn (runTrans m) ↑S ↑S) :
    Set.BijOn (runTrans m) ↑(intervalFamily S) ↑(intervalFamily S) :=
  bijOn_of_image_eq (image_intervalFamily hA hm hb)

/-! ## Determinacy: the family determines the action on `S` -/

/-- **Two `S`-stabilizing elements agreeing on the interval family agree on
`S`.**  A coordinate of the image of `x ∈ S` is `true` iff it is `true` in the
image of some piece of `x` (core A plus pointwise reconstruction). -/
theorem runTrans_eq_on_of_agree (hA : StabIntervalAction w) {S : Finset (Config w)}
    {m m' : TransMonoid w} (hm : m ∈ NonCrossing w) (hm' : m' ∈ NonCrossing w)
    (hb : Set.BijOn (runTrans m) ↑S ↑S) (hb' : Set.BijOn (runTrans m') ↑S ↑S)
    (hagree : ∀ y ∈ intervalFamily S, runTrans m y = runTrans m' y)
    {x : Config w} (hx : x ∈ S) : runTrans m x = runTrans m' x := by
  funext j
  have hiff : runTrans m x j = true ↔ runTrans m' x j = true := by
    rw [mem_intervalsOf_true_iff (x := runTrans m x) (j := j),
      mem_intervalsOf_true_iff (x := runTrans m' x) (j := j),
      hA S m hm hb x hx, hA S m' hm' hb' x hx]
    constructor
    · rintro ⟨y, hy, hyj⟩
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hy
      refine ⟨runTrans m' I, Finset.mem_image_of_mem _ hI, ?_⟩
      rw [← hagree I (mem_intervalFamily.mpr ⟨x, hx, hI⟩)]
      exact hyj
    · rintro ⟨y, hy, hyj⟩
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hy
      refine ⟨runTrans m I, Finset.mem_image_of_mem _ hI, ?_⟩
      rw [hagree I (mem_intervalFamily.mpr ⟨x, hx, hI⟩)]
      exact hyj
  cases h1 : runTrans m x j with
  | true => exact (hiff.mp h1).symm
  | false =>
    cases h2 : runTrans m' x j with
    | true =>
      have hcontra := hiff.mpr h2
      rw [h1] at hcontra
      simp at hcontra
    | false => rfl

/-! ## The induced permutation of a stabilized finite set -/

/-- The permutation of a finite set induced by a monoid element that bijects
it. -/
noncomputable def bijPerm {A : Finset (Config w)} {m : TransMonoid w}
    (hb : Set.BijOn (runTrans m) ↑A ↑A) : Equiv.Perm {x // x ∈ A} :=
  Equiv.ofBijective
    (fun x => ⟨runTrans m x.val, Finset.mem_coe.mp (hb.mapsTo (Finset.mem_coe.mpr x.2))⟩)
    (Finite.injective_iff_bijective.mp (fun a b hab =>
      Subtype.ext (hb.injOn (Finset.mem_coe.mpr a.2) (Finset.mem_coe.mpr b.2)
        (congrArg Subtype.val hab))))

@[simp] theorem bijPerm_apply {A : Finset (Config w)} {m : TransMonoid w}
    (hb : Set.BijOn (runTrans m) ↑A ↑A) (x : {x // x ∈ A}) :
    (bijPerm hb x).val = runTrans m x.val := rfl

/-! ## The subgroup of `S`-stabilizing realized permutations of the family -/

/-- A permutation of the interval family realized by an element that also
stabilizes `S`. -/
def StabRealized (S : Finset (Config w))
    (φ : Equiv.Perm {y // y ∈ intervalFamily S}) : Prop :=
  ∃ m ∈ NonCrossing w,
    (∀ y : {y // y ∈ intervalFamily S}, (φ y).val = runTrans m y.val) ∧
    Set.BijOn (runTrans m) ↑S ↑S

theorem bijOn_one (A : Finset (Config w)) :
    Set.BijOn (runTrans (1 : TransMonoid w)) ↑A ↑A :=
  ⟨fun _ ha => ha, fun _ _ _ _ h => h, fun y hy => ⟨y, hy, rfl⟩⟩

theorem StabRealized.one (S : Finset (Config w)) :
    StabRealized S (1 : Equiv.Perm {y // y ∈ intervalFamily S}) :=
  ⟨1, Submonoid.one_mem _, fun _ => rfl, bijOn_one S⟩

theorem StabRealized.mul {S : Finset (Config w)}
    {φ ψ : Equiv.Perm {y // y ∈ intervalFamily S}}
    (hφ : StabRealized S φ) (hψ : StabRealized S ψ) : StabRealized S (φ * ψ) := by
  obtain ⟨ma, hma, hra, hba⟩ := hφ
  obtain ⟨mb, hmb, hrb, hbb⟩ := hψ
  have heq : runTrans (mb * ma) = runTrans ma ∘ runTrans mb :=
    funext fun z => runTrans_mul mb ma z
  refine ⟨mb * ma, Submonoid.mul_mem _ hmb hma, ?_, ?_⟩
  · intro y
    have h1 : ((φ * ψ) y).val = (φ (ψ y)).val := rfl
    rw [h1, hra (ψ y), hrb y, heq]
    rfl
  · rw [heq]
    exact hba.comp hbb

theorem StabRealized.pow {S : Finset (Config w)}
    {φ : Equiv.Perm {y // y ∈ intervalFamily S}}
    (h : StabRealized S φ) : ∀ j : Nat, StabRealized S (φ ^ j) := by
  intro j
  induction j with
  | zero =>
    have h0 : φ ^ 0 = 1 := pow_zero φ
    rw [h0]
    exact StabRealized.one S
  | succ j ih =>
    have h1 : φ ^ (j + 1) = φ ^ j * φ := pow_succ φ j
    rw [h1]
    exact StabRealized.mul ih h

theorem StabRealized.inv {S : Finset (Config w)}
    {φ : Equiv.Perm {y // y ∈ intervalFamily S}}
    (h : StabRealized S φ) : StabRealized S φ⁻¹ := by
  classical
  set K := Fintype.card (Equiv.Perm {y // y ∈ intervalFamily S}) with hK
  have hKpos : 0 < K := Fintype.card_pos
  have hstep : φ ^ (K - 1) * φ = 1 := by
    have hcard : φ ^ K = 1 := pow_card_eq_one
    have hK1 : K - 1 + 1 = K := Nat.succ_pred_eq_of_pos hKpos
    calc φ ^ (K - 1) * φ = φ ^ (K - 1 + 1) := (pow_succ φ (K - 1)).symm
      _ = φ ^ K := by rw [hK1]
      _ = 1 := hcard
  have h2 : φ ^ (K - 1) = φ⁻¹ := mul_eq_one_iff_eq_inv.mp hstep
  rw [← h2]
  exact StabRealized.pow h (K - 1)

/-- The `S`-stabilizing realized permutations of the interval family, as a
subgroup. -/
noncomputable def stabRealizedSubgroup (S : Finset (Config w)) :
    Subgroup (Equiv.Perm {y // y ∈ intervalFamily S}) where
  carrier := {φ | StabRealized S φ}
  one_mem' := StabRealized.one S
  mul_mem' := by
    intro a b ha hb
    exact StabRealized.mul ha hb
  inv_mem' := by
    intro a ha
    exact StabRealized.inv ha

theorem mem_stabRealizedSubgroup {S : Finset (Config w)}
    {φ : Equiv.Perm {y // y ∈ intervalFamily S}} :
    φ ∈ stabRealizedSubgroup S ↔ StabRealized S φ := Iff.rfl

theorem stabRealizedSubgroup_le (S : Finset (Config w)) :
    stabRealizedSubgroup S ≤ realizedSubgroup (intervalFamily S) := by
  intro φ hφ
  obtain ⟨m, hm, hr, -⟩ := mem_stabRealizedSubgroup.mp hφ
  exact mem_realizedSubgroup.mpr ⟨m, hm, hr⟩

/-! ## The induced-permutation homomorphism -/

/-- A chosen witness realizing an element of `stabRealizedSubgroup S`. -/
noncomputable def stabWitness {S : Finset (Config w)} (φH : stabRealizedSubgroup S) :
    TransMonoid w :=
  Classical.choose (mem_stabRealizedSubgroup.mp φH.2)

theorem stabWitness_spec {S : Finset (Config w)} (φH : stabRealizedSubgroup S) :
    stabWitness φH ∈ NonCrossing w ∧
      (∀ y : {y // y ∈ intervalFamily S},
        (φH.1 y).val = runTrans (stabWitness φH) y.val) ∧
      Set.BijOn (runTrans (stabWitness φH)) ↑S ↑S :=
  Classical.choose_spec (mem_stabRealizedSubgroup.mp φH.2)

/-- The permutation of `S` induced by (the witness of) an element of the
stabilizing subgroup. -/
noncomputable def stabPermToFun {S : Finset (Config w)} (φH : stabRealizedSubgroup S) :
    Equiv.Perm {x // x ∈ S} :=
  bijPerm (stabWitness_spec φH).2.2

/-- Any two `S`-stabilizing realizers of the same family permutation induce the
same permutation of `S`. -/
theorem stabPerm_eq_of_realizes (hA : StabIntervalAction w) {S : Finset (Config w)}
    {m m' : TransMonoid w} (hm : m ∈ NonCrossing w) (hm' : m' ∈ NonCrossing w)
    (hb : Set.BijOn (runTrans m) ↑S ↑S) (hb' : Set.BijOn (runTrans m') ↑S ↑S)
    {φ : Equiv.Perm {y // y ∈ intervalFamily S}}
    (hr : ∀ y : {y // y ∈ intervalFamily S}, (φ y).val = runTrans m y.val)
    (hr' : ∀ y : {y // y ∈ intervalFamily S}, (φ y).val = runTrans m' y.val)
    {x : Config w} (hx : x ∈ S) : runTrans m x = runTrans m' x := by
  refine runTrans_eq_on_of_agree hA hm hm' hb hb' ?_ hx
  intro y hy
  rw [← hr ⟨y, hy⟩, ← hr' ⟨y, hy⟩]

/-- The induced-permutation homomorphism from the stabilizing subgroup of the
family to the permutations of `S`. -/
noncomputable def stabPermHom (hA : StabIntervalAction w) (S : Finset (Config w)) :
    stabRealizedSubgroup S →* Equiv.Perm {x // x ∈ S} :=
  MonoidHom.mk' stabPermToFun (by
    intro a b
    apply Equiv.ext
    intro x
    apply Subtype.ext
    obtain ⟨hmab, hrab, hbab⟩ := stabWitness_spec (a * b)
    obtain ⟨hma, hra, hba⟩ := stabWitness_spec a
    obtain ⟨hmb, hrb, hbb⟩ := stabWitness_spec b
    set ma := stabWitness a
    set mb := stabWitness b
    set mab := stabWitness (a * b)
    have heq : runTrans (mb * ma) = runTrans ma ∘ runTrans mb :=
      funext fun z => runTrans_mul mb ma z
    have hmba : mb * ma ∈ NonCrossing w := Submonoid.mul_mem _ hmb hma
    have hbba : Set.BijOn (runTrans (mb * ma)) ↑S ↑S := by
      rw [heq]
      exact hba.comp hbb
    have hrba : ∀ y : {y // y ∈ intervalFamily S},
        ((a * b).1 y).val = runTrans (mb * ma) y.val := by
      intro y
      have h1 : ((a * b).1 y).val = (a.1 (b.1 y)).val := rfl
      rw [h1, hra (b.1 y), hrb y, heq]
      rfl
    have hagree := stabPerm_eq_of_realizes hA hmab hmba hbab hbba hrab hrba
      (x := x.val) x.2
    have hlhs : ((stabPermToFun (a * b)) x).val = runTrans mab x.val := rfl
    have hrhs : ((stabPermToFun a * stabPermToFun b) x).val
        = runTrans (mb * ma) x.val := by
      have h1 : ((stabPermToFun a * stabPermToFun b) x).val
          = (stabPermToFun a (stabPermToFun b x)).val := rfl
      rw [h1]
      have h2 : (stabPermToFun a (stabPermToFun b x)).val
          = runTrans ma (stabPermToFun b x).val := rfl
      rw [h2]
      have h3 : (stabPermToFun b x).val = runTrans mb x.val := rfl
      rw [h3, heq]
      rfl
    rw [hlhs, hrhs, hagree])

/-- **The homomorphism hits exactly the realized permutations of `S`.** -/
theorem stabPermHom_range (hA : StabIntervalAction w) (S : Finset (Config w)) :
    (stabPermHom hA S).range = realizedSubgroup S := by
  ext e
  constructor
  · rintro ⟨φH, rfl⟩
    obtain ⟨hm, hr, hb⟩ := stabWitness_spec φH
    exact mem_realizedSubgroup.mpr ⟨stabWitness φH, hm, fun x => rfl⟩
  · intro he
    obtain ⟨m, hm, hb, hr⟩ := bijOn_of_realizedPerm (mem_realizedSubgroup.mp he)
    have hbT : Set.BijOn (runTrans m) ↑(intervalFamily S) ↑(intervalFamily S) :=
      bijOn_intervalFamily hA hm hb
    set φ : Equiv.Perm {y // y ∈ intervalFamily S} := bijPerm hbT with hφdef
    have hφmem : φ ∈ stabRealizedSubgroup S :=
      mem_stabRealizedSubgroup.mpr ⟨m, hm, fun y => rfl, hb⟩
    refine ⟨⟨φ, hφmem⟩, ?_⟩
    obtain ⟨hm', hr', hb'⟩ := stabWitness_spec (⟨φ, hφmem⟩ : stabRealizedSubgroup S)
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have hagree := stabPerm_eq_of_realizes hA hm' hm hb' hb hr'
      (fun y => rfl) (x := x.val) x.2
    have hlhs : ((stabPermHom hA S) ⟨φ, hφmem⟩ x).val
        = runTrans (stabWitness (⟨φ, hφmem⟩ : stabRealizedSubgroup S)) x.val := rfl
    rw [hlhs, hagree, ← hr x]

/-! ## H1 from the two cores -/

/-- **The heart lemma H1 follows from core A and core B.** -/
theorem isCyclic_realizedSubgroup_of_cores (hA : StabIntervalAction w)
    (hB : IntervalSetsCyclic w) (S : Finset (Config w)) :
    IsCyclic (realizedSubgroup S) := by
  haveI h1 : IsCyclic (realizedSubgroup (intervalFamily S)) :=
    hB _ (fun y hy => isIntervalConfig_of_mem_intervalFamily hy)
  haveI h2 : IsCyclic
      ((stabRealizedSubgroup S).subgroupOf (realizedSubgroup (intervalFamily S))) :=
    Subgroup.isCyclic _
  haveI h3 : IsCyclic (stabRealizedSubgroup S) :=
    isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe (stabRealizedSubgroup_le S)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (stabRealizedSubgroup_le S)).surjective
  rw [← stabPermHom_range hA S]
  exact isCyclic_of_surjective (stabPermHom hA S).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

end Internal
end AllenderOQ3
