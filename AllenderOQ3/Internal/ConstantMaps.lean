import AllenderOQ3.Internal.HolonomyGroups
import AllenderOQ3.Internal.GeneratorGeometry

set_option autoImplicit false

/-!
# Constant configuration maps are non-crossing

The bottom of the holonomy tower: every constant map `fun _ => q` lies in
`NonCrossing w`, hence every singleton `{q}` is reachable from every nonempty
set of configurations.  This yields the covering property of the reachability
lattice that the brick structure of the assembly design rests on.

The witness is a two-layer, edge-free circuit on `w` inputs whose `2w` gates
are all literals reading input `g % w`; an edge-free circuit is
incidence-cylindrical (`incidenceCylinder_of_edgeFree`), all its layers have
at most `w` vertices, and its layer-`0` transition sends every configuration
to the vector of literal values — a constant map.  Since the layer indexing
composed with the input index is a bijection of `Fin w`, a suitable input `x`
realizes *every* prescribed constant vector `q`.

Everything here is `sorry`-free.
-/

namespace AllenderOQ3
namespace Internal
namespace Holonomy

attribute [local instance] Classical.propDecidable

/-- The constant transition onto the configuration `q`. -/
noncomputable def constTrans {w : Nat} (q : Config w) : TransMonoid w :=
  ofConfigMap (fun _ => q)

@[simp] theorem runTrans_constTrans {w : Nat} (q s : Config w) :
    runTrans (constTrans q) s = q := rfl

/-- The two-layer all-literal witness circuit on `w` inputs. -/
def constCircuit (w : Nat) (hw : 0 < w) : ADRCircuit w where
  gateCount := 2 * w
  output := ⟨0, by omega⟩
  kind := fun g => ADRGate.literal ⟨g.val % w, Nat.mod_lt _ hw⟩ false
  layer := fun g => g.val / w
  edge := fun _ _ => false

theorem constCircuit_wellFormed (w : Nat) (hw : 0 < w) :
    WellFormedADR (constCircuit w hw) := by
  constructor
  · intro u v h
    exact absurd h Bool.false_ne_true
  · intro g _ h
    rfl

theorem constCircuit_hmvNormal (w : Nat) (hw : 0 < w) :
    HMVNormal (constCircuit w hw) := by
  refine ⟨constCircuit_wellFormed w hw, ?_⟩
  intro g hg
  exact absurd hg Bool.false_ne_true

theorem constCircuit_layer_le (w : Nat) (hw : 0 < w)
    (g : Fin (constCircuit w hw).gateCount) : (constCircuit w hw).layer g ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  have h2 : 2 ≤ g.val / w := hcon
  have h3 : 2 * w ≤ (g.val / w) * w := Nat.mul_le_mul_right w h2
  have h4 : (g.val / w) * w ≤ g.val := Nat.div_mul_le_self g.val w
  have h5 : g.val < 2 * w := g.isLt
  omega

theorem constCircuit_totalWidth (w : Nat) (hw : 0 < w) :
    TotalWidthAtMost (constCircuit w hw) w := by
  intro ell
  by_cases hell : ell ≤ 1
  · have hinj : Set.InjOn
        (fun g : Fin (constCircuit w hw).gateCount => (⟨g.val % w, Nat.mod_lt _ hw⟩ : Fin w))
        ↑(Finset.univ.filter (fun g : Fin (constCircuit w hw).gateCount =>
          (constCircuit w hw).layer g = ell)) := by
      intro a ha b hb hab
      have hla : a.val / w = ell :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hlb : b.val / w = ell :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      have hmod : a.val % w = b.val % w := congrArg Fin.val hab
      have ha' : a.val = w * (a.val / w) + a.val % w := (Nat.div_add_mod a.val w).symm
      have hb' : b.val = w * (b.val / w) + b.val % w := (Nat.div_add_mod b.val w).symm
      rw [hla] at ha'
      rw [hlb] at hb'
      apply Fin.ext
      omega
    have hcard := Finset.card_le_card_of_injOn
      (fun g : Fin (constCircuit w hw).gateCount => (⟨g.val % w, Nat.mod_lt _ hw⟩ : Fin w))
      (fun a _ => Finset.mem_univ _) hinj
    calc (Finset.univ.filter (fun g : Fin (constCircuit w hw).gateCount =>
            (constCircuit w hw).layer g = ell)).card
        ≤ (Finset.univ : Finset (Fin w)).card := hcard
      _ = w := by simp
  · have hempty : (Finset.univ.filter
        (fun g : Fin (constCircuit w hw).gateCount =>
          (constCircuit w hw).layer g = ell)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro g _
      have := constCircuit_layer_le w hw g
      omega
    rw [hempty]
    simp

/-- The layer-`1` vertex count of the witness circuit is exactly `w`. -/
theorem constCircuit_card_layer_one (w : Nat) (hw : 0 < w) :
    Fintype.card (LayerVertex (constCircuit w hw) 1) = w := by
  classical
  rw [Fintype.card_subtype]
  apply le_antisymm
  · exact constCircuit_totalWidth w hw 1
  · have hinj : Set.InjOn
        (fun j : Fin w =>
          (⟨w + j.val, by
            have hg : (constCircuit w hw).gateCount = 2 * w := rfl
            have hj := j.isLt
            omega⟩ :
            Fin (constCircuit w hw).gateCount))
        ↑(Finset.univ : Finset (Fin w)) := by
      intro a _ b _ hab
      have h2 : w + a.val = w + b.val := congrArg Fin.val hab
      apply Fin.ext
      omega
    have hmem : Set.MapsTo
        (fun j : Fin w =>
          (⟨w + j.val, by
            have hg : (constCircuit w hw).gateCount = 2 * w := rfl
            have hj := j.isLt
            omega⟩ :
            Fin (constCircuit w hw).gateCount))
        ↑(Finset.univ : Finset (Fin w))
        ↑(Finset.univ.filter (fun g : Fin (constCircuit w hw).gateCount =>
            (constCircuit w hw).layer g = 1)) := by
      intro j _
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      have hj : j.val < w := j.isLt
      have hl : (constCircuit w hw).layer
          ⟨w + j.val, by have hg : (constCircuit w hw).gateCount = 2 * w := rfl
                         have hj2 := j.isLt; omega⟩ = (w + j.val) / w := rfl
      rw [hl, Nat.add_comm w j.val, Nat.add_div_right _ hw, Nat.div_eq_of_lt hj]
    have hcard := Finset.card_le_card_of_injOn
      (fun j : Fin w =>
        (⟨w + j.val, by
            have hg : (constCircuit w hw).gateCount = 2 * w := rfl
            have hj := j.isLt
            omega⟩ :
          Fin (constCircuit w hw).gateCount))
      hmem hinj
    calc w = (Finset.univ : Finset (Fin w)).card := by simp
      _ ≤ _ := hcard

/-- The layer-`0` transition of the witness circuit realizes every constant
map, for a suitable input. -/
theorem exists_input_layerTrans_eq_constTrans (w : Nat) (hw : 0 < w)
    (cert : IncidenceCylinder (constCircuit w hw)) (q : Config w) :
    ∃ x : Fin w → Bool, layerTrans (constCircuit w hw) cert x 0 = constTrans q := by
  classical
  have h2 : (cert.layerOrder (0 + 1)).entries.length = w := by
    rw [length_entries_eq_card, constCircuit_card_layer_one w hw]
  set sigma : Fin w → Fin w := fun j =>
    ⟨(vtxAt (constCircuit w hw) cert (0 + 1) h2 j).val.val % w, Nat.mod_lt _ hw⟩
    with hsigma
  have hsig_inj : Function.Injective sigma := by
    intro a b hab
    have hva : ((vtxAt (constCircuit w hw) cert (0 + 1) h2 a).val.val) / w = 1 :=
      (vtxAt (constCircuit w hw) cert (0 + 1) h2 a).2
    have hvb : ((vtxAt (constCircuit w hw) cert (0 + 1) h2 b).val.val) / w = 1 :=
      (vtxAt (constCircuit w hw) cert (0 + 1) h2 b).2
    have hmod : (vtxAt (constCircuit w hw) cert (0 + 1) h2 a).val.val % w
        = (vtxAt (constCircuit w hw) cert (0 + 1) h2 b).val.val % w :=
      congrArg Fin.val hab
    have hda : (vtxAt (constCircuit w hw) cert (0 + 1) h2 a).val.val
        = w * ((vtxAt (constCircuit w hw) cert (0 + 1) h2 a).val.val / w)
          + (vtxAt (constCircuit w hw) cert (0 + 1) h2 a).val.val % w :=
      (Nat.div_add_mod _ w).symm
    have hdb : (vtxAt (constCircuit w hw) cert (0 + 1) h2 b).val.val
        = w * ((vtxAt (constCircuit w hw) cert (0 + 1) h2 b).val.val / w)
          + (vtxAt (constCircuit w hw) cert (0 + 1) h2 b).val.val % w :=
      (Nat.div_add_mod _ w).symm
    rw [hva] at hda
    rw [hvb] at hdb
    have hveq : (vtxAt (constCircuit w hw) cert (0 + 1) h2 a).val
        = (vtxAt (constCircuit w hw) cert (0 + 1) h2 b).val := by
      apply Fin.ext
      omega
    have hvtx : vtxAt (constCircuit w hw) cert (0 + 1) h2 a
        = vtxAt (constCircuit w hw) cert (0 + 1) h2 b := Subtype.ext hveq
    have hidx := congrArg (idxOfVtx (constCircuit w hw) cert (0 + 1) h2.le) hvtx
    rwa [idxOfVtx_vtxAt, idxOfVtx_vtxAt] at hidx
  have hsig_bij : Function.Bijective sigma :=
    Finite.injective_iff_bijective.mp hsig_inj
  set e := Equiv.ofBijective sigma hsig_bij with he
  refine ⟨fun i => q (e.symm i), ?_⟩
  apply transMonoid_ext
  intro s
  funext j
  have hk : (constCircuit w hw).kind
      (vtxAt (constCircuit w hw) cert (0 + 1) h2 j).val
        = ADRGate.literal (sigma j) false := rfl
  have hlit := layerTransMap_literal (c := constCircuit w hw) (cert := cert)
    (x := fun i => q (e.symm i)) (ell := 0) h2 s j hk
  have hrun : runTrans (layerTrans (constCircuit w hw) cert
      (fun i => q (e.symm i)) 0) s j
        = layerTransMap (constCircuit w hw) cert (fun i => q (e.symm i)) 0 s j := rfl
  rw [hrun, hlit]
  have hbeta : (if false = true then !((fun i => q (e.symm i)) (sigma j))
      else (fun i => q (e.symm i)) (sigma j)) = q (e.symm (sigma j)) := by
    rw [if_neg Bool.false_ne_true]
  rw [hbeta]
  have hes : e.symm (sigma j) = j := by
    have hj : sigma j = e j := rfl
    rw [hj, Equiv.symm_apply_apply]
  rw [hes]
  rfl

/-- **Every constant map is non-crossing.** -/
theorem constTrans_mem_nonCrossing {w : Nat} (q : Config w) :
    constTrans q ∈ NonCrossing w := by
  classical
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    have hsub : Subsingleton (Config 0) := by
      constructor
      intro a b
      funext i
      exact absurd i.isLt (by omega)
    have h1 : constTrans q = 1 := by
      apply transMonoid_ext
      intro s
      exact hsub.allEq q s
    rw [h1]
    exact Submonoid.one_mem _
  · obtain ⟨cert⟩ := incidenceCylinder_of_edgeFree (constCircuit w hw)
      (fun _ _ => rfl)
    obtain ⟨x, hx⟩ := exists_input_layerTrans_eq_constTrans w hw cert q
    rw [← hx]
    exact layerTrans_mem_nonCrossing _ cert x 0
      (constCircuit_hmvNormal w hw) (constCircuit_totalWidth w hw)

/-- **Every singleton is reachable from every nonempty set.** -/
theorem reach_singleton_of_mem {w : Nat} {S : Finset (Config w)} {q : Config w}
    (hq : q ∈ S) : Reach S {q} := by
  refine ⟨constTrans q, constTrans_mem_nonCrossing q, ?_⟩
  have h : ImageOf (constTrans q) S = S.image (fun _ => q) := rfl
  rw [h, Finset.image_const ⟨q, hq⟩]

/-- In particular the singletons are reachable sets of the lattice. -/
theorem reachableSet_singleton {w : Nat} (q : Config w) :
    ReachableSet ({q} : Finset (Config w)) :=
  reach_singleton_of_mem (Finset.mem_univ q)

/-! ## Bricks and the covering property -/

open Classical in
/-- The brick family of `S`: the maximal strict reachable subsets of `S`. -/
noncomputable def bricksOf {w : Nat} (S : Finset (Config w)) :
    Finset (Finset (Config w)) :=
  Finset.univ.filter (fun T => ReachableSet T ∧ T ⊂ S ∧
    ∀ U : Finset (Config w), ReachableSet U → U ⊂ S → T ⊆ U → U = T)

theorem mem_bricksOf {w : Nat} {S T : Finset (Config w)} :
    T ∈ bricksOf S ↔ ReachableSet T ∧ T ⊂ S ∧
      ∀ U : Finset (Config w), ReachableSet U → U ⊂ S → T ⊆ U → U = T := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

/-- **The covering property**: in a set with at least two elements, every
point lies in some brick.  The singleton `{q}` is a strict reachable subset
(`constTrans`), and any maximal strict reachable subset containing `q` — which
exists by finiteness — is maximal among *all* strict reachable subsets, since
every strict reachable superset again contains `q`. -/
theorem exists_brick_mem {w : Nat} {S : Finset (Config w)} (hS2 : 1 < S.card)
    {q : Config w} (hq : q ∈ S) : ∃ B ∈ bricksOf S, q ∈ B := by
  classical
  set F := Finset.univ.filter
    (fun T : Finset (Config w) => ReachableSet T ∧ T ⊂ S ∧ q ∈ T) with hF
  have hqS : ({q} : Finset (Config w)) ⊆ S := Finset.singleton_subset_iff.mpr hq
  have hqne : ({q} : Finset (Config w)) ≠ S := by
    intro h
    rw [← h] at hS2
    simp at hS2
  have hne : F.Nonempty := by
    refine ⟨{q}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, reachableSet_singleton q,
      lt_of_le_of_ne hqS hqne, Finset.mem_singleton_self q⟩⟩
  obtain ⟨B, hB⟩ := F.exists_maximal hne
  have hBmem := Finset.mem_filter.mp hB.1
  obtain ⟨hreach, hsub, hqB⟩ := hBmem.2
  refine ⟨B, mem_bricksOf.mpr ⟨hreach, hsub, ?_⟩, hqB⟩
  intro U hUreach hUsub hBU
  have hqU : q ∈ U := hBU hqB
  have hUF : U ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUreach, hUsub, hqU⟩
  have hUB : U ⊆ B := hB.2 hUF hBU
  exact Finset.Subset.antisymm hUB hBU

section BrickAction

variable {w : Nat}

/-- The action of a permutation of a type on its finite subsets, as a group
homomorphism into the permutations of the finset lattice. -/
def finsetPermHom {alpha : Type} : Equiv.Perm alpha →* Equiv.Perm (Finset alpha) where
  toFun pi := pi.finsetCongr
  map_one' := by
    refine Equiv.ext (fun A => ?_)
    change Finset.map (Equiv.toEmbedding (1 : Equiv.Perm alpha)) A = A
    refine Finset.ext (fun a => ?_)
    simp
  map_mul' f g := by
    refine Equiv.ext (fun A => ?_)
    simp [Equiv.finsetCongr_apply, Finset.map_map]
    rfl

/-- A permutation of `S` acting on the finite sets of configurations: it moves
subsets of `S` by their images and fixes configurations outside `S`. -/
noncomputable def setPerm (S : Finset (Config w)) (σ : Equiv.Perm {x // x ∈ S}) :
    Equiv.Perm (Finset (Config w)) :=
  finsetPermHom (Equiv.Perm.ofSubtype σ)

theorem setPerm_apply (S : Finset (Config w)) (σ : Equiv.Perm {x // x ∈ S})
    (A : Finset (Config w)) :
    setPerm S σ A = A.image (Equiv.Perm.ofSubtype σ) := by
  simp [setPerm, finsetPermHom, Equiv.finsetCongr_apply, Finset.map_eq_image]

theorem setPerm_one (S : Finset (Config w)) :
    setPerm S (1 : Equiv.Perm {x // x ∈ S}) = 1 := by
  simp [setPerm, map_one]

theorem setPerm_mul (S : Finset (Config w)) (σ τ : Equiv.Perm {x // x ∈ S}) :
    setPerm S (σ * τ) = setPerm S σ * setPerm S τ := by
  simp [setPerm, map_mul]

theorem setPerm_inv_apply (S : Finset (Config w)) (σ : Equiv.Perm {x // x ∈ S})
    (A : Finset (Config w)) : setPerm S σ⁻¹ (setPerm S σ A) = A := by
  have h : setPerm S σ⁻¹ * setPerm S σ = 1 := by
    rw [← setPerm_mul, inv_mul_cancel, setPerm_one]
  exact congrArg (fun e : Equiv.Perm (Finset (Config w)) => e A) h

theorem setPerm_subset {S A : Finset (Config w)} (σ : Equiv.Perm {x // x ∈ S})
    (hA : A ⊆ S) : setPerm S σ A ⊆ S := by
  rw [setPerm_apply]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hxS : x ∈ S := hA hx
  rw [Equiv.Perm.ofSubtype_apply_of_mem σ hxS]
  exact (σ ⟨x, hxS⟩).2

theorem setPerm_card (S A : Finset (Config w)) (σ : Equiv.Perm {x // x ∈ S}) :
    (setPerm S σ A).card = A.card := by
  rw [setPerm_apply]
  exact Finset.card_image_of_injective _ (Equiv.injective _)

theorem setPerm_mono {S A B : Finset (Config w)} (σ : Equiv.Perm {x // x ∈ S})
    (h : A ⊆ B) : setPerm S σ A ⊆ setPerm S σ B := by
  rw [setPerm_apply, setPerm_apply]
  exact Finset.image_subset_image h

theorem setPerm_eq_imageOf {S A : Finset (Config w)} {σ : Equiv.Perm {x // x ∈ S}}
    {m : TransMonoid w} (hA : A ⊆ S)
    (hr : ∀ x : {x // x ∈ S}, (σ x).val = runTrans m x.val) :
    setPerm S σ A = ImageOf m A := by
  rw [setPerm_apply]
  refine Finset.image_congr ?_
  intro x hx
  have hxS : x ∈ S := hA (Finset.mem_coe.mp hx)
  rw [Equiv.Perm.ofSubtype_apply_of_mem σ hxS]
  exact hr ⟨x, hxS⟩

theorem setPerm_reachableSet {S A : Finset (Config w)} {σ : Equiv.Perm {x // x ∈ S}}
    (hσ : RealizedPerm S σ) (hA : A ⊆ S) (hreach : ReachableSet A) :
    ReachableSet (setPerm S σ A) := by
  obtain ⟨m, hm, hr⟩ := hσ
  rw [setPerm_eq_imageOf hA hr]
  exact reachableSet_of_reach hreach (reach_imageOf hm)

theorem setPerm_ssubset {S A : Finset (Config w)} (σ : Equiv.Perm {x // x ∈ S})
    (hA : A ⊂ S) : setPerm S σ A ⊂ S := by
  refine Finset.ssubset_iff_of_subset (setPerm_subset σ hA.subset) |>.mpr ?_
  by_contra hcon
  push_neg at hcon
  have hsub : S ⊆ setPerm S σ A := hcon
  have hcard : S.card ≤ (setPerm S σ A).card := Finset.card_le_card hsub
  rw [setPerm_card] at hcard
  have := Finset.card_lt_card hA
  omega

/-- **Realized permutations of `S` permute its bricks.** -/
theorem setPerm_mem_bricksOf {S A : Finset (Config w)} {σ : Equiv.Perm {x // x ∈ S}}
    (hσ : RealizedPerm S σ) (hA : A ∈ bricksOf S) : setPerm S σ A ∈ bricksOf S := by
  obtain ⟨hreach, hss, hmax⟩ := mem_bricksOf.mp hA
  have hσinv : RealizedPerm S σ⁻¹ := RealizedPerm.inv hσ
  refine mem_bricksOf.mpr ⟨setPerm_reachableSet hσ hss.subset hreach,
    setPerm_ssubset σ hss, ?_⟩
  intro U hUreach hUss hsub
  have hUS : U ⊆ S := hUss.subset
  have h1 : ReachableSet (setPerm S σ⁻¹ U) := setPerm_reachableSet hσinv hUS hUreach
  have h2 : setPerm S σ⁻¹ U ⊂ S := setPerm_ssubset σ⁻¹ hUss
  have h3 : A ⊆ setPerm S σ⁻¹ U := by
    have hmono := setPerm_mono (σ := σ⁻¹) hsub
    rwa [setPerm_inv_apply] at hmono
  have h4 : setPerm S σ⁻¹ U = A := hmax _ h1 h2 h3
  have h5 : setPerm S σ (setPerm S σ⁻¹ U) = U := by
    have hone : setPerm S σ * setPerm S σ⁻¹ = 1 := by
      rw [← setPerm_mul, mul_inv_cancel, setPerm_one]
    exact congrArg (fun e : Equiv.Perm (Finset (Config w)) => e U) hone
  rw [← h4, h5]

theorem setPerm_mem_bricksOf_iff {S A : Finset (Config w)}
    {σ : Equiv.Perm {x // x ∈ S}} (hσ : RealizedPerm S σ) :
    setPerm S σ A ∈ bricksOf S ↔ A ∈ bricksOf S := by
  constructor
  · intro h
    have hb := setPerm_mem_bricksOf (RealizedPerm.inv hσ) h
    rwa [setPerm_inv_apply] at hb
  · exact setPerm_mem_bricksOf hσ

/-- The action of the realized permutations of `S` on its brick family. -/
noncomputable def bricksHom (S : Finset (Config w)) :
    realizedSubgroup S →* Equiv.Perm {A // A ∈ bricksOf S} where
  toFun σ := (setPerm S σ.val).subtypePerm
    (fun _ => setPerm_mem_bricksOf_iff (mem_realizedSubgroup.mp σ.2))
  map_one' := by
    refine Equiv.ext (fun A => Subtype.ext ?_)
    change setPerm S (1 : Equiv.Perm {x // x ∈ S}) A.val = A.val
    rw [setPerm_one]
    rfl
  map_mul' σ τ := by
    refine Equiv.ext (fun A => Subtype.ext ?_)
    change setPerm S (σ.val * τ.val) A.val = setPerm S σ.val (setPerm S τ.val A.val)
    rw [setPerm_mul]
    rfl

theorem bricksOf_subset {S A : Finset (Config w)} (hA : A ∈ bricksOf S) : A ⊆ S :=
  (mem_bricksOf.mp hA).2.1.subset

/-- If the bricks of `S` cover it, then an element realizing a permutation of
the brick family maps `S` onto `S`. -/
theorem imageOf_eq_self_of_realizedFamPerm {S : Finset (Config w)} (hS2 : 1 < S.card)
    {e : Equiv.Perm {A // A ∈ bricksOf S}} {m : TransMonoid w}
    (hr : ∀ A : {A // A ∈ bricksOf S}, (e A).val = ImageOf m A.val) :
    ImageOf m S = S := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨B, hB, hqB⟩ := exists_brick_mem hS2 hq
    have hmem : runTrans m q ∈ ImageOf m B := Finset.mem_image_of_mem _ hqB
    rw [← hr ⟨B, hB⟩] at hmem
    exact bricksOf_subset (e ⟨B, hB⟩).2 hmem
  · intro q hq
    obtain ⟨B, hB, hqB⟩ := exists_brick_mem hS2 hq
    have hBval : B = ImageOf m (e⁻¹ ⟨B, hB⟩).val := by
      have h := hr (e⁻¹ ⟨B, hB⟩)
      have h2 : e (e⁻¹ ⟨B, hB⟩) = ⟨B, hB⟩ := Equiv.apply_symm_apply e _
      rw [h2] at h
      exact h
    rw [hBval] at hqB
    obtain ⟨c, hc, hcq⟩ := Finset.mem_image.mp hqB
    have hcS : c ∈ S := bricksOf_subset (e⁻¹ ⟨B, hB⟩).2 hc
    exact Finset.mem_image.mpr ⟨c, hcS, hcq⟩

/-- **Every realized permutation of the brick family of `S` is induced by a
realized permutation of `S` itself.** -/
theorem realizedFamSubgroup_bricksOf_le_range {S : Finset (Config w)} (hS2 : 1 < S.card) :
    realizedFamSubgroup (bricksOf S) ≤ (bricksHom S).range := by
  intro e he
  obtain ⟨m, hm, hr⟩ := mem_realizedFamSubgroup.mp he
  have himg : ImageOf m S = S := imageOf_eq_self_of_realizedFamPerm hS2 hr
  have hcardim : (S.image (runTrans m)).card = S.card := by
    have h : S.image (runTrans m) = S := himg
    rw [h]
  have hinj : Set.InjOn (runTrans m) ↑S := Finset.injOn_of_card_image_eq hcardim
  have hmaps : ∀ x : {x // x ∈ S}, runTrans m x.val ∈ S := by
    intro x
    have : runTrans m x.val ∈ ImageOf m S := Finset.mem_image_of_mem _ x.2
    rwa [himg] at this
  set g : {x // x ∈ S} → {x // x ∈ S} := fun x => ⟨runTrans m x.val, hmaps x⟩ with hg
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 : runTrans m a.val = runTrans m b.val := congrArg Subtype.val hab
    exact Subtype.ext (hinj (Finset.mem_coe.mpr a.2) (Finset.mem_coe.mpr b.2) h1)
  have hgbij : Function.Bijective g := Finite.injective_iff_bijective.mp hginj
  set σ : Equiv.Perm {x // x ∈ S} := Equiv.ofBijective g hgbij with hσdef
  have hσ : RealizedPerm S σ := ⟨m, hm, fun x => rfl⟩
  refine ⟨⟨σ, mem_realizedSubgroup.mpr hσ⟩, ?_⟩
  refine Equiv.ext (fun A => Subtype.ext ?_)
  change setPerm S σ A.val = (e A).val
  rw [setPerm_eq_imageOf (bricksOf_subset A.2) (fun x => rfl), hr A]

theorem bricksOf_eq_empty_of_card_le_one {S : Finset (Config w)} (hS : S.card ≤ 1) :
    bricksOf S = ∅ := by
  refine Finset.eq_empty_of_forall_notMem (fun T hT => ?_)
  obtain ⟨hreach, hss, -⟩ := mem_bricksOf.mp hT
  have hcard : T.card < S.card := Finset.card_lt_card hss
  have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨m, -, hm⟩ := hreach
  rw [hT0] at hm
  have hne : runTrans m (fun _ => false) ∈ ImageOf m (Finset.univ : Finset (Config w)) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  rw [← hm] at hne
  exact absurd hne (Finset.notMem_empty _)

end BrickAction

/- The former H2 corollary (`isCyclic_realizedFamSubgroup_bricksOf`) is
RETIRED together with H1 (2026-08-18): the local-divisor route needs neither.
The brick machinery above stays available. -/

end Holonomy
end Internal
end AllenderOQ3
