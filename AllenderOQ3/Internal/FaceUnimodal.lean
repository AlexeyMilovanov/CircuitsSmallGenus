import AllenderOQ3.Internal.MinCorner
import AllenderOQ3.Internal.CutNecklace

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Unimodality of faces at genus zero

`MinCorner` proves that every face orbit contains a min corner (a dart `d`
with `d` and `r.rotation d` both ascending) and that the number of min
corners is at least the number of faces.  Here the sandwich closes: at genus
zero, with unique source and sink, the count is exactly the face count
(`card_minCorners_eq_faceCount`), hence **every face orbit contains exactly
one min corner** (`existsUnique_minCorner_in_faceOrbit`).

The file also proves the necklace-step identity at a min corner
(`neckPerm_of_minCorner`): the first return of the face walk starting at the
reversed corner dart happens in one step, so consecutive ascending darts in a
vertex rotation are adjacent on the necklace of their transition.  This is
the local ingredient for the contiguity (grouping) obligations of
`CutNecklace`.
-/

namespace AllenderOQ3.Internal

variable {n : Nat} {c : ADRCircuit n}

/-- At genus zero with unique source and sink, the min-corner count equals
the face count: the equality case of the Euler--Morse sandwich. -/
theorem card_minCorners_eq_faceCount (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    (h_edges : ∃ u w, c.edge u w = true) :
    (Finset.univ.filter (fun d : CircuitDart c =>
      dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)).card
      = permCycleCount (facePermutation r) := by
  classical
  obtain ⟨s, hs1, hs2⟩ := hS
  obtain ⟨t, ht1, ht2⟩ := hT
  have hC : componentCount c = 1 :=
    connected_of_unique_source hP ⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩
  have hI : isolatedVertexCount c = 0 :=
    isolated_free hP ⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩ h_edges
  have h_ne_st : s ≠ t := by
    intro heq
    subst heq
    have h_iso_s : ∀ u, ¬UnderlyingAdj c s u := by
      intro u hadj
      obtain ⟨h1', _⟩ := hadj
      rcases h1' with h | h
      · have := ht1 u; rw [this] at h; contradiction
      · have := hs1 u; rw [this] at h; contradiction
    have h_iso_count : isolatedVertexCount c = 0 := hI
    unfold isolatedVertexCount at h_iso_count
    have h_mem : s ∈ Finset.univ.filter
        (fun x : Fin c.gateCount => ∀ u, ¬UnderlyingAdj c x u) := by
      simp [h_iso_s]
    have h_card_pos : 0 < (Finset.univ.filter
        (fun x : Fin c.gateCount => ∀ u, ¬UnderlyingAdj c x u)).card :=
      Finset.card_pos.mpr ⟨s, h_mem⟩
    rw [h_iso_count] at h_card_pos
    exact lt_irrefl 0 h_card_pos
  have hEuler := defect_eq_of_rotationGenus_zero (r := r) hZero
  rw [hC, hI] at hEuler
  have hMK := card_minCorners_add_switchCount_eq_edgeCount hP r
  have hFM := card_minCorners_ge_faceCount hP r
  have hKI : ∑ v : Fin c.gateCount, switchCount r v
      = (Finset.univ.filter (fun x : Fin c.gateCount =>
          ¬ IsGraphSource c x ∧ ¬ IsGraphSink c x)).card := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : Fin c.gateCount => ¬ IsGraphSource c x ∧ ¬ IsGraphSink c x)
      (fun v => switchCount r v)]
    have h1 : ∑ v ∈ Finset.univ.filter (fun x : Fin c.gateCount =>
        ¬ IsGraphSource c x ∧ ¬ IsGraphSink c x), switchCount r v
        = (Finset.univ.filter (fun x : Fin c.gateCount =>
            ¬ IsGraphSource c x ∧ ¬ IsGraphSink c x)).card := by
      have hone : ∀ v ∈ Finset.univ.filter (fun x : Fin c.gateCount =>
          ¬ IsGraphSource c x ∧ ¬ IsGraphSink c x), switchCount r v = 1 := by
        intro v hv
        rw [Finset.mem_filter] at hv
        exact switchCount_eq_one_of_internal hP ⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩
          r hZero hv.2.1 hv.2.2
      rw [Finset.sum_congr rfl hone]
      simp
    have h2 : ∑ v ∈ Finset.univ.filter (fun x : Fin c.gateCount =>
        ¬(¬ IsGraphSource c x ∧ ¬ IsGraphSink c x)), switchCount r v = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [Finset.mem_filter] at hv
      rcases not_and_or.mp hv.2 with h | h
      · exact switchCount_eq_zero_of_source r (not_not.mp h)
      · exact switchCount_eq_zero_of_sink hP r (not_not.mp h)
    rw [h1, h2, add_zero]
  have hI_eq : Finset.univ.filter (fun x : Fin c.gateCount =>
      ¬ IsGraphSource c x ∧ ¬ IsGraphSink c x)
      = Finset.univ \ ({s, t} : Finset (Fin c.gateCount)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxs, hxt⟩
      rintro (rfl | rfl)
      · exact hxs hs1
      · exact hxt ht1
    · intro hx
      exact ⟨fun h => hx (Or.inl (hs2 x h)), fun h => hx (Or.inr (ht2 x h))⟩
  have h2card : ({s, t} : Finset (Fin c.gateCount)).card = 2 :=
    Finset.card_pair h_ne_st
  have hsub : ({s, t} : Finset (Fin c.gateCount)) ⊆ Finset.univ :=
    fun x _ => Finset.mem_univ x
  have h2le : 2 ≤ c.gateCount := by
    have := Finset.card_le_card hsub
    rw [h2card, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hIV : (Finset.univ.filter (fun x : Fin c.gateCount =>
      ¬ IsGraphSource c x ∧ ¬ IsGraphSink c x)).card + 2 = c.gateCount := by
    rw [hI_eq, Finset.card_sdiff, Finset.inter_univ, h2card, Finset.card_univ,
      Fintype.card_fin]
    omega
  omega

/-- At genus zero with unique source and sink, two min corners on the same
face orbit coincide. -/
theorem minCorner_unique_in_faceOrbit (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    {d1 d2 : CircuitDart c}
    (h1 : dartIsUp d1 = true) (h1r : dartIsUp (r.rotation d1) = true)
    (h2 : dartIsUp d2 = true) (h2r : dartIsUp (r.rotation d2) = true)
    (hsame : (facePermutation r).SameCycle (r.rotation d1) (r.rotation d2)) :
    d1 = d2 := by
  classical
  have h_edges : ∃ u w, c.edge u w = true := by
    have h := h1
    rw [dartIsUp] at h
    exact ⟨d1.source, d1.target, h⟩
  let p := facePermutation r
  let M := Finset.univ.filter (fun d : CircuitDart c =>
    dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)
  let R (x y : CircuitDart c) : Prop := ∃ k : Nat, (p ^ k) x = y
  have hR : Equivalence R := by
    constructor
    · intro x; exact ⟨0, rfl⟩
    · intro x y hxy; exact perm_forwardReach_symm p hxy
    · intro x y z ⟨k1, hk1⟩ ⟨k2, hk2⟩
      exact ⟨k2 + k1, by rw [pow_add, Equiv.Perm.mul_apply, hk1, hk2]⟩
  let rank := fun y => (Fintype.equivFin (CircuitDart c) y).val
  let S := Finset.univ.filter (fun x => ∀ y, R x y → rank x ≤ rank y)
  have h_permCycle : permCycleCount p = S.card := by rfl
  let f (x : CircuitDart c) : CircuitDart c :=
    Classical.choose (exists_minCorner_in_faceOrbit hP r x)
  have hf_spec (x : CircuitDart c) :=
    Classical.choose_spec (exists_minCorner_in_faceOrbit hP r x)
  have h_img : ∀ x ∈ S, f x ∈ M := by
    intro x _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hf_spec x).1, (hf_spec x).2.1⟩
  have hrank_inj : Function.Injective rank := by
    intro a b hab
    dsimp [rank] at hab
    exact (Fintype.equivFin (CircuitDart c)).injective (Fin.ext hab)
  have h_inj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    intro x hx y hy heq
    rw [Finset.mem_filter] at hx hy
    have hc1 : p.SameCycle x (r.rotation (f x)) := (hf_spec x).2.2
    have hc2 : p.SameCycle y (r.rotation (f y)) := (hf_spec y).2.2
    have hc1' : p.SameCycle (r.rotation (f y)) x := by
      rw [← heq]
      exact hc1.symm
    have h_same : p.SameCycle x y := (hc2.trans hc1').symm
    have hxy : R x y := h_same.exists_nat_pow_eq
    exact minRep_unique hR rank hrank_inj hxy hx.2 hy.2
  have h_subset : S.image f ⊆ M := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact h_img x hx
  have hMF := card_minCorners_eq_faceCount hP hS hT r hZero h_edges
  have h_image_card : (S.image f).card = S.card :=
    Finset.card_image_of_injOn h_inj
  have h_eq_sets : S.image f = M := by
    apply Finset.eq_of_subset_of_card_le h_subset
    rw [h_image_card, ← h_permCycle]
    exact le_of_eq hMF
  have hd1M : d1 ∈ M :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h1r⟩
  have hd2M : d2 ∈ M :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, h2r⟩
  rw [← h_eq_sets] at hd1M hd2M
  obtain ⟨x1, hx1S, hfx1⟩ := Finset.mem_image.mp hd1M
  obtain ⟨x2, hx2S, hfx2⟩ := Finset.mem_image.mp hd2M
  have hc1 : p.SameCycle x1 (r.rotation d1) := by
    have h := (hf_spec x1).2.2
    rw [show Classical.choose (exists_minCorner_in_faceOrbit hP r x1) = d1
      from hfx1] at h
    exact h
  have hc2 : p.SameCycle x2 (r.rotation d2) := by
    have h := (hf_spec x2).2.2
    rw [show Classical.choose (exists_minCorner_in_faceOrbit hP r x2) = d2
      from hfx2] at h
    exact h
  have hx12 : p.SameCycle x1 x2 := (hc1.trans hsame).trans hc2.symm
  have hR12 : R x1 x2 := hx12.exists_nat_pow_eq
  rw [Finset.mem_filter] at hx1S hx2S
  have hx_eq : x1 = x2 := minRep_unique hR rank hrank_inj hR12 hx1S.2 hx2S.2
  rw [← hfx1, ← hfx2, hx_eq]

/-- Every face orbit contains exactly one min corner. -/
theorem existsUnique_minCorner_in_faceOrbit (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    (d0 : CircuitDart c) :
    ∃! d : CircuitDart c, dartIsUp d = true ∧ dartIsUp (r.rotation d) = true ∧
      (facePermutation r).SameCycle d0 (r.rotation d) := by
  obtain ⟨d, hd1, hd2, hd3⟩ := exists_minCorner_in_faceOrbit hP r d0
  refine ⟨d, ⟨hd1, hd2, hd3⟩, ?_⟩
  rintro d' ⟨h1', h2', h3'⟩
  exact minCorner_unique_in_faceOrbit hP hS hT r hZero h1' h2' hd1 hd2
    (h3'.symm.trans hd3)

/-! ## The necklace step at a min corner -/

/-- The reverse of an ascending dart is a cut dart of its source layer. -/
theorem revDart_cut_of_up (hP : ProperLayered c) (d : CircuitDart c)
    (h1 : dartIsUp d = true) :
    isCutDart c (c.layer d.source) (dartReverse c d) = true := by
  rw [isCutDart, beq_iff_eq]
  have hup := layer_of_dartIsUp hP d h1
  have hsrc : (dartReverse c d).source = d.target := rfl
  have htgt : (dartReverse c d).target = d.source := rfl
  rw [hsrc, htgt]
  omega

/-- The rotation successor at a min corner is a cut dart of the same layer. -/
theorem rotDart_cut_of_corner (hP : ProperLayered c) (r : OrientableRotation c)
    (d : CircuitDart c) (h2 : dartIsUp (r.rotation d) = true) :
    isCutDart c (c.layer d.source) (r.rotation d) = true := by
  have hs := r.preservesSource d
  rw [isCutDart, beq_iff_eq, hs]
  have hup := layer_of_dartIsUp hP (r.rotation d) h2
  rw [hs] at hup
  omega

/-- At a min corner the face walk from the reversed dart returns to the cut
in a single step, landing on the rotation successor. -/
theorem firstReturn_of_minCorner (hP : ProperLayered c)
    (r : OrientableRotation c) (d : CircuitDart c)
    (h1 : dartIsUp d = true) (h2 : dartIsUp (r.rotation d) = true) :
    (firstReturn r (c.layer d.source))
        ⟨dartReverse c d, revDart_cut_of_up hP d h1⟩
      = ⟨r.rotation d, rotDart_cut_of_corner hP r d h2⟩ := by
  have hrr : (dartReverse c) ((dartReverse c) d) = d :=
    (dartReverse c).left_inv d
  have hstep : facePermutation r (dartReverse c d) = r.rotation d := by
    have h : facePermutation r (dartReverse c d)
        = r.rotation ((dartReverse c) ((dartReverse c) d)) := rfl
    rw [h, hrr]
  have hT : firstReturnTime (facePermutation r)
      (fun dd => isCutDart c (c.layer d.source) dd = true)
      ⟨dartReverse c d, revDart_cut_of_up hP d h1⟩ = 1 := by
    rw [firstReturnTime, Nat.find_eq_iff]
    constructor
    · refine ⟨le_refl 1, ?_⟩
      change isCutDart c (c.layer d.source)
        ((facePermutation r ^ 1) (dartReverse c d)) = true
      rw [pow_one, hstep]
      exact rotDart_cut_of_corner hP r d h2
    · intro k hk hcontra
      exact absurd hcontra.1 (by omega)
  apply Subtype.ext
  rw [firstReturn_val, hT, pow_one]
  exact hstep

/-- The necklace step at a min corner: consecutive ascending darts of a
vertex rotation are necklace-adjacent (on the descending side) on the
transition of their source layer. -/
theorem neckPerm_of_minCorner (hP : ProperLayered c)
    (r : OrientableRotation c) (d : CircuitDart c)
    (h1 : dartIsUp d = true) (h2 : dartIsUp (r.rotation d) = true) :
    (neckPerm r (c.layer d.source))
        ⟨dartReverse c d, revDart_cut_of_up hP d h1⟩
      = (cutDartReverse c (c.layer d.source))
          ⟨r.rotation d, rotDart_cut_of_corner hP r d h2⟩ := by
  change (cutDartReverse c (c.layer d.source))
      ((firstReturn r (c.layer d.source))
        ⟨dartReverse c d, revDart_cut_of_up hP d h1⟩) = _
  rw [firstReturn_of_minCorner hP r d h1 h2]

/-! ## The necklace step at a max corner

A max corner is a dart `d` with `d` and `r.rotation d` both descending: the
corner between two consecutive incoming darts of the common source vertex.
The same one-step argument as for min corners shows that the face walk from
the reversed dart crosses the cut of the layer *below* the vertex in a single
step.  This is the local adjacency of the incoming fibers on the necklace. -/

/-- The reverse of a descending dart is a cut dart of its target layer. -/
theorem revDart_cut_of_down (hP : ProperLayered c) (d : CircuitDart c)
    (h1 : dartIsUp d = false) :
    isCutDart c (c.layer d.target) (dartReverse c d) = true := by
  rw [isCutDart, beq_iff_eq]
  have hdown := layer_of_not_dartIsUp hP d h1
  have hsrc : (dartReverse c d).source = d.target := rfl
  have htgt : (dartReverse c d).target = d.source := rfl
  rw [hsrc, htgt]
  omega

/-- The rotation successor at a max corner is a cut dart of the layer below
the common source vertex. -/
theorem rotDart_cut_of_maxCorner (hP : ProperLayered c)
    (r : OrientableRotation c) (d : CircuitDart c)
    (h1 : dartIsUp d = false) (h2 : dartIsUp (r.rotation d) = false) :
    isCutDart c (c.layer d.target) (r.rotation d) = true := by
  have hs := r.preservesSource d
  rw [isCutDart, beq_iff_eq, hs]
  have hd := layer_of_not_dartIsUp hP d h1
  have hdown := layer_of_not_dartIsUp hP (r.rotation d) h2
  rw [hs] at hdown
  omega

/-- At a max corner the face walk from the reversed dart returns to the cut
below the corner vertex in a single step, landing on the rotation
successor. -/
theorem firstReturn_of_maxCorner (hP : ProperLayered c)
    (r : OrientableRotation c) (d : CircuitDart c)
    (h1 : dartIsUp d = false) (h2 : dartIsUp (r.rotation d) = false) :
    (firstReturn r (c.layer d.target))
        ⟨dartReverse c d, revDart_cut_of_down hP d h1⟩
      = ⟨r.rotation d, rotDart_cut_of_maxCorner hP r d h1 h2⟩ := by
  have hrr : (dartReverse c) ((dartReverse c) d) = d :=
    (dartReverse c).left_inv d
  have hstep : facePermutation r (dartReverse c d) = r.rotation d := by
    have h : facePermutation r (dartReverse c d)
        = r.rotation ((dartReverse c) ((dartReverse c) d)) := rfl
    rw [h, hrr]
  have hT : firstReturnTime (facePermutation r)
      (fun dd => isCutDart c (c.layer d.target) dd = true)
      ⟨dartReverse c d, revDart_cut_of_down hP d h1⟩ = 1 := by
    rw [firstReturnTime, Nat.find_eq_iff]
    constructor
    · refine ⟨le_refl 1, ?_⟩
      change isCutDart c (c.layer d.target)
        ((facePermutation r ^ 1) (dartReverse c d)) = true
      rw [pow_one, hstep]
      exact rotDart_cut_of_maxCorner hP r d h1 h2
    · intro k hk hcontra
      exact absurd hcontra.1 (by omega)
  apply Subtype.ext
  rw [firstReturn_val, hT, pow_one]
  exact hstep

/-- The necklace step at a max corner: consecutive descending darts of a
vertex rotation are necklace-adjacent (on the ascending side) on the
transition below their source vertex. -/
theorem neckPerm_of_maxCorner (hP : ProperLayered c)
    (r : OrientableRotation c) (d : CircuitDart c)
    (h1 : dartIsUp d = false) (h2 : dartIsUp (r.rotation d) = false) :
    (neckPerm r (c.layer d.target))
        ⟨dartReverse c d, revDart_cut_of_down hP d h1⟩
      = (cutDartReverse c (c.layer d.target))
          ⟨r.rotation d, rotDart_cut_of_maxCorner hP r d h1 h2⟩ := by
  change (cutDartReverse c (c.layer d.target))
      ((firstReturn r (c.layer d.target))
        ⟨dartReverse c d, revDart_cut_of_down hP d h1⟩) = _
  rw [firstReturn_of_maxCorner hP r d h1 h2]

/-! ## Max corners: the count

The descending mirror of the min-corner count.  The number of max corners
(darts `d` with `d` and `r.rotation d` both descending) equals the number of
min corners; no cyclic decomposition is needed, only the bijection `d ↦
r.rotation d` and inclusion–exclusion over the up/down split. -/

theorem card_up_next_split (r : OrientableRotation c) :
    (Finset.univ.filter (fun d : CircuitDart c =>
        dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)).card
      + (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp d = true ∧ dartIsUp (r.rotation d) = false)).card
      = (Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true)).card := by
  classical
  have h_union :
      Finset.univ.filter (fun d : CircuitDart c =>
        dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)
      ∪ Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp d = true ∧ dartIsUp (r.rotation d) = false)
      = Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases h : dartIsUp (r.rotation d) <;> simp
  have h_disj :
      Disjoint
        (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp d = true ∧ dartIsUp (r.rotation d) = true))
        (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp d = true ∧ dartIsUp (r.rotation d) = false)) := by
    rw [Finset.disjoint_filter]
    intro d _ h1 h2
    rw [h1.2] at h2
    exact absurd h2.2 (by simp)
  rw [← Finset.card_union_of_disjoint h_disj, h_union]

theorem card_down_next_split (r : OrientableRotation c) :
    (Finset.univ.filter (fun d : CircuitDart c =>
        dartIsUp d = false ∧ dartIsUp (r.rotation d) = false)).card
      + (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp d = false ∧ dartIsUp (r.rotation d) = true)).card
      = (Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = false)).card := by
  classical
  have h_union :
      Finset.univ.filter (fun d : CircuitDart c =>
        dartIsUp d = false ∧ dartIsUp (r.rotation d) = false)
      ∪ Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp d = false ∧ dartIsUp (r.rotation d) = true)
      = Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = false) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases h : dartIsUp (r.rotation d) <;> simp
  have h_disj :
      Disjoint
        (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp d = false ∧ dartIsUp (r.rotation d) = false))
        (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp d = false ∧ dartIsUp (r.rotation d) = true)) := by
    rw [Finset.disjoint_filter]
    intro d _ h1 h2
    rw [h1.2] at h2
    exact absurd h2.2 (by simp)
  rw [← Finset.card_union_of_disjoint h_disj, h_union]

theorem card_up_prev_split (r : OrientableRotation c) :
    (Finset.univ.filter (fun d : CircuitDart c =>
        dartIsUp (r.rotation.symm d) = true ∧ dartIsUp d = true)).card
      + (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp (r.rotation.symm d) = false ∧ dartIsUp d = true)).card
      = (Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true)).card := by
  classical
  have h_union :
      Finset.univ.filter (fun d : CircuitDart c =>
        dartIsUp (r.rotation.symm d) = true ∧ dartIsUp d = true)
      ∪ Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp (r.rotation.symm d) = false ∧ dartIsUp d = true)
      = Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases h : dartIsUp (r.rotation.symm d) <;> simp
  have h_disj :
      Disjoint
        (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp (r.rotation.symm d) = true ∧ dartIsUp d = true))
        (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp (r.rotation.symm d) = false ∧ dartIsUp d = true)) := by
    rw [Finset.disjoint_filter]
    intro d _ h1 h2
    rw [h1.1] at h2
    exact absurd h2.1 (by simp)
  rw [← Finset.card_union_of_disjoint h_disj, h_union]

theorem card_minCorner_shift (r : OrientableRotation c) :
    (Finset.univ.filter (fun d : CircuitDart c =>
        dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)).card
      = (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp (r.rotation.symm d) = true ∧ dartIsUp d = true)).card := by
  classical
  refine Finset.card_bij (fun d _ => r.rotation d) ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd ⊢
    refine ⟨Finset.mem_univ _, ?_, hd.2.2⟩
    rw [Equiv.symm_apply_apply]
    exact hd.2.1
  · intro d1 h1 d2 h2 h
    exact r.rotation.injective h
  · intro y hy
    rw [Finset.mem_filter] at hy
    refine ⟨r.rotation.symm y, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hy.2.1, ?_⟩
      rw [Equiv.apply_symm_apply]
      exact hy.2.2
    · exact r.rotation.apply_symm_apply y

theorem card_downUp_shift (r : OrientableRotation c) :
    (Finset.univ.filter (fun d : CircuitDart c =>
        dartIsUp d = false ∧ dartIsUp (r.rotation d) = true)).card
      = (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp (r.rotation.symm d) = false ∧ dartIsUp d = true)).card := by
  classical
  refine Finset.card_bij (fun d _ => r.rotation d) ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd ⊢
    refine ⟨Finset.mem_univ _, ?_, hd.2.2⟩
    rw [Equiv.symm_apply_apply]
    exact hd.2.1
  · intro d1 h1 d2 h2 h
    exact r.rotation.injective h
  · intro y hy
    rw [Finset.mem_filter] at hy
    refine ⟨r.rotation.symm y, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hy.2.1, ?_⟩
      rw [Equiv.apply_symm_apply]
      exact hy.2.2
    · exact r.rotation.apply_symm_apply y

/-- The number of max corners equals the number of min corners. -/
theorem card_maxCorners_eq_minCorners (hP : ProperLayered c)
    (r : OrientableRotation c) :
    (Finset.univ.filter (fun d : CircuitDart c =>
        dartIsUp d = false ∧ dartIsUp (r.rotation d) = false)).card
      = (Finset.univ.filter (fun d : CircuitDart c =>
          dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)).card := by
  have h1 := card_up_next_split r
  have h2 := card_down_next_split r
  have h3 := card_up_prev_split r
  have h4 := card_minCorner_shift r
  have h5 := card_downUp_shift r
  have h6 := card_upDarts_eq_card_downDarts hP
  omega

/-- At genus zero with unique source and sink, the max-corner count also
equals the face count. -/
theorem card_maxCorners_eq_faceCount (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    (h_edges : ∃ u w, c.edge u w = true) :
    (Finset.univ.filter (fun d : CircuitDart c =>
      dartIsUp d = false ∧ dartIsUp (r.rotation d) = false)).card
      = permCycleCount (facePermutation r) := by
  rw [card_maxCorners_eq_minCorners hP r]
  exact card_minCorners_eq_faceCount hP hS hT r hZero h_edges

/-- Every face orbit contains a max corner: a dart `d` with `d` and
`r.rotation d` both descending and `r.rotation d` on the orbit. -/
theorem exists_maxCorner_in_faceOrbit (hP : ProperLayered c)
    (r : OrientableRotation c) (d0 : CircuitDart c) :
    ∃ d : CircuitDart c, dartIsUp d = false ∧ dartIsUp (r.rotation d) = false ∧
      (facePermutation r).SameCycle d0 (r.rotation d) := by
  classical
  let p := facePermutation r
  let S : CircuitDart c → Prop := fun x => p.SameCycle d0 x
  have hS : ∀ x, S (p x) ↔ S x := by
    intro x
    unfold S
    exact Equiv.Perm.sameCycle_apply_right
  let p_restr := p.subtypePerm hS
  have hcyc : ∀ x y : { x // S x }, ∃ k : Nat, (p_restr ^ k) x = y := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    have hxy : p.SameCycle x y := hx.symm.trans hy
    obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
    use k
    apply Subtype.ext
    rw [Equiv.Perm.subtypePerm_pow]
    exact hk
  let pred : { x // S x } → Bool := fun x => dartIsUp x.1
  have hup := faceOrbit_has_up_and_down hP r d0
  obtain ⟨k_up, hk_up⟩ := hup.1
  obtain ⟨k_down, hk_down⟩ := hup.2
  have hd_up : S ((p ^ k_up) d0) := ⟨(k_up : ℤ), rfl⟩
  have hd_down : S ((p ^ k_down) d0) := ⟨(k_down : ℤ), rfl⟩
  have ha : pred ⟨(p ^ k_up) d0, hd_up⟩ = true := hk_up
  have hb : pred ⟨(p ^ k_down) d0, hd_down⟩ = false := hk_down
  obtain ⟨x, hx1, hx2⟩ := exists_switch_of_cycle p_restr hcyc pred ha hb
  refine ⟨dartReverse c x.1, ?_, ?_, ?_⟩
  · have hx1' : dartIsUp x.1 = true := hx1
    rw [dartIsUp_dartReverse hP, hx1']
    rfl
  · have hval : r.rotation (dartReverse c x.1) = p x.1 := rfl
    rw [hval]
    have hpx : ((p_restr x) : CircuitDart c) = p x.1 := rfl
    rw [← hpx]
    exact hx2
  · have hval : r.rotation (dartReverse c x.1) = p x.1 := rfl
    rw [hval]
    exact x.2.trans (Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl)

/-- At genus zero with unique source and sink, two max corners on the same
face orbit coincide. -/
theorem maxCorner_unique_in_faceOrbit (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    (h_edges : ∃ u w, c.edge u w = true)
    {d1 d2 : CircuitDart c}
    (h1 : dartIsUp d1 = false) (h1r : dartIsUp (r.rotation d1) = false)
    (h2 : dartIsUp d2 = false) (h2r : dartIsUp (r.rotation d2) = false)
    (hsame : (facePermutation r).SameCycle (r.rotation d1) (r.rotation d2)) :
    d1 = d2 := by
  classical
  let p := facePermutation r
  let M := Finset.univ.filter (fun d : CircuitDart c =>
    dartIsUp d = false ∧ dartIsUp (r.rotation d) = false)
  let R (x y : CircuitDart c) : Prop := ∃ k : Nat, (p ^ k) x = y
  have hR : Equivalence R := by
    constructor
    · intro x; exact ⟨0, rfl⟩
    · intro x y hxy; exact perm_forwardReach_symm p hxy
    · intro x y z ⟨k1, hk1⟩ ⟨k2, hk2⟩
      exact ⟨k2 + k1, by rw [pow_add, Equiv.Perm.mul_apply, hk1, hk2]⟩
  let rank := fun y => (Fintype.equivFin (CircuitDart c) y).val
  let S := Finset.univ.filter (fun x => ∀ y, R x y → rank x ≤ rank y)
  have h_permCycle : permCycleCount p = S.card := by rfl
  let f (x : CircuitDart c) : CircuitDart c :=
    Classical.choose (exists_maxCorner_in_faceOrbit hP r x)
  have hf_spec (x : CircuitDart c) :=
    Classical.choose_spec (exists_maxCorner_in_faceOrbit hP r x)
  have h_img : ∀ x ∈ S, f x ∈ M := by
    intro x _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hf_spec x).1, (hf_spec x).2.1⟩
  have hrank_inj : Function.Injective rank := by
    intro a b hab
    dsimp [rank] at hab
    exact (Fintype.equivFin (CircuitDart c)).injective (Fin.ext hab)
  have h_inj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    intro x hx y hy heq
    rw [Finset.mem_filter] at hx hy
    have hc1 : p.SameCycle x (r.rotation (f x)) := (hf_spec x).2.2
    have hc2 : p.SameCycle y (r.rotation (f y)) := (hf_spec y).2.2
    have hc1' : p.SameCycle (r.rotation (f y)) x := by
      rw [← heq]
      exact hc1.symm
    have h_same : p.SameCycle x y := (hc2.trans hc1').symm
    have hxy : R x y := h_same.exists_nat_pow_eq
    exact minRep_unique hR rank hrank_inj hxy hx.2 hy.2
  have h_subset : S.image f ⊆ M := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact h_img x hx
  have hMF := card_maxCorners_eq_faceCount hP hS hT r hZero h_edges
  have h_image_card : (S.image f).card = S.card :=
    Finset.card_image_of_injOn h_inj
  have h_eq_sets : S.image f = M := by
    apply Finset.eq_of_subset_of_card_le h_subset
    rw [h_image_card, ← h_permCycle]
    exact le_of_eq hMF
  have hd1M : d1 ∈ M :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h1r⟩
  have hd2M : d2 ∈ M :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, h2r⟩
  rw [← h_eq_sets] at hd1M hd2M
  obtain ⟨x1, hx1S, hfx1⟩ := Finset.mem_image.mp hd1M
  obtain ⟨x2, hx2S, hfx2⟩ := Finset.mem_image.mp hd2M
  have hc1 : p.SameCycle x1 (r.rotation d1) := by
    have h := (hf_spec x1).2.2
    rw [show Classical.choose (exists_maxCorner_in_faceOrbit hP r x1) = d1
      from hfx1] at h
    exact h
  have hc2 : p.SameCycle x2 (r.rotation d2) := by
    have h := (hf_spec x2).2.2
    rw [show Classical.choose (exists_maxCorner_in_faceOrbit hP r x2) = d2
      from hfx2] at h
    exact h
  have hx12 : p.SameCycle x1 x2 := (hc1.trans hsame).trans hc2.symm
  have hR12 : R x1 x2 := hx12.exists_nat_pow_eq
  rw [Finset.mem_filter] at hx1S hx2S
  have hx_eq : x1 = x2 := minRep_unique hR rank hrank_inj hR12 hx1S.2 hx2S.2
  rw [← hfx1, ← hfx2, hx_eq]

/-- Every face orbit contains exactly one max corner. -/
theorem existsUnique_maxCorner_in_faceOrbit (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    (h_edges : ∃ u w, c.edge u w = true) (d0 : CircuitDart c) :
    ∃! d : CircuitDart c, dartIsUp d = false ∧ dartIsUp (r.rotation d) = false ∧
      (facePermutation r).SameCycle d0 (r.rotation d) := by
  obtain ⟨d, hd1, hd2, hd3⟩ := exists_maxCorner_in_faceOrbit hP r d0
  refine ⟨d, ⟨hd1, hd2, hd3⟩, ?_⟩
  rintro d' ⟨h1', h2', h3'⟩
  exact maxCorner_unique_in_faceOrbit hP hS hT r hZero h_edges h1' h2' hd1 hd2
    (h3'.symm.trans hd3)

end AllenderOQ3.Internal
