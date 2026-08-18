import AllenderOQ3.Internal.MinCorner

set_option autoImplicit false

/-!
# Down–up corners at a vertex

`switchCount r v` counts the *up→down* corners of the rotation at `v`: the
out-darts `d` of `v` that ascend while `r.rotation d` descends.  The mirror
count is the number of *down→up* corners, `downUpCount r v`.  On a cyclic
rotation the two are equal (`downUpCount_eq_switchCount`); the proof is the
per-vertex form of the inclusion–exclusion used in `FaceUnimodal` for the
global corner counts, and needs no planarity.

Combined with `switchCount_eq_one_of_internal` this gives the bimodality of a
genus-zero rotation at a vertex in the form used by the necklace argument: a
vertex that is not the graph source has **at most one** down→up corner
(`downUpCount_le_one`), i.e. its incoming darts occupy one cyclic block.
-/

namespace AllenderOQ3.Internal

variable {n : Nat} {c : ADRCircuit n}

/-- The number of *down→up* corners of the rotation `r` at the vertex `v`. -/
noncomputable def downUpCount (r : OrientableRotation c) (v : Fin c.gateCount) :
    Nat := by
  classical
  exact (Finset.univ.filter fun d : CircuitDart c =>
    d.source = v ∧ dartIsUp d = false ∧ dartIsUp (r.rotation d) = true).card

/-- **The two corner counts at a vertex agree.** -/
theorem downUpCount_eq_switchCount (r : OrientableRotation c)
    (v : Fin c.gateCount) : downUpCount r v = switchCount r v := by
  classical
  set A := Finset.univ.filter (fun d : CircuitDart c =>
    d.source = v ∧ dartIsUp d = true ∧ dartIsUp (r.rotation d) = true) with hA
  set B := Finset.univ.filter (fun d : CircuitDart c =>
    d.source = v ∧ dartIsUp d = true ∧ dartIsUp (r.rotation d) = false) with hB
  set C := Finset.univ.filter (fun d : CircuitDart c =>
    d.source = v ∧ dartIsUp d = false ∧ dartIsUp (r.rotation d) = true) with hC
  set A' := Finset.univ.filter (fun d : CircuitDart c =>
    d.source = v ∧ dartIsUp (r.rotation.symm d) = true ∧ dartIsUp d = true) with hA'
  set C' := Finset.univ.filter (fun d : CircuitDart c =>
    d.source = v ∧ dartIsUp (r.rotation.symm d) = false ∧ dartIsUp d = true) with hC'
  set U := Finset.univ.filter (fun d : CircuitDart c =>
    d.source = v ∧ dartIsUp d = true) with hU
  have hsplit1 : A.card + B.card = U.card := by
    have hunion : A ∪ B = U := by
      ext d
      simp only [hA, hB, hU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      cases h : dartIsUp (r.rotation d) <;> simp
    have hdisj : Disjoint A B := by
      rw [hA, hB, Finset.disjoint_filter]
      intro d _ h1 h2
      rw [h1.2.2] at h2
      exact absurd h2.2.2 (by simp)
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hsplit2 : A'.card + C'.card = U.card := by
    have hunion : A' ∪ C' = U := by
      ext d
      simp only [hA', hC', hU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      cases h : dartIsUp (r.rotation.symm d) <;> simp
    have hdisj : Disjoint A' C' := by
      rw [hA', hC', Finset.disjoint_filter]
      intro d _ h1 h2
      rw [h1.2.1] at h2
      exact absurd h2.2.1 (by simp)
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hshiftA : A.card = A'.card := by
    refine Finset.card_bij (fun d _ => r.rotation d) ?_ ?_ ?_
    · intro d hd
      rw [hA, Finset.mem_filter] at hd
      rw [hA', Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_, hd.2.2.2⟩
      · rw [r.preservesSource]; exact hd.2.1
      · rw [Equiv.symm_apply_apply]; exact hd.2.2.1
    · intro d1 _ d2 _ h
      exact r.rotation.injective h
    · intro y hy
      rw [hA', Finset.mem_filter] at hy
      refine ⟨r.rotation.symm y, ?_, r.rotation.apply_symm_apply y⟩
      rw [hA, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hy.2.2.1, ?_⟩
      · rw [← r.preservesSource (r.rotation.symm y), r.rotation.apply_symm_apply]
        exact hy.2.1
      · rw [Equiv.apply_symm_apply]; exact hy.2.2.2
  have hshiftC : C.card = C'.card := by
    refine Finset.card_bij (fun d _ => r.rotation d) ?_ ?_ ?_
    · intro d hd
      rw [hC, Finset.mem_filter] at hd
      rw [hC', Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_, hd.2.2.2⟩
      · rw [r.preservesSource]; exact hd.2.1
      · rw [Equiv.symm_apply_apply]; exact hd.2.2.1
    · intro d1 _ d2 _ h
      exact r.rotation.injective h
    · intro y hy
      rw [hC', Finset.mem_filter] at hy
      refine ⟨r.rotation.symm y, ?_, r.rotation.apply_symm_apply y⟩
      rw [hC, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hy.2.2.1, ?_⟩
      · rw [← r.preservesSource (r.rotation.symm y), r.rotation.apply_symm_apply]
        exact hy.2.1
      · rw [Equiv.apply_symm_apply]; exact hy.2.2.2
  have hBs : B.card = switchCount r v := rfl
  have hCd : C.card = downUpCount r v := rfl
  omega

/-- At the graph source every dart ascends, so there is no down→up corner. -/
theorem downUpCount_eq_zero_of_source (r : OrientableRotation c)
    {v : Fin c.gateCount} (hs : IsGraphSource c v) : downUpCount r v = 0 := by
  classical
  rw [downUpCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro d - ⟨hdv, hdown, -⟩
  have hup : dartIsUp d = true := by
    rcases d.property.1 with he | he
    · exact he
    · exfalso
      have hd : (d.1).1 = v := hdv
      rw [hd, hs (d.1).2] at he
      exact absurd he (by simp)
  rw [hup] at hdown
  exact absurd hdown (by simp)

/-- **Every vertex carries at most one down→up corner** at a genus-zero
rotation: its incoming darts form a single cyclic block of the rotation. -/
theorem downUpCount_le_one (hpl : ProperLayered c)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hg : rotationGenus r = 0)
    (v : Fin c.gateCount) :
    downUpCount r v ≤ 1 := by
  by_cases hns : IsGraphSource c v
  · rw [downUpCount_eq_zero_of_source r hns]
    omega
  rw [downUpCount_eq_switchCount]
  by_cases hnt : IsGraphSink c v
  · rw [switchCount_eq_zero_of_sink hpl r hnt]
    omega
  · rw [switchCount_eq_one_of_internal hpl hsrc hsnk r hg hns hnt]

/-- The unique down→up corner: two down-darts of `v` whose rotation successors
ascend are equal. -/
theorem downUp_corner_unique (hpl : ProperLayered c)
    (hsrc : ∃! s, IsGraphSource c s) (hsnk : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hg : rotationGenus r = 0)
    {v : Fin c.gateCount}
    {d1 d2 : CircuitDart c}
    (hs1 : d1.source = v) (hd1 : dartIsUp d1 = false)
    (hr1 : dartIsUp (r.rotation d1) = true)
    (hs2 : d2.source = v) (hd2 : dartIsUp d2 = false)
    (hr2 : dartIsUp (r.rotation d2) = true) :
    d1 = d2 := by
  classical
  have hle := downUpCount_le_one hpl hsrc hsnk r hg v
  rw [downUpCount] at hle
  refine Finset.card_le_one.mp hle d1 ?_ d2 ?_ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · exact ⟨hs1, hd1, hr1⟩
  · exact ⟨hs2, hd2, hr2⟩

end AllenderOQ3.Internal
