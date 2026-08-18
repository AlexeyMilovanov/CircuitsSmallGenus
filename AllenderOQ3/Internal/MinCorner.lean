import AllenderOQ3.Internal.StGraph
import AllenderOQ3.Internal.EulerDefect
import AllenderOQ3.Internal.DartSwitch
import AllenderOQ3.Internal.OrbitCount

set_option autoImplicit false
set_option linter.unusedVariables false

namespace AllenderOQ3.Internal

variable {n : Nat} {c : ADRCircuit n}

theorem source_facePermutation (r : OrientableRotation c) (d : CircuitDart c) :
    (facePermutation r d).source = d.target := by
  dsimp [facePermutation]
  rw [r.preservesSource]
  rfl

/-- On any face orbit, there is an up-dart and a down-dart. -/
theorem faceOrbit_has_up_and_down (hP : ProperLayered c) (r : OrientableRotation c)
    (d : CircuitDart c) :
    (∃ k : Nat, dartIsUp ((facePermutation r ^ k) d) = true) ∧
    (∃ k : Nat, dartIsUp ((facePermutation r ^ k) d) = false) := by
  classical
  let p := facePermutation r
  let orbit := Finset.univ.filter (fun x => p.SameCycle d x)
  have h_orbit : orbit.Nonempty := by
    use d
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.rfl⟩
  obtain ⟨max_d, hmax_in, hmax_le⟩ := Finset.exists_max_image orbit (fun x => c.layer x.source) h_orbit
  obtain ⟨min_d, hmin_in, hmin_le⟩ := Finset.exists_min_image orbit (fun x => c.layer x.source) h_orbit
  
  have h_max_next : p max_d ∈ orbit := by
    rw [Finset.mem_filter] at hmax_in ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    exact hmax_in.2.trans (Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl)
  have h_min_next : p min_d ∈ orbit := by
    rw [Finset.mem_filter] at hmin_in ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    exact hmin_in.2.trans (Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl)
    
  have hl_max := hmax_le (p max_d) h_max_next
  have hl_min := hmin_le (p min_d) h_min_next
  rw [source_facePermutation] at hl_max hl_min
  
  constructor
  · obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hmin_in).2.exists_nat_pow_eq
    use k
    cases h : dartIsUp min_d
    · have h_down := layer_of_not_dartIsUp hP min_d h
      omega
    · rw [← hk] at h
      exact h
  · obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hmax_in).2.exists_nat_pow_eq
    use k
    cases h : dartIsUp max_d
    · rw [← hk] at h
      exact h
    · have h_up := layer_of_dartIsUp hP max_d h
      omega

/-- Every face orbit contains a dart `d` with `dartIsUp d ∧ dartIsUp (r.rotation d)` and `r.rotation d` in that orbit. -/
theorem exists_minCorner_in_faceOrbit (hP : ProperLayered c) (r : OrientableRotation c)
    (d0 : CircuitDart c) :
    ∃ d : CircuitDart c, dartIsUp d = true ∧ dartIsUp (r.rotation d) = true ∧
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

  let pred : { x // S x } → Bool := fun x => !(dartIsUp x.1)
  have hup := faceOrbit_has_up_and_down hP r d0
  obtain ⟨k_up, hk_up⟩ := hup.1
  obtain ⟨k_down, hk_down⟩ := hup.2
  
  have hd_up : S ((p ^ k_up) d0) := ⟨(k_up : ℤ), rfl⟩
  have hd_down : S ((p ^ k_down) d0) := ⟨(k_down : ℤ), rfl⟩
  
  have ha : pred ⟨(p ^ k_down) d0, hd_down⟩ = true := by
    dsimp [pred]
    rw [hk_down]
    rfl
  have hb : pred ⟨(p ^ k_up) d0, hd_up⟩ = false := by
    dsimp [pred]
    rw [hk_up]
    rfl
    
  obtain ⟨x, hx1, hx2⟩ := exists_switch_of_cycle p_restr hcyc pred ha hb
  use dartReverse c x.1
  have hd_up_x : dartIsUp (dartReverse c x.1) = true := by
    have h1 : dartIsUp x.1 = false := by
      revert hx1
      dsimp [pred]
      cases dartIsUp x.1
      · intro _
        rfl
      · intro hcon
        contradiction
    rw [dartIsUp_dartReverse hP, h1]
    rfl
  have h_rot : dartIsUp (r.rotation (dartReverse c x.1)) = true := by
    have h2 : dartIsUp (p x.1) = true := by
      revert hx2
      dsimp [pred]
      have : (p_restr x).1 = p x.1 := rfl
      rw [this]
      cases dartIsUp (p x.1)
      · intro hcon
        contradiction
      · intro _
        rfl
    exact h2
  refine ⟨hd_up_x, h_rot, ?_⟩
  have : r.rotation (dartReverse c x.1) = p x.1 := rfl
  rw [this]
  exact x.2.trans (Equiv.Perm.sameCycle_apply_right.mpr Equiv.Perm.SameCycle.rfl)

theorem card_minCorners_ge_faceCount (hP : ProperLayered c) (r : OrientableRotation c) :
    permCycleCount (facePermutation r) ≤
    (Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)).card := by
  classical
  let p := facePermutation r
  let M := Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)
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
  let f (x : CircuitDart c) : CircuitDart c := Classical.choose (exists_minCorner_in_faceOrbit hP r x)
  have hf_spec (x : CircuitDart c) := Classical.choose_spec (exists_minCorner_in_faceOrbit hP r x)
  have h_img : ∀ x ∈ S, f x ∈ M := by
    intro x _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hf_spec x).1, (hf_spec x).2.1⟩
  have h_inj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    intro x hx y hy heq
    rw [Finset.mem_filter] at hx hy
    have h1 : p.SameCycle x (r.rotation (f x)) := (hf_spec x).2.2
    have h2 : p.SameCycle y (r.rotation (f y)) := (hf_spec y).2.2
    have h1_symm : p.SameCycle (r.rotation (f x)) x := Equiv.Perm.SameCycle.symm h1
    have h1_symm' : p.SameCycle (r.rotation (f y)) x := by
      rw [← heq]
      exact h1_symm
    have h_same : p.SameCycle x y := Equiv.Perm.SameCycle.symm (Equiv.Perm.SameCycle.trans h2 h1_symm')
    have hxy : R x y := h_same.exists_nat_pow_eq
    have hrank_inj : Function.Injective rank := by
      intro a b hab
      dsimp [rank] at hab
      exact (Fintype.equivFin (CircuitDart c)).injective (Fin.ext hab)
    exact minRep_unique hR rank hrank_inj hxy hx.2 hy.2
  have h_le := Finset.card_image_of_injOn h_inj
  rw [h_permCycle, ← h_le]
  have h_subset : S.image f ⊆ M := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact h_img x hx
  exact Finset.card_le_card h_subset

theorem sum_switchCount_eq (r : OrientableRotation c) :
    ∑ v : Fin c.gateCount, switchCount r v =
    (Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true ∧ dartIsUp (r.rotation d) = false)).card := by
  classical
  let T := Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true ∧ dartIsUp (r.rotation d) = false)
  have h_biUnion : T = Finset.univ.biUnion (fun v => T.filter (fun d => d.source = v)) := by
    ext d
    simp only [T, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun h => ⟨d.source, h, rfl⟩, fun ⟨v, h, hd⟩ => h⟩
  have h_disj : (↑(Finset.univ : Finset (Fin c.gateCount)) : Set (Fin c.gateCount)).PairwiseDisjoint (fun v => T.filter (fun d => d.source = v)) := by
    intro v1 _ v2 _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_filter]
    intro d _ hd1 hd2
    rw [hd1] at hd2
    exact hne hd2
  have h_sum : ∑ v : Fin c.gateCount, (T.filter (fun d => d.source = v)).card = T.card := by
    have hc := Finset.card_biUnion h_disj
    rw [← h_biUnion] at hc
    exact hc.symm
  have h_eq : ∀ v, switchCount r v = (T.filter (fun d => d.source = v)).card := by
    intro v
    unfold switchCount
    congr 1
    ext d
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨⟨h.2.1, h.2.2⟩, h.1⟩, fun h => ⟨h.2, h.1.1, h.1.2⟩⟩
  rw [← h_sum]
  exact Finset.sum_congr rfl (fun v _ => h_eq v)

theorem card_minCorners_add_switchCount_eq_edgeCount (hP : ProperLayered c) (r : OrientableRotation c) :
    (Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)).card +
    ∑ v : Fin c.gateCount, switchCount r v = underlyingEdgeCount c := by
  classical
  rw [sum_switchCount_eq]
  let T_up := Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true)
  have h_add : (T_up.filter (fun d => dartIsUp (r.rotation d) = true)).card + (T_up.filter (fun d => dartIsUp (r.rotation d) = false)).card = T_up.card := by
    let T1 := T_up.filter (fun d => dartIsUp (r.rotation d) = true)
    let T2 := T_up.filter (fun d => dartIsUp (r.rotation d) = false)
    have h_union : T1 ∪ T2 = T_up := by
      ext d
      simp only [T1, T2, T_up, Finset.mem_union, Finset.mem_filter]
      cases dartIsUp (r.rotation d) <;> simp
    have h_disj : Disjoint T1 T2 := by
      rw [Finset.disjoint_filter]
      intro d _ h1 h2
      rw [h1] at h2
      contradiction
    rw [← Finset.card_union_of_disjoint h_disj, h_union]
  have h1 : (Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)) = T_up.filter (fun d => dartIsUp (r.rotation d) = true) := by
    ext d
    simp only [T_up, Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 : (Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true ∧ dartIsUp (r.rotation d) = false)) = T_up.filter (fun d => dartIsUp (r.rotation d) = false) := by
    ext d
    simp only [T_up, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h1, h2, h_add]
  exact card_upDarts_eq_edgeCount hP

theorem switchCount_eq_one_of_internal (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) (hZero : rotationGenus r = 0)
    {v : Fin c.gateCount} (hns : ¬ IsGraphSource c v) (hnt : ¬ IsGraphSink c v) :
    switchCount r v = 1 := by
  have h_edges : ∃ u w, c.edge u w = true := by
    obtain ⟨u, hu⟩ : ∃ u, c.edge u v = true := by
      by_contra h
      push_neg at h
      have : IsGraphSource c v := fun x => Bool.eq_false_iff.mpr (h x)
      exact hns this
    exact ⟨u, v, hu⟩

  have hC : componentCount c = 1 := connected_of_unique_source hP hS hT
  have hI : isolatedVertexCount c = 0 := isolated_free hP hS hT h_edges
  
  have hEuler := defect_eq_of_rotationGenus_zero (r := r) hZero
  rw [hC, hI] at hEuler
  
  let E := underlyingEdgeCount c
  let F := permCycleCount (facePermutation r)
  let K := ∑ x, switchCount r x
  let M := (Finset.univ.filter (fun d : CircuitDart c => dartIsUp d = true ∧ dartIsUp (r.rotation d) = true)).card

  have hEuler_eq : 2 + E = c.gateCount + F := by omega

  have hMK : M + K = E := card_minCorners_add_switchCount_eq_edgeCount hP r
  have hFM : F ≤ M := card_minCorners_ge_faceCount hP r

  have hK_le : K ≤ c.gateCount - 2 := by omega

  obtain ⟨s, hs1, hs2⟩ := hS
  obtain ⟨t, ht1, ht2⟩ := hT

  have h_ne_st : s ≠ t := by
    intro heq
    subst heq
    have h_iso_s : ∀ u, ¬UnderlyingAdj c s u := by
      intro u ⟨h1, _⟩
      rcases h1 with h | h
      · have := ht1 u; rw [this] at h; contradiction
      · have := hs1 u; rw [this] at h; contradiction
    have h_iso_count : isolatedVertexCount c = 0 := hI
    unfold isolatedVertexCount at h_iso_count
    have h_mem : s ∈ Finset.univ.filter (fun x : Fin c.gateCount => ∀ u, ¬UnderlyingAdj c x u) := by simp [h_iso_s]
    have h_card_pos : 0 < (Finset.univ.filter (fun x : Fin c.gateCount => ∀ u, ¬UnderlyingAdj c x u)).card := Finset.card_pos.mpr ⟨s, h_mem⟩
    rw [h_iso_count] at h_card_pos
    exact lt_irrefl 0 h_card_pos

  let I := Finset.univ.filter (fun x : Fin c.gateCount => ¬ IsGraphSource c x ∧ ¬ IsGraphSink c x)
  have h_I_card_le : I.card ≤ K := card_internal_le_sum_switchCount hP ⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩ r
  
  have h_I_eq_V_minus_2 : I.card = c.gateCount - 2 := by
    have hs_not_mem : s ∉ I := by simp [I, hs1]
    have ht_not_mem : t ∉ I := by simp [I, ht1]
    have h_in_I : ∀ x, x ≠ s ∧ x ≠ t → x ∈ I := by
      intro x ⟨hx1, hx2⟩
      have hx_not_s : ¬ IsGraphSource c x := fun h => hx1 (hs2 x h)
      have hx_not_t : ¬ IsGraphSink c x := fun h => hx2 (ht2 x h)
      simp [I, hx_not_s, hx_not_t]
    have h_union : I ∪ {s, t} = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
      by_cases h : x = s ∨ x = t
      · exact Or.inr h
      · push_neg at h
        exact Or.inl (h_in_I x h)
    have h_disj : Disjoint I {s, t} := by
      rw [Finset.disjoint_insert_right]
      constructor
      · exact hs_not_mem
      · rw [Finset.disjoint_left]
        intro x hx hx2
        simp only [Finset.mem_singleton] at hx2
        subst hx2
        exact ht_not_mem hx
    have h_card := Finset.card_union_of_disjoint h_disj
    rw [h_union] at h_card
    have h_st_card : ({s, t} : Finset (Fin c.gateCount)).card = 2 := Finset.card_pair h_ne_st
    have h_univ_card : (Finset.univ : Finset (Fin c.gateCount)).card = c.gateCount := by rw [Finset.card_univ, Fintype.card_fin]
    rw [h_st_card, h_univ_card] at h_card
    omega

  have hK_eq : K = c.gateCount - 2 := by omega
  have h_I_eq_K : I.card = K := by omega
  
  have hs_zero : switchCount r s = 0 := switchCount_eq_zero_of_source hP r hs1
  have ht_zero : switchCount r t = 0 := switchCount_eq_zero_of_sink hP r ht1

  have h_sum_I : ∑ x ∈ I, switchCount r x = K := by
    have h_sum_all : ∑ x, switchCount r x = K := rfl
    have h_sum_split : ∑ x, switchCount r x = ∑ x ∈ I, switchCount r x + ∑ x ∈ {s, t}, switchCount r x := by
      have h_union : I ∪ {s, t} = Finset.univ := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
        by_cases h : x = s ∨ x = t
        · exact Or.inr h
        · push_neg at h
          have hx_not_s : ¬ IsGraphSource c x := fun h_s => h.1 (hs2 x h_s)
          have hx_not_t : ¬ IsGraphSink c x := fun h_t => h.2 (ht2 x h_t)
          simp [I, hx_not_s, hx_not_t]
      have h_disj : Disjoint I {s, t} := by
        rw [Finset.disjoint_insert_right]
        constructor
        · exact (by simp [I, hs1] : s ∉ I)
        · rw [Finset.disjoint_singleton_right]
          exact (by simp [I, ht1] : t ∉ I)
      have hsum : ∑ x ∈ I ∪ {s, t}, switchCount r x = ∑ x ∈ I, switchCount r x + ∑ x ∈ {s, t}, switchCount r x := Finset.sum_union h_disj
      rw [h_union] at hsum
      exact hsum
    have h_sum_st : ∑ x ∈ {s, t}, switchCount r x = 0 := by
      rw [Finset.sum_insert (by simp [h_ne_st]), Finset.sum_singleton]
      rw [hs_zero, ht_zero, add_zero]
    rw [h_sum_st, add_zero] at h_sum_split
    rw [h_sum_all] at h_sum_split
    exact h_sum_split.symm

  have h_v_in_I : v ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hns, hnt⟩
  have h_switch_v : 1 ≤ switchCount r v := one_le_switchCount_of_internal hP ⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩ r hns hnt
  
  have h_sum_I_2 : ∑ x ∈ I, switchCount r x = I.card + ∑ x ∈ I, (switchCount r x - 1) := by
    have : ∀ x ∈ I, switchCount r x = 1 + (switchCount r x - 1) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have h1 : 1 ≤ switchCount r x := one_le_switchCount_of_internal hP ⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩ r hx.2.1 hx.2.2
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    simp
  
  have h_sub_zero : ∑ x ∈ I, (switchCount r x - 1) = 0 := by
    calc ∑ x ∈ I, (switchCount r x - 1)
      _ = ∑ x ∈ I, switchCount r x - I.card := by omega
      _ = K - K := by rw [h_sum_I, h_I_eq_K]
      _ = 0 := by omega
  
  have h_sub_v_zero : switchCount r v - 1 = 0 := by
    have h_nonneg : ∀ x ∈ I, 0 ≤ switchCount r x - 1 := fun _ _ => by omega
    exact Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp h_sub_zero v h_v_in_I
  omega

end Internal
end AllenderOQ3
