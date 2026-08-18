import AllenderOQ3.Internal.CutNecklace

set_option autoImplicit false

/-!
# Orbit words with one exit per fibre are cyclically contiguous

The combinatorial core behind the necklace grouping obligations, with no
circuit content at all.

Let `q` be a permutation of a finite type and `w = orbitList q a0` one of its
orbit words.  Call `x` an *exit* of its `key`-fibre when `key (q x) ≠ key x`.
If every fibre has at most one exit — `x` and `y` in a common fibre that are
both exits must be equal — then the fibres of `w` are contiguous *after a
cyclic rotation* (`cyclicContiguous_orbitList`).

The rotation is unavoidable: `orbitList` starts at `a0`, which is in general in
the middle of its own block.  The proof rotates `w` so that it starts at a
block boundary, and then a fibre that were split into two runs would exit
twice.
-/

namespace AllenderOQ3.Internal

/-- Three letters of a sublist come from three increasing positions. -/
theorem exists_indices_of_sublist_three {alpha : Type} (x t y : alpha)
    (w : List alpha) (h : [x, t, y].Sublist w) :
    ∃ i j k, ∃ (_ : i < w.length) (_ : j < w.length) (hk : k < w.length),
      i < j ∧ j < k ∧ w[i] = x ∧ w[j] = t ∧ w[k]'hk = y := by
  rw [List.cons_sublist_iff] at h
  obtain ⟨r₁, r₂, rfl, hx, h2⟩ := h
  rw [List.cons_sublist_iff] at h2
  obtain ⟨r₃, r₄, rfl, ht, h3⟩ := h2
  have hy : y ∈ r₄ := List.singleton_sublist.mp h3
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, hjt⟩ := List.getElem_of_mem ht
  obtain ⟨k, hk, hky⟩ := List.getElem_of_mem hy
  have hlen : (r₁ ++ (r₃ ++ r₄)).length = r₁.length + (r₃.length + r₄.length) := by
    simp
  refine ⟨i, r₁.length + j, r₁.length + (r₃.length + k), by omega, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_⟩
  · rw [List.getElem_append_left hi]; exact hix
  · rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_left hj]; exact hjt
  · rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact hky

/-- Contiguity is a statement about triples of increasing positions. -/
theorem keyContiguous_of_getElem {alpha beta : Type} (key : alpha → beta)
    (w : List alpha)
    (h : ∀ i j k, ∀ (hi : i < w.length) (hj : j < w.length) (hk : k < w.length),
      i < j → j < k → key (w[i]'hi) = key (w[k]'hk) →
        key (w[j]'hj) = key (w[i]'hi)) :
    KeyContiguous key w := by
  intro x t y hsub hxy
  obtain ⟨i, j, k, hi, hj, hk, hij, hjk, hix, hjt, hky⟩ :=
    exists_indices_of_sublist_three x t y w hsub
  have := h i j k hi hj hk hij hjk (by rw [hix, hky]; exact hxy)
  rw [hix, hjt] at this
  exact this

section Orbit

variable {alpha beta : Type} [Fintype alpha] [DecidableEq alpha]

/-- **Orbit words with at most one exit per fibre are cyclically contiguous.**
`x` is an exit of its fibre when `key (q x) ≠ key x`; the hypothesis says that
two exits in a common fibre coincide. -/
theorem cyclicContiguous_orbitList (q : Equiv.Perm alpha) (a0 : alpha)
    (key : alpha → beta)
    (hexit : ∀ x ∈ orbitList q a0, ∀ y ∈ orbitList q a0,
      key x = key y → key (q x) ≠ key x → key (q y) ≠ key y → x = y) :
    CyclicContiguous key (orbitList q a0) := by
  classical
  set P := orbitPeriod q a0 with hPdef
  set g : Nat → alpha := fun m => (q ^ m) a0 with hgdef
  set w := orbitList q a0 with hwdef
  have hw : w = (List.range P).map g := rfl
  have hlen : w.length = P := by rw [hw]; simp
  have hget : ∀ (m : Nat) (hm : m < w.length), w[m]'hm = g m := by
    intro m hm
    have h1 : w[m]'hm = ((List.range P).map g)[m]'hm := rfl
    rw [h1, List.getElem_map, List.getElem_range]
  have hstep : ∀ m, q (g m) = g (m + 1) := by
    intro m
    change q ((q ^ m) a0) = (q ^ (m + 1)) a0
    rw [pow_succ', Equiv.Perm.mul_apply]
  have hper : ∀ m, g (m + P) = g m := by
    intro m
    change (q ^ (m + P)) a0 = (q ^ m) a0
    rw [pow_add, Equiv.Perm.mul_apply, hPdef, orbitPeriod_return]
  have hmem : ∀ m, g m ∈ w := fun m => pow_mem_orbitList q a0 m
  by_cases hex : ∃ s, s < P ∧ key (g s) ≠ key (g (s + 1))
  · obtain ⟨s, hsP, hskey⟩ := hex
    set b := s + 1 with hbdef
    refine ⟨w.drop b ++ w.take b,
      ⟨w.take b, w.drop b, (List.take_append_drop b w).symm, rfl⟩, ?_⟩
    have hdroplen : (w.drop b).length = P - b := by
      rw [List.length_drop, hlen]
    have hlen' : (w.drop b ++ w.take b).length = P := by
      rw [List.length_append, List.length_drop, List.length_take, hlen]
      omega
    have hperm : (w.drop b ++ w.take b).Perm w := by
      refine List.Perm.trans List.perm_append_comm ?_
      rw [List.take_append_drop]
    have hnodup' : (w.drop b ++ w.take b).Nodup :=
      (hperm.nodup_iff).mpr (by rw [hwdef]; exact orbitList_nodup q a0)
    have hw'get : ∀ (m : Nat) (hm : m < (w.drop b ++ w.take b).length),
        (w.drop b ++ w.take b)[m]'hm = g (b + m) := by
      intro m hm
      have hmP : m < P := hlen' ▸ hm
      by_cases hmb : m < (w.drop b).length
      · rw [List.getElem_append_left hmb, List.getElem_drop, hget]
      · rw [List.getElem_append_right (by omega), List.getElem_take, hget]
        have hb : b ≤ P := by omega
        have hidx : b + m = (m - (w.drop b).length) + P := by omega
        rw [hidx, hper]
    refine keyContiguous_of_getElem key (w.drop b ++ w.take b) ?_
    intro i j k hi hj hk hij hjk hik
    have ei := hw'get i hi
    have ej := hw'get j hj
    have ek := hw'get k hk
    rw [hlen'] at hi hj hk
    rw [ei, ek] at hik
    rw [ei, ej]
    by_contra hne
    set K := key (g (b + i)) with hKdef
    set Pr : Nat → Prop := fun m => key (g (b + m)) = K with hPrdef
    have hPri : Pr i := rfl
    have hPrk : Pr k := hik.symm
    -- the last position before `j` still in the fibre is an exit
    set p := Nat.findGreatest Pr (j - 1) with hpdef
    have hpspec : key (g (b + p)) = K :=
      Nat.findGreatest_spec (P := Pr) (m := i) (by omega) hPri
    have hpge : i ≤ p := Nat.le_findGreatest (P := Pr) (by omega) hPri
    have hple : p ≤ j - 1 := Nat.findGreatest_le _
    have hpexit : key (g (b + p + 1)) ≠ K := by
      by_cases hpj : p + 1 = j
      · have hbj : b + p + 1 = b + j := by omega
        rw [hbj]
        exact hne
      · have hng : ¬ Pr (p + 1) :=
          Nat.findGreatest_is_greatest (P := Pr) (k := p + 1) (n := j - 1)
            (by omega) (by omega)
        have hbp : b + (p + 1) = b + p + 1 := by omega
        rw [hPrdef] at hng
        simp only [hbp] at hng
        exact hng
    -- the last position of the whole word still in the fibre is another exit
    set p' := Nat.findGreatest Pr (P - 1) with hp'def
    have hp'spec : key (g (b + p')) = K :=
      Nat.findGreatest_spec (P := Pr) (m := k) (by omega) hPrk
    have hp'ge : k ≤ p' := Nat.le_findGreatest (P := Pr) (by omega) hPrk
    have hp'le : p' ≤ P - 1 := Nat.findGreatest_le _
    have hp'exit : key (g (b + p' + 1)) ≠ K := by
      by_cases hlast : p' + 1 = P
      · have h1 : b + p' = s + P := by omega
        have h2 : b + p' + 1 = (s + 1) + P := by omega
        rw [h2, hper]
        rw [h1, hper] at hp'spec
        rw [← hp'spec]
        exact fun hcon => hskey hcon.symm
      · have hng : ¬ Pr (p' + 1) :=
          Nat.findGreatest_is_greatest (P := Pr) (k := p' + 1) (n := P - 1)
            (by omega) (by omega)
        have hbp : b + (p' + 1) = b + p' + 1 := by omega
        rw [hPrdef] at hng
        simp only [hbp] at hng
        exact hng
    -- two exits in the same fibre must coincide, but the positions differ
    have hpp' : p ≠ p' := by omega
    have heq : g (b + p) = g (b + p') := by
      refine hexit (g (b + p)) (hmem _) (g (b + p')) (hmem _) ?_ ?_ ?_
      · rw [hpspec, hp'spec]
      · rw [hstep, hpspec]
        exact hpexit
      · rw [hstep, hp'spec]
        exact hp'exit
    have hpP : p < P := by omega
    have hp'P : p' < P := by omega
    have hgi := hw'get p (by omega)
    have hgi' := hw'get p' (by omega)
    exact hpp' ((hnodup'.getElem_inj_iff (i := p) (hi := by omega)
      (j := p') (hj := by omega)).mp (by rw [hgi, hgi']; exact heq))
  · push_neg at hex
    refine ⟨w, ⟨w, [], (List.append_nil w).symm, rfl⟩, ?_⟩
    have hall : ∀ m, m < P → key (g m) = key (g 0) := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ nn ih =>
        intro hn
        rw [← hex nn (by omega)]
        exact ih (by omega)
    have hconst : ∀ z ∈ w, key z = key (g 0) := by
      intro z hz
      rw [hw, List.mem_map] at hz
      obtain ⟨m, hm, hmz⟩ := hz
      rw [← hmz]
      exact hall m (List.mem_range.mp hm)
    intro x t y hsub _
    have hx : x ∈ w := hsub.subset (by simp)
    have ht : t ∈ w := hsub.subset (by simp)
    rw [hconst x hx, hconst t ht]

end Orbit

end AllenderOQ3.Internal
