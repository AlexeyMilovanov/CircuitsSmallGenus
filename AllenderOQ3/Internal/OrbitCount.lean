import AllenderOQ3.Base

set_option autoImplicit false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace AllenderOQ3.Internal

theorem gateCount_pos {n : Nat} (c : ADRCircuit n) : 0 < c.gateCount := by
  have := c.output.isLt
  omega

theorem perm_forwardReach_symm {α : Type} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) {x y : α} (h : ∃ k : Nat, (p ^ k) x = y) :
    ∃ k : Nat, (p ^ k) y = x := by
  obtain ⟨k, hk⟩ := h
  use orderOf p - (k % orderOf p)
  have hord : 1 ≤ orderOf p := orderOf_pos p
  have h1 : orderOf p - (k % orderOf p) + (k % orderOf p) = orderOf p :=
    Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt k (orderOf_pos p)))
  calc (p ^ (orderOf p - (k % orderOf p))) y
    _ = (p ^ (orderOf p - (k % orderOf p))) ((p ^ k) x) := by rw [hk]
    _ = (p ^ (orderOf p - (k % orderOf p))) ((p ^ (k % orderOf p)) x) := by rw [pow_mod_orderOf]
    _ = ((p ^ (orderOf p - (k % orderOf p))) * (p ^ (k % orderOf p))) x := rfl
    _ = (p ^ (orderOf p - (k % orderOf p) + (k % orderOf p))) x := by rw [pow_add]
    _ = (p ^ orderOf p) x := by rw [h1]
    _ = (1 : Equiv.Perm α) x := by rw [pow_orderOf_eq_one]
    _ = x := rfl

open Classical in
theorem exists_minRep {α : Type} [Fintype α] {r : α → α → Prop}
    (hr : Equivalence r) (rank : α → Nat) (a : α) :
    ∃ x, r a x ∧ ∀ y, r x y → rank x ≤ rank y := by
  let S := Finset.univ.filter (fun x => r a x)
  have hS : S.Nonempty := by
    use a
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hr.refl a⟩
  let m := S.image rank
  have hm : m.Nonempty := Finset.Nonempty.image hS rank
  have hmin : m.min' hm ∈ m := Finset.min'_mem m hm
  rw [Finset.mem_image] at hmin
  obtain ⟨x, hx1, hx2⟩ := hmin
  use x
  have hx1' := Finset.mem_filter.mp hx1
  refine ⟨hx1'.2, ?_⟩
  intro y hy
  have hy1 : y ∈ S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hr.trans hx1'.2 hy⟩
  have h_img : rank y ∈ m := Finset.mem_image_of_mem rank hy1
  have h_le := Finset.min'_le m (rank y) h_img
  calc rank x = m.min' hm := hx2
    _ ≤ rank y := h_le

theorem minRep_unique {α : Type} {r : α → α → Prop} (hr : Equivalence r)
    (rank : α → Nat) (hrank : Function.Injective rank) {x y : α}
    (hxy : r x y)
    (hx : ∀ z, r x z → rank x ≤ rank z) (hy : ∀ z, r y z → rank y ≤ rank z) : x = y := by
  have hyx : r y x := hr.symm hxy
  have h1 := hx y hxy
  have h2 := hy x hyx
  have h3 : rank x = rank y := le_antisymm h1 h2
  exact hrank h3

theorem vertexReachable_equiv {n : Nat} (c : ADRCircuit n) : Equivalence (VertexReachable c) := by
  constructor
  · intro x; exact Relation.ReflTransGen.refl
  · apply Relation.ReflTransGen.symmetric
    intro u v huv
    obtain ⟨h1, h2⟩ := huv
    exact ⟨h1.elim Or.inr Or.inl, Ne.symm h2⟩
  · intro x y z h1 h2
    exact Relation.ReflTransGen.trans h1 h2

open Classical in
theorem componentCount_pos {n : Nat} (c : ADRCircuit n) : 1 ≤ componentCount c := by
  have hpos := gateCount_pos c
  have hne : Nonempty (Fin c.gateCount) := ⟨c.output⟩
  obtain ⟨x, _hx1, hx2⟩ := exists_minRep (vertexReachable_equiv c) Fin.val c.output
  unfold componentCount
  apply Finset.card_pos.mpr
  use x
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx2⟩

open Classical in
theorem componentCount_ge_of_pairwise_unreachable {n : Nat} (c : ADRCircuit n)
    (S : Finset (Fin c.gateCount))
    (hS : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ VertexReachable c u v) :
    S.card ≤ componentCount c := by
  let f (u : Fin c.gateCount) : Fin c.gateCount :=
    Classical.choose (exists_minRep (vertexReachable_equiv c) Fin.val u)
  have hf (u : Fin c.gateCount) :
      VertexReachable c u (f u) ∧ ∀ y, VertexReachable c (f u) y → (f u).val ≤ y.val :=
    Classical.choose_spec (exists_minRep (vertexReachable_equiv c) Fin.val u)
  unfold componentCount
  have h_img (u : Fin c.gateCount) : f u ∈ Finset.univ.filter (fun u =>
      ∀ v, VertexReachable c u v → u.val ≤ v.val) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ (f u), (hf u).2⟩
  have h_inj : ∀ u ∈ S, ∀ v ∈ S, f u = f v → u = v := by
    intro u hu v hv heq
    by_contra h_neq
    have h1 : VertexReachable c u (f u) := (hf u).1
    have h2 : VertexReachable c v (f v) := (hf v).1
    rw [heq] at h1
    have h_reach : VertexReachable c u v := by
      have heq_rel := vertexReachable_equiv c
      exact heq_rel.trans h1 (heq_rel.symm h2)
    exact hS u hu v hv h_neq h_reach
  have h_card := Finset.card_image_of_injOn h_inj
  have h_subset : S.image f ⊆ Finset.univ.filter (fun u =>
      ∀ v, VertexReachable c u v → u.val ≤ v.val) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨u, _hu, rfl⟩ := hx
    exact h_img u
  rw [← h_card]
  exact Finset.card_le_card h_subset

open Classical in
theorem permCycleCount_pos {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : Equiv.Perm α) : 1 ≤ permCycleCount p := by
  let r (x y : α) : Prop := ∃ k : Nat, (p ^ k) x = y
  have hr : Equivalence r := by
    constructor
    · intro x; exact ⟨0, rfl⟩
    · intro x y hxy; exact perm_forwardReach_symm p hxy
    · intro x y z ⟨k1, hk1⟩ ⟨k2, hk2⟩
      exact ⟨k2 + k1, by rw [pow_add, Equiv.Perm.mul_apply, hk1, hk2]⟩
  obtain ⟨a⟩ := ‹Nonempty α›
  obtain ⟨x, _, hx2⟩ := exists_minRep hr (fun y => (Fintype.equivFin α y).val) a
  unfold permCycleCount
  apply Finset.card_pos.mpr
  use x
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx2⟩

end AllenderOQ3.Internal
