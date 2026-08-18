import AllenderOQ3.Internal.N4Spec

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# Structural properties of the N4 refinement

Well-formedness, the fan-in bound of §2.1, the total width bound of §5 and the size
bound of §5 of `docs/INCIDENCE_REFINEMENT.md`, all proved on the abstract gate type.
-/

/-- Two positions in a base-`T` expansion with digits below `T` agree. -/
theorem n4_digits_inj {T b j b' j' : Nat} (hj : j < T) (hj' : j' < T)
    (h : b * T + j = b' * T + j') : b = b' ∧ j = j' := by
  rcases Nat.lt_trichotomy b b' with hb | hb | hb
  · exfalso
    have h1 : b * T + T ≤ b' * T := by
      calc b * T + T = (b + 1) * T := by ring
        _ ≤ b' * T := Nat.mul_le_mul_right T hb
    omega
  · subst hb; omega
  · exfalso
    have h1 : b' * T + T ≤ b * T := by
      calc b' * T + T = (b' + 1) * T := by ring
        _ ≤ b * T := Nat.mul_le_mul_right T hb
    omega

variable {n : Nat}

section Structure

variable (c : ADRCircuit n) (F : Nat) (pred : Fin c.gateCount → List (Fin c.gateCount))

@[simp] theorem n4Spec_edge (u v : N4Gate c.gateCount F) :
    (n4Spec c F pred).edge u v = n4Edge c F pred u v := rfl

@[simp] theorem n4Spec_layer (u : N4Gate c.gateCount F) :
    (n4Spec c F pred).layer u = n4Layer c F u := rfl

@[simp] theorem n4Spec_kind (u : N4Gate c.gateCount F) :
    (n4Spec c F pred).kind u = n4Kind c F u := rfl

/-- The source of a wire into a checkpoint node. -/
theorem n4Edge_into_old {u : N4Gate c.gateCount F} {g : Fin c.gateCount}
    (h : n4Edge c F pred u (N4.old g) = true) :
    ∃ (j : Fin (F + 1)) (k : Fin (F + 1)), u = N4.node g j k ∧ j.val = F ∧ k.val = 0 ∧
      (c.kind g).isComputation = true := by
  rcases u with u | ⟨g', j', k'⟩
  · exact absurd h (by simp [n4Edge])
  · simp only [n4Edge, decide_eq_true_eq] at h
    exact ⟨j', k', by rw [h.1], h.2.1, h.2.2.1, h.2.2.2⟩

/-- The source of a wire into a node of the first micro-layer of a strip. -/
theorem n4Edge_into_node_zero {u : N4Gate c.gateCount F} {g : Fin c.gateCount}
    {j k : Fin (F + 1)} (hj : j.val = 0) (h : n4Edge c F pred u (N4.node g j k) = true) :
    1 ≤ k.val ∧ ∃ w : Fin c.gateCount, u = N4.old w ∧ (pred g)[k.val - 1]? = some w := by
  rcases u with u | ⟨g', j', k'⟩
  · simp only [n4Edge, decide_eq_true_eq] at h
    exact ⟨h.2.1, u, rfl, h.2.2⟩
  · simp only [n4Edge, decide_eq_true_eq] at h
    omega

/-- The source of a wire into a node of a later micro-layer of a strip. -/
theorem n4Edge_into_node_succ {u : N4Gate c.gateCount F} {g : Fin c.gateCount}
    {j k : Fin (F + 1)} {j0 : Nat} (hj : j.val = j0 + 1)
    (h : n4Edge c F pred u (N4.node g j k) = true) :
    ∃ k' : Fin (F + 1), ∃ j' : Fin (F + 1), u = N4.node g j' k' ∧ j'.val = j0 ∧
      ((k.val = 0 ∧ k'.val = 0) ∨ (k.val = 0 ∧ k'.val = 1) ∨
        (1 ≤ k.val ∧ k'.val = k.val + 1)) := by
  rcases u with u | ⟨g', j', k'⟩
  · simp only [n4Edge, decide_eq_true_eq] at h
    omega
  · simp only [n4Edge, decide_eq_true_eq] at h
    obtain ⟨rfl, hjj, hcase⟩ := h
    refine ⟨k', j', rfl, by omega, ?_⟩
    rcases hcase with ⟨a, b⟩ | ⟨a, b, _⟩ | ⟨a, b, _⟩
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr (Or.inl ⟨a, b⟩)
    · exact Or.inr (Or.inr ⟨a, b⟩)

/-! ## Well-formedness -/

theorem n4Spec_wellFormed (hlay : ∀ g u, u ∈ pred g → c.layer u + 1 = c.layer g) :
    SpecWellFormed (n4Spec c F pred) := by
  constructor
  · rintro u (v | ⟨g, j, k⟩) h
    · obtain ⟨j', k', rfl, hjF, -, -⟩ := n4Edge_into_old c F pred h
      simp only [n4Spec_layer, n4Layer, hjF]
      ring
    · rcases hj : j.val with _ | j0
      · obtain ⟨hk, w, rfl, hget⟩ := n4Edge_into_node_zero c F pred hj h
        obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hget
        have hw : w ∈ pred g := hval ▸ List.getElem_mem hlt
        have hlg := hlay g w hw
        simp only [n4Spec_layer, n4Layer, hj, ← hlg]
      · obtain ⟨k', j', rfl, hj', -⟩ := n4Edge_into_node_succ c F pred hj h
        simp only [n4Spec_layer, n4Layer, hj, hj']
        omega
  · rintro (g | ⟨g, j, k⟩) ⟨i, b, hkind⟩ u
    · -- an old literal gate has no incoming wire
      have hcomp : (c.kind g).isComputation = false := by
        cases hg : c.kind g with
        | literal i' b' => rfl
        | andGate => rw [n4Spec_kind, n4Kind, hg] at hkind; exact absurd hkind (by simp)
        | orGate => rw [n4Spec_kind, n4Kind, hg] at hkind; exact absurd hkind (by simp)
      by_contra hcon
      have h : n4Edge c F pred u (N4.old g) = true := by
        simpa [n4Spec] using Bool.not_eq_false _ |>.mp hcon
      obtain ⟨-, -, -, -, -, hc⟩ := n4Edge_into_old c F pred h
      rw [hcomp] at hc
      exact Bool.false_ne_true hc
    · -- only the fresh port nodes are literals, and they are sources
      have hzero : j.val = 0 ∧ k.val = 0 := by
        by_contra hcon
        rw [n4Spec_kind, n4Kind, if_neg hcon] at hkind
        by_cases hk : k.val = 0
        · rw [if_pos hk, n4Op] at hkind
          cases hg : c.kind g with
          | literal i' b' => rw [hg] at hkind; exact absurd hkind (by simp)
          | andGate => rw [hg] at hkind; exact absurd hkind (by simp)
          | orGate => rw [hg] at hkind; exact absurd hkind (by simp)
        · rw [if_neg hk] at hkind
          exact absurd hkind (by simp)
      by_contra hcon
      have h : n4Edge c F pred u (N4.node g j k) = true := by
        simpa [n4Spec] using Bool.not_eq_false _ |>.mp hcon
      obtain ⟨hk, -⟩ := n4Edge_into_node_zero c F pred hzero.1 h
      omega

/-! ## Fan-in -/

/-- The slot marker used to separate the at most two sources of a node. -/
def n4Slot {m F : Nat} : N4Gate m F → Bool
  | Sum.inl _ => true
  | Sum.inr (_, _, k) => decide (k.val = 0)

/-- The old gate a node belongs to. -/
def n4Base {m F : Nat} : N4Gate m F → Fin m
  | Sum.inl g => g
  | Sum.inr (g, _, _) => g

/-- The slot index of a node; checkpoint nodes get the accumulator slot. -/
def n4SlotIdx {m F : Nat} : N4Gate m F → Fin (F + 1)
  | Sum.inl _ => ⟨0, Nat.succ_pos F⟩
  | Sum.inr (_, _, k) => k

theorem n4Spec_fanin (v : N4Gate c.gateCount F) :
    (Finset.univ.filter fun u => (n4Spec c F pred).edge u v = true).card ≤ 2 := by
  classical
  have hcard : (Finset.univ : Finset Bool).card = 2 := rfl
  rw [← hcard]
  refine Finset.card_le_card_of_injOn n4Slot (fun a _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
  intro a ha b hb hab
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
    n4Spec_edge] at ha hb
  rcases v with v | ⟨v, j, k⟩
  · obtain ⟨ja, ka, rfl, hjaF, hka0, -⟩ := n4Edge_into_old c F pred ha
    obtain ⟨jb, kb, rfl, hjbF, hkb0, -⟩ := n4Edge_into_old c F pred hb
    have : ja = jb := Fin.ext (by omega)
    have : ka = kb := Fin.ext (by omega)
    simp_all
  · rcases hj : j.val with _ | j0
    · obtain ⟨-, wa, rfl, hga⟩ := n4Edge_into_node_zero c F pred hj ha
      obtain ⟨-, wb, rfl, hgb⟩ := n4Edge_into_node_zero c F pred hj hb
      rw [hga] at hgb
      simp_all
    · obtain ⟨ka, ja, rfl, hja, hca⟩ := n4Edge_into_node_succ c F pred hj ha
      obtain ⟨kb, jb, rfl, hjb, hcb⟩ := n4Edge_into_node_succ c F pred hj hb
      simp only [n4Slot, decide_eq_decide] at hab
      have hjab : ja = jb := Fin.ext (by omega)
      have hkab : ka = kb := by
        refine Fin.ext ?_
        rcases hca with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases hcb with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
      rw [hjab, hkab]

/-! ## Total width -/

theorem n4_base_layer_eq {a b : N4Gate c.gateCount F} {ell : Nat}
    (ha : n4Layer c F a = ell) (hb : n4Layer c F b = ell) :
    c.layer (n4Base a) = c.layer (n4Base b) := by
  rcases a with a | ⟨a, ja, ka⟩ <;> rcases b with b | ⟨b, jb, kb⟩ <;>
    simp only [n4Layer] at ha hb <;> simp only [n4Base]
  · have := n4_digits_inj (T := F + 2) (b := c.layer a + 1) (j := 0)
      (b' := c.layer b + 1) (j' := 0) (by omega) (by omega) (by omega)
    omega
  · exfalso
    have := n4_digits_inj (T := F + 2) (b := c.layer a + 1) (j := 0)
      (b' := c.layer b) (j' := jb.val + 1) (by omega) (by omega) (by omega)
    omega
  · exfalso
    have := n4_digits_inj (T := F + 2) (b := c.layer a) (j := ja.val + 1)
      (b' := c.layer b + 1) (j' := 0) (by omega) (by omega) (by omega)
    omega
  · have := n4_digits_inj (T := F + 2) (b := c.layer a) (j := ja.val + 1)
      (b' := c.layer b) (j' := jb.val + 1) (by omega) (by omega) (by omega)
    omega

theorem n4_fiber_inj {a b : N4Gate c.gateCount F} {ell : Nat}
    (ha : n4Layer c F a = ell) (hb : n4Layer c F b = ell)
    (hbase : n4Base a = n4Base b) (hslot : n4SlotIdx a = n4SlotIdx b) : a = b := by
  rcases a with a | ⟨a, ja, ka⟩ <;> rcases b with b | ⟨b, jb, kb⟩ <;>
    simp only [n4Base] at hbase <;> simp only [n4Layer] at ha hb
  · rw [hbase]
  · exfalso
    have := n4_digits_inj (T := F + 2) (b := c.layer a + 1) (j := 0)
      (b' := c.layer b) (j' := jb.val + 1) (by omega) (by omega) (by omega)
    omega
  · exfalso
    have := n4_digits_inj (T := F + 2) (b := c.layer a) (j := ja.val + 1)
      (b' := c.layer b + 1) (j' := 0) (by omega) (by omega) (by omega)
    omega
  · subst hbase
    have hj : ja = jb := Fin.ext (by omega)
    simp only [n4SlotIdx] at hslot
    rw [hj, hslot]

theorem n4Spec_totalWidth {W : Nat} (hw : TotalWidthAtMost c W) (ell : Nat) :
    (Finset.univ.filter fun g : N4Gate c.gateCount F =>
      (n4Spec c F pred).layer g = ell).card ≤ (F + 1) * W := by
  classical
  set s : Finset (N4Gate c.gateCount F) :=
    Finset.univ.filter (fun g => (n4Spec c F pred).layer g = ell) with hs
  rcases Finset.eq_empty_or_nonempty s with hemp | ⟨a₀, ha₀⟩
  · simp [hemp]
  · have hmem : ∀ a ∈ s, n4Layer c F a = ell := by
      intro a ha
      rw [hs, Finset.mem_filter] at ha
      exact ha.2
    have hbase : ∀ a ∈ s, c.layer (n4Base a) = c.layer (n4Base a₀) := fun a ha =>
      n4_base_layer_eq c F (hmem a ha) (hmem a₀ ha₀)
    have himg : (s.image n4Base).card ≤ W := by
      refine le_trans (Finset.card_le_card ?_) (hw (c.layer (n4Base a₀)))
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbase a ha⟩
    refine le_trans (Finset.card_le_mul_card_image (f := n4Base) s (F + 1) ?_) ?_
    · intro b _
      have hcard : (Finset.univ : Finset (Fin (F + 1))).card = F + 1 := by simp
      rw [← hcard]
      refine Finset.card_le_card_of_injOn n4SlotIdx
        (fun a _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      exact n4_fiber_inj c F (hmem x hx.1) (hmem y hy.1) (by rw [hx.2, hy.2]) hxy
    · exact Nat.mul_le_mul_left (F + 1) himg

/-! ## Size -/

theorem n4_card_gate : Fintype.card (N4Gate c.gateCount F)
    = c.gateCount + c.gateCount * ((F + 1) * (F + 1)) := by
  simp [N4Gate, Fintype.card_sum, Fintype.card_prod]

end Structure

end AllenderOQ3.Internal
