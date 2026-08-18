import AllenderOQ3.Internal.N4Structure
import AllenderOQ3.Internal.N4Inc
import AllenderOQ3.Internal.ListGrouping

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# The layers of the refined circuit

§3 of `docs/INCIDENCE_REFINEMENT.md`.  Writing `T = F + 2`, the layers of the refined
circuit are

* the checkpoint layers `(m + 1) * T`, carrying the old gates of layer `m` in their old
  cyclic order, and
* the micro-layers `m * T + j + 1` for `j ≤ F`, carrying the `F + 1` slots of the strip of
  every old gate of layer `m`, in the old cyclic order of the gates and in slot order
  inside the block of one gate.

This file fixes the cyclic order of every layer and describes the possible shapes of an
arc of every transition.
-/

variable {n : Nat} (c : ADRCircuit n) (F : Nat) (cyl : IncidenceCylinder c)

/-! ## Guarded constructors -/

/-- The vertex `g` of layer `ell`, if it is one. -/
def n4LV (ell : Nat) (g : N4Gate c.gateCount F) :
    List (SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ell) :=
  if h : n4Layer c F g = ell then [⟨g, h⟩] else []

/-- The arc `u → v` of the transition out of layer `ell`, if it is one. -/
def n4Arc (ell : Nat) (u v : N4Gate c.gateCount F) :
    List (SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) :=
  if h : n4Edge c F (n4Inc c cyl) u v = true ∧ n4Layer c F u = ell ∧
      n4Layer c F v = ell + 1 then [⟨(u, v), h⟩] else []

theorem mem_n4LV {ell : Nat} {g : N4Gate c.gateCount F}
    {a : SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ell} :
    a ∈ n4LV c F cyl ell g ↔ a.1 = g := by
  unfold n4LV
  split
  · next h =>
      simp only [List.mem_singleton]
      exact ⟨fun ha => by rw [ha], fun ha => Subtype.ext ha⟩
  · next h =>
      simp only [List.not_mem_nil, false_iff]
      intro ha
      exact h (ha ▸ a.2)

theorem mem_n4Arc {ell : Nat} {u v : N4Gate c.gateCount F}
    {a : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell} :
    a ∈ n4Arc c F cyl ell u v ↔ a.1 = (u, v) := by
  unfold n4Arc
  split
  · next h =>
      simp only [List.mem_singleton]
      exact ⟨fun ha => by rw [ha], fun ha => Subtype.ext ha⟩
  · next h =>
      simp only [List.not_mem_nil, false_iff]
      intro ha
      refine h ?_
      have h1 := a.2
      rw [ha] at h1
      exact h1

/-- A guarded vertex is at most a singleton. -/
theorem n4LV_sublist (ell : Nat) (g : N4Gate c.gateCount F) :
    ((n4LV c F cyl ell g).map Subtype.val).Sublist [g] := by
  unfold n4LV
  split
  · simp
  · simp

theorem eq_of_mem_n4LV_val {ell : Nat} {g x : N4Gate c.gateCount F}
    (hx : x ∈ (n4LV c F cyl ell g).map Subtype.val) : x = g :=
  List.mem_singleton.mp ((n4LV_sublist c F cyl ell g).mem hx)

/-- A guarded arc is at most a singleton. -/
theorem n4Arc_sublist (ell : Nat) (u v : N4Gate c.gateCount F) :
    ((n4Arc c F cyl ell u v).map (fun e => e.1)).Sublist [(u, v)] := by
  unfold n4Arc
  split
  · simp
  · simp

theorem eq_of_mem_n4Arc_val {ell : Nat} {u v : N4Gate c.gateCount F}
    {x : N4Gate c.gateCount F × N4Gate c.gateCount F}
    (hx : x ∈ (n4Arc c F cyl ell u v).map (fun e => e.1)) : x = (u, v) :=
  List.mem_singleton.mp ((n4Arc_sublist c F cyl ell u v).mem hx)

/-! ## Layer arithmetic -/

/-- A slot index, clamped into range. -/
def finClamp (F a : Nat) : Fin (F + 1) := ⟨min a F, by omega⟩

theorem finClamp_val {F a : Nat} (h : a ≤ F) : (finClamp F a).val = a := by
  simp [finClamp, Nat.min_eq_left h]

theorem finClamp_self {F : Nat} (k : Fin (F + 1)) : finClamp F k.val = k :=
  Fin.ext (finClamp_val (by omega))

theorem finClamp_eq {F s : Nat} (h : s < F + 1) : (⟨s, h⟩ : Fin (F + 1)) = finClamp F s :=
  Fin.ext (by rw [finClamp_val (by omega)])

theorem n4_mod_lt (ell F : Nat) : ell % (F + 2) < F + 2 := Nat.mod_lt _ (by omega)

@[simp] theorem finClamp_zero (F : Nat) : (finClamp F 0).val = 0 := by simp [finClamp]

/-- The micro-layer index of a layer of the refined circuit. -/
def n4MicroIdx (F ell : Nat) : Fin (F + 1) := finClamp F (ell % (F + 2) - 1)

@[simp] theorem n4MicroIdx_val (F ell : Nat) :
    (n4MicroIdx F ell).val = ell % (F + 2) - 1 := by
  have := n4_mod_lt ell F
  simp [n4MicroIdx, finClamp, Nat.min_eq_left (show ell % (F + 2) - 1 ≤ F by omega)]

/-- The target slot of the reduction arc leaving slot `k`. -/
def n4TargetSlot {F : Nat} (k : Fin (F + 1)) : Fin (F + 1) :=
  ⟨if k.val ≤ 1 then 0 else k.val - 1, by split <;> omega⟩

@[simp] theorem n4TargetSlot_val {F : Nat} (k : Fin (F + 1)) :
    (n4TargetSlot k).val = if k.val ≤ 1 then 0 else k.val - 1 := rfl

/-- No gate of the refined circuit sits on layer `0`. -/
theorem n4Layer_ne_zero (g : N4Gate c.gateCount F) : n4Layer c F g ≠ 0 := by
  rcases g with g | ⟨g, j, k⟩ <;> simp [n4Layer]

theorem n4_old_layer_iff (g : Fin c.gateCount) (ell : Nat) :
    n4Layer c F (N4.old g) = ell ↔
      (ell % (F + 2) = 0 ∧ 0 < ell ∧ c.layer g + 1 = ell / (F + 2)) := by
  have hdm : ell / (F + 2) * (F + 2) + ell % (F + 2) = ell := Nat.div_add_mod' ell (F + 2)
  constructor
  · intro h
    simp only [n4Layer] at h
    obtain ⟨h1, h2⟩ := n4_digits_inj (T := F + 2) (b := c.layer g + 1) (j := 0)
      (b' := ell / (F + 2)) (j' := ell % (F + 2)) (by omega) (n4_mod_lt ell F) (by omega)
    refine ⟨h2.symm, ?_, h1⟩
    rw [← h]
    have : 0 < (c.layer g + 1) * (F + 2) := by positivity
    omega
  · rintro ⟨h1, -, h2⟩
    simp only [n4Layer]
    rw [h2]
    omega

theorem n4_node_layer_iff (g : Fin c.gateCount) (j k : Fin (F + 1)) (ell : Nat) :
    n4Layer c F (N4.node g j k) = ell ↔
      (c.layer g = ell / (F + 2) ∧ j.val + 1 = ell % (F + 2)) := by
  have hdm : ell / (F + 2) * (F + 2) + ell % (F + 2) = ell := Nat.div_add_mod' ell (F + 2)
  have hj : j.val + 1 < F + 2 := by omega
  constructor
  · intro h
    simp only [n4Layer] at h
    exact n4_digits_inj (T := F + 2) (b := c.layer g) (j := j.val + 1)
      (b' := ell / (F + 2)) (j' := ell % (F + 2)) hj (n4_mod_lt ell F) (by omega)
  · rintro ⟨h1, h2⟩
    simp only [n4Layer]
    rw [h1]
    omega

/-! ## Arithmetic of consecutive layers -/

theorem n4_div_mod_eq {T q r ell : Nat} (hr : r < T) (h : ell = q * T + r) :
    ell / T = q ∧ ell % T = r := by
  have hT : 0 < T := by omega
  have hdm : ell / T * T + ell % T = ell := Nat.div_add_mod' ell T
  have hlt : ell % T < T := Nat.mod_lt _ hT
  exact n4_digits_inj hlt hr (by omega)

theorem n4_succ_zero {ell : Nat} (hr : ell % (F + 2) = 0) :
    (ell + 1) % (F + 2) = 1 ∧ (ell + 1) / (F + 2) = ell / (F + 2) := by
  have hdm : ell / (F + 2) * (F + 2) + ell % (F + 2) = ell := Nat.div_add_mod' ell (F + 2)
  obtain ⟨h1, h2⟩ := n4_div_mod_eq (T := F + 2) (q := ell / (F + 2)) (r := 1)
    (ell := ell + 1) (by omega) (by omega)
  exact ⟨h2, h1⟩

theorem n4_succ_mid {ell : Nat} (h2 : ell % (F + 2) ≤ F) :
    (ell + 1) % (F + 2) = ell % (F + 2) + 1 ∧ (ell + 1) / (F + 2) = ell / (F + 2) := by
  have hdm : ell / (F + 2) * (F + 2) + ell % (F + 2) = ell := Nat.div_add_mod' ell (F + 2)
  obtain ⟨ha, hb⟩ := n4_div_mod_eq (T := F + 2) (q := ell / (F + 2))
    (r := ell % (F + 2) + 1) (ell := ell + 1) (by omega) (by omega)
  exact ⟨hb, ha⟩

theorem n4_succ_last {ell : Nat} (hr : ell % (F + 2) = F + 1) :
    (ell + 1) % (F + 2) = 0 ∧ (ell + 1) / (F + 2) = ell / (F + 2) + 1 := by
  have hdm : ell / (F + 2) * (F + 2) + ell % (F + 2) = ell := Nat.div_add_mod' ell (F + 2)
  obtain ⟨ha, hb⟩ := n4_div_mod_eq (T := F + 2) (q := ell / (F + 2) + 1) (r := 0)
    (ell := ell + 1) (by omega) (by rw [Nat.add_mul]; omega)
  exact ⟨hb, ha⟩

/-! ## The shape of an arc -/

theorem n4_leaf_arc_shape {ell : Nat} (hr : ell % (F + 2) = 0)
    (e : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) :
    ∃ (u g : Fin c.gateCount) (k : Fin (F + 1)),
      e.1 = (N4.old u, N4.node g (finClamp F 0) k) ∧ 1 ≤ k.val ∧
        (n4Inc c cyl g)[k.val - 1]? = some u ∧ c.layer g = ell / (F + 2) := by
  obtain ⟨hedge, hlu, hlv⟩ := e.2
  obtain ⟨hm1, hm2⟩ := n4_succ_zero F hr
  rcases hv : e.1.2 with v | ⟨g, j, k⟩
  · exfalso
    rw [hv] at hedge hlv
    obtain ⟨jF, k0, hu, hjF, -, -⟩ := n4Edge_into_old c F (n4Inc c cyl) hedge
    rw [hu] at hlu
    obtain ⟨-, h2⟩ := (n4_node_layer_iff c F v jF k0 ell).mp hlu
    omega
  · rw [hv] at hedge hlv
    obtain ⟨hg, hj⟩ := (n4_node_layer_iff c F g j k (ell + 1)).mp hlv
    have hj0 : j.val = 0 := by omega
    obtain ⟨hk, u, hu, hget⟩ := n4Edge_into_node_zero c F (n4Inc c cyl) hj0 hedge
    refine ⟨u, g, k, ?_, hk, hget, by rw [hg, hm2]⟩
    rw [Prod.ext_iff]
    refine ⟨by rw [← hu], ?_⟩
    have hjc : j = finClamp F 0 := Fin.ext (by simp [hj0])
    rw [hv, hjc]

theorem n4_strip_arc_shape {ell : Nat} (hr1 : ell % (F + 2) ≠ 0) (hr2 : ell % (F + 2) ≠ F + 1)
    (e : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) :
    ∃ (g : Fin c.gateCount) (k : Fin (F + 1)),
      e.1 = (N4.node g (n4MicroIdx F ell) k,
        N4.node g (n4MicroIdx F (ell + 1)) (n4TargetSlot k)) ∧ c.layer g = ell / (F + 2) := by
  obtain ⟨hedge, hlu, hlv⟩ := e.2
  have hmod : ell % (F + 2) < F + 2 := n4_mod_lt ell F
  obtain ⟨hm1, hm2⟩ := n4_succ_mid F (ell := ell) (by omega)
  rcases hv : e.1.2 with v | ⟨g, j, k⟩
  · exfalso
    rw [hv] at hedge hlv
    obtain ⟨jF, k0, hu, hjF, -, -⟩ := n4Edge_into_old c F (n4Inc c cyl) hedge
    rw [hu] at hlu
    obtain ⟨-, h2⟩ := (n4_node_layer_iff c F v jF k0 ell).mp hlu
    omega
  · rw [hv] at hedge hlv
    obtain ⟨hg, hj⟩ := (n4_node_layer_iff c F g j k (ell + 1)).mp hlv
    have hjval : j.val = ell % (F + 2) := by omega
    have hjsucc : j.val = (ell % (F + 2) - 1) + 1 := by omega
    obtain ⟨k', j', hu, hj', hcase⟩ := n4Edge_into_node_succ c F (n4Inc c cyl) hjsucc hedge
    refine ⟨g, k', ?_, by rw [hg, hm2]⟩
    rw [Prod.ext_iff]
    constructor
    · have hj1 : j' = n4MicroIdx F ell := Fin.ext (by simp only [hj', n4MicroIdx_val])
      rw [hu, hj1]
    · have hj2 : j = n4MicroIdx F (ell + 1) :=
        Fin.ext (by simp only [n4MicroIdx_val, hm1]; omega)
      have hk2 : k = n4TargetSlot k' := by
        refine Fin.ext ?_
        simp only [n4TargetSlot_val]
        rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [if_pos (by omega)]; omega
        · rw [if_pos (by omega)]; omega
        · rw [if_neg (by omega)]; omega
      rw [hv, hj2, hk2]

theorem n4_final_arc_shape {ell : Nat} (hr : ell % (F + 2) = F + 1)
    (e : SpecTransitionArc (n4Spec c F (n4Inc c cyl)) ell) :
    ∃ g : Fin c.gateCount,
      e.1 = (N4.node g (n4MicroIdx F ell) (finClamp F 0), N4.old g) ∧
        c.layer g = ell / (F + 2) ∧ (c.kind g).isComputation = true := by
  obtain ⟨hedge, hlu, hlv⟩ := e.2
  obtain ⟨hm1, hm2⟩ := n4_succ_last F hr
  rcases hv : e.1.2 with v | ⟨g, j, k⟩
  · rw [hv] at hedge hlv
    obtain ⟨jF, k0, hu, hjF, hk0, hcomp⟩ := n4Edge_into_old c F (n4Inc c cyl) hedge
    obtain ⟨-, -, hlayer⟩ := (n4_old_layer_iff c F v (ell + 1)).mp hlv
    refine ⟨v, ?_, by omega, hcomp⟩
    rw [Prod.ext_iff]
    refine ⟨?_, by rw [hv]⟩
    have hj1 : jF = n4MicroIdx F ell := Fin.ext (by simp only [hjF, n4MicroIdx_val]; omega)
    have hk1 : k0 = finClamp F 0 := Fin.ext (by simp [hk0])
    rw [hu, hj1, hk1]
  · exfalso
    rw [hv] at hlv
    obtain ⟨-, h2⟩ := (n4_node_layer_iff c F g j k (ell + 1)).mp hlv
    omega

/-! ## The layer listings -/

/-- The vertex in slot `s` of micro-layer `j` of the strip of `g`, if it is a vertex of
layer `ell`. -/
def n4LVSlot (ell : Nat) (g : Fin c.gateCount) (j : Fin (F + 1)) (s : Nat) :
    List (SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ell) :=
  if h : s < F + 1 then n4LV c F cyl ell (N4.node g j ⟨s, h⟩) else []

theorem n4LVSlot_of_lt {ell : Nat} {g : Fin c.gateCount} {j : Fin (F + 1)} {s : Nat}
    (h : s < F + 1) :
    n4LVSlot c F cyl ell g j s = n4LV c F cyl ell (N4.node g j (finClamp F s)) := by
  rw [n4LVSlot, dif_pos h, finClamp_eq h]

theorem n4LVSlot_of_ge {ell : Nat} {g : Fin c.gateCount} {j : Fin (F + 1)} {s : Nat}
    (h : ¬ s < F + 1) : n4LVSlot c F cyl ell g j s = [] := by
  rw [n4LVSlot, dif_neg h]

theorem mem_n4LVSlot {ell : Nat} {g : Fin c.gateCount} {j : Fin (F + 1)} {s : Nat}
    {a : SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ell} :
    a ∈ n4LVSlot c F cyl ell g j s ↔ (s < F + 1 ∧ a.1 = N4.node g j (finClamp F s)) := by
  by_cases h : s < F + 1
  · rw [n4LVSlot_of_lt c F cyl h, mem_n4LV]
    exact ⟨fun ha => ⟨h, ha⟩, fun ha => ha.2⟩
  · rw [n4LVSlot_of_ge c F cyl h]
    simp [h]

/-- The vertices of layer `ell` of the refined circuit, in cyclic order: the old gates of
the corresponding layer, or the `F + 1` slots of each of their strips. -/
def n4LayerList (ell : Nat) : List (SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ell) :=
  if ell % (F + 2) = 0 then
    (cyl.layerOrder (ell / (F + 2) - 1)).entries.flatMap
      (fun v => n4LV c F cyl ell (N4.old v.1))
  else
    (cyl.layerOrder (ell / (F + 2))).entries.flatMap
      (fun v => (List.range (F + 1)).flatMap (n4LVSlot c F cyl ell v.1 (n4MicroIdx F ell)))

theorem n4LayerList_nodup (ell : Nat) : (n4LayerList c F cyl ell).Nodup := by
  refine List.Nodup.of_map Subtype.val ?_
  rw [n4LayerList]
  split
  · rw [List.map_flatMap]
    refine nodup_flatMap_of_ne _ _ (cyl.layerOrder _).nodup ?_ ?_
    · intro v _
      exact List.Nodup.sublist (n4LV_sublist c F cyl ell (N4.old v.1)) (by simp)
    · intro v _ w _ hvw x hx hx'
      have h1 := eq_of_mem_n4LV_val c F cyl hx
      have h2 := eq_of_mem_n4LV_val c F cyl hx'
      rw [h1] at h2
      exact hvw (Subtype.ext (Sum.inl.inj h2))
  · rw [List.map_flatMap]
    refine nodup_flatMap_of_ne _ _ (cyl.layerOrder _).nodup ?_ ?_
    · intro v _
      rw [List.map_flatMap]
      refine nodup_flatMap_of_ne _ _ List.nodup_range ?_ ?_
      · intro s _
        rw [n4LVSlot]
        split
        · exact List.Nodup.sublist (n4LV_sublist c F cyl ell _) (by simp)
        · simp
      · intro s hs t ht hst x hx hx'
        rw [List.mem_map] at hx hx'
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, hab⟩ := hx'
        obtain ⟨-, ha1⟩ := (mem_n4LVSlot c F cyl).mp ha
        obtain ⟨-, hb1⟩ := (mem_n4LVSlot c F cyl).mp hb
        have heq : N4.node v.1 (n4MicroIdx F ell) (finClamp F t)
            = N4.node v.1 (n4MicroIdx F ell) (finClamp F s) := by
          rw [← hb1, hab, ha1]
        have hs' : s < F + 1 := List.mem_range.mp hs
        have ht' : t < F + 1 := List.mem_range.mp ht
        have hval := congrArg (fun p => (p.2.2 : Fin (F + 1)).val) (Sum.inr.inj heq)
        simp only [finClamp_val (show t ≤ F by omega), finClamp_val (show s ≤ F by omega)] at hval
        exact hst hval.symm
    · intro v _ w _ hvw x hx hx'
      rw [List.map_flatMap, List.mem_flatMap] at hx hx'
      obtain ⟨s, -, hs⟩ := hx
      obtain ⟨t, -, ht⟩ := hx'
      rw [List.mem_map] at hs ht
      obtain ⟨a, ha, rfl⟩ := hs
      obtain ⟨b, hb, hab⟩ := ht
      obtain ⟨-, ha1⟩ := (mem_n4LVSlot c F cyl).mp ha
      obtain ⟨-, hb1⟩ := (mem_n4LVSlot c F cyl).mp hb
      have heq : N4.node w.1 (n4MicroIdx F ell) (finClamp F t)
          = N4.node v.1 (n4MicroIdx F ell) (finClamp F s) := by
        rw [← hb1, hab, ha1]
      have hval := congrArg (fun p => p.1) (Sum.inr.inj heq)
      exact hvw (Subtype.ext hval.symm)

theorem n4LayerList_complete (ell : Nat)
    (a : SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ell) : a ∈ n4LayerList c F cyl ell := by
  rcases ha : a.1 with g | ⟨g, j, k⟩
  · have hlayer : n4Layer c F (N4.old g) = ell := by
      have h := a.2
      rw [ha] at h
      exact h
    obtain ⟨hr, hpos, hq⟩ := (n4_old_layer_iff c F g ell).mp hlayer
    rw [n4LayerList, if_pos hr]
    refine List.mem_flatMap.mpr ⟨⟨g, by omega⟩, (cyl.layerOrder _).complete _, ?_⟩
    exact (mem_n4LV c F cyl).mpr ha
  · have hlayer : n4Layer c F (N4.node g j k) = ell := by
      have h := a.2
      rw [ha] at h
      exact h
    obtain ⟨hq, hj⟩ := (n4_node_layer_iff c F g j k ell).mp hlayer
    have hr : ell % (F + 2) ≠ 0 := by omega
    rw [n4LayerList, if_neg hr]
    refine List.mem_flatMap.mpr ⟨⟨g, hq⟩, (cyl.layerOrder _).complete _, ?_⟩
    refine List.mem_flatMap.mpr ⟨k.val, List.mem_range.mpr k.isLt, ?_⟩
    refine (mem_n4LVSlot c F cyl).mpr ⟨k.isLt, ?_⟩
    have hjm : j = n4MicroIdx F ell := Fin.ext (by simp only [n4MicroIdx_val]; omega)
    rw [ha, hjm, finClamp_self]

/-- The cyclic order of layer `ell` of the refined circuit. -/
def n4LayerOrder (ell : Nat) : CyclicListing (SpecLayerVertex (n4Spec c F (n4Inc c cyl)) ell) where
  entries := n4LayerList c F cyl ell
  nodup := n4LayerList_nodup c F cyl ell
  complete := n4LayerList_complete c F cyl ell

end AllenderOQ3.Internal
