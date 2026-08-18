import AllenderOQ3.Internal.DartClass
import AllenderOQ3.Internal.CountInvariance

/-!
# E1-B2: switch corners of a rotation at an internal vertex

This file supplies the counting half of the Euler/Morse corner argument used by
the Hansen arc-order principle (external fact E1).

* `exists_switch_of_cycle` is a purely generic statement about permutations: on
  a single cycle a non-constant `Bool` predicate must have an adjacent
  `true → false` step.
* `switchCount r v` counts the *switch corners* of the rotation `r` at the
  vertex `v`: the darts leaving `v` that are up-darts and whose rotation
  successor is a down-dart.
* `one_le_switchCount_of_internal` says that every internal vertex of a properly
  layered st-graph carries at least one switch corner.  It combines the generic
  cycle lemma with `Internal.exists_updown_dart_of_internal`.
* `card_upDarts_eq_card_downDarts` and `card_upDarts_eq_edgeCount` are the
  handshake counts for the up/down dichotomy.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/-! ### A generic cycle lemma -/

/-- On a single cycle, a `Bool` predicate that takes both values somewhere has an
adjacent `true → false` step. -/
theorem exists_switch_of_cycle {α : Type} (p : Equiv.Perm α)
    (hcyc : ∀ x y : α, ∃ k : Nat, (p ^ k) x = y)
    (pred : α → Bool) {a b : α} (ha : pred a = true) (hb : pred b = false) :
    ∃ x : α, pred x = true ∧ pred (p x) = false := by
  classical
  obtain ⟨K, hK⟩ := hcyc a b
  have hex : ∃ k : Nat, pred ((p ^ k) a) = false := ⟨K, by rw [hK]; exact hb⟩
  have hk : pred ((p ^ Nat.find hex) a) = false := Nat.find_spec hex
  have hkpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hk
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hk
      rw [ha] at hk
      exact absurd hk (by simp)
    · exact h
  refine ⟨(p ^ (Nat.find hex - 1)) a, ?_, ?_⟩
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    simpa using hmin
  · have hstep : p ((p ^ (Nat.find hex - 1)) a) = (p ^ Nat.find hex) a := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    rw [hstep]
    exact hk

/-! ### Switch corners at a vertex -/

variable {n : Nat} {c : ADRCircuit n}

/-- The number of *switch corners* of the rotation `r` at the vertex `v`: darts
leaving `v` that are up-darts whose rotation successor is a down-dart. -/
noncomputable def switchCount (r : OrientableRotation c) (v : Fin c.gateCount) : Nat := by
  classical
  exact (Finset.univ.filter fun d : CircuitDart c =>
    d.source = v ∧ dartIsUp d = true ∧ dartIsUp (r.rotation d) = false).card

/-- The rotation restricted to the darts leaving a fixed vertex. -/

theorem switchCount_eq_zero_of_source (hP : ProperLayered c) (r : OrientableRotation c) {s : Fin c.gateCount}
    (hs : IsGraphSource c s) : switchCount r s = 0 := by
  unfold switchCount
  rw [Finset.card_eq_zero]
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h_src, h_up, h_up'⟩
    have h_sig_src : (r.rotation d).source = s := by
      have : (r.rotation d).source = d.source := r.preservesSource d
      rw [this, h_src]
    have H : ∀ d' : CircuitDart c, d'.source = s → dartIsUp d' = true := by
      intro d' hd'
      unfold dartIsUp
      have hadj : c.edge d'.source d'.target = true ∨ c.edge d'.target d'.source = true := d'.property.1
      rcases hadj with he | he
      · exact he
      · have : c.edge d'.target s = false := hs d'.target
        rw [← hd'] at this
        rw [this] at he
        exact Bool.noConfusion he
    have H2 := H (r.rotation d) h_sig_src
    simp [H2] at h_up'
  · intro h
    simp at h

theorem switchCount_eq_zero_of_sink (hP : ProperLayered c) (r : OrientableRotation c) {t : Fin c.gateCount}
    (ht : IsGraphSink c t) : switchCount r t = 0 := by
  unfold switchCount
  rw [Finset.card_eq_zero]
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h_src, h_up, h_up'⟩
    have H : ∀ d' : CircuitDart c, d'.source = t → dartIsUp d' = false := by
      intro d' hd'
      unfold dartIsUp
      have hadj : c.edge d'.source d'.target = true ∨ c.edge d'.target d'.source = true := d'.property.1
      rcases hadj with he | he
      · have : c.edge t d'.target = false := ht d'.target
        rw [← hd'] at this
        rw [this] at he
        exact Bool.noConfusion he
      · cases h_eq : c.edge d'.source d'.target
        · rfl
        · have h1 : c.layer d'.source + 1 = c.layer d'.target := hP d'.source d'.target h_eq
          have h2 : c.layer d'.target + 1 = c.layer d'.source := hP d'.target d'.source he
          omega
    have H2 := H d h_src
    simp [H2] at h_up
  · intro h
    simp at h

def vertexRotation (r : OrientableRotation c) (v : Fin c.gateCount) :
    Equiv.Perm {d : CircuitDart c // d.source = v} :=
  r.rotation.subtypePerm (fun d => by rw [r.preservesSource])

/-- The darts leaving a fixed vertex form a single cycle of the rotation. -/
theorem vertexRotation_cyclic (r : OrientableRotation c) (v : Fin c.gateCount)
    (x y : {d : CircuitDart c // d.source = v}) :
    ∃ k : Nat, ((vertexRotation r v) ^ k) x = y := by
  obtain ⟨k, hk⟩ := r.cyclicAtVertex x.1 y.1 (by rw [x.2, y.2])
  refine ⟨k, ?_⟩
  apply Subtype.ext
  rw [vertexRotation, Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply]
  exact hk

/-- Every internal vertex — neither the graph source nor the graph sink — carries
at least one switch corner. -/
theorem one_le_switchCount_of_internal (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) {v : Fin c.gateCount}
    (hns : ¬ IsGraphSource c v) (hnt : ¬ IsGraphSink c v) :
    1 ≤ switchCount r v := by
  classical
  obtain ⟨⟨du, hdu, hup⟩, ⟨dd, hdd, hdown⟩⟩ :=
    exists_updown_dart_of_internal hP hS hT hns hnt
  obtain ⟨x, hx1, hx2⟩ :=
    exists_switch_of_cycle (vertexRotation r v) (vertexRotation_cyclic r v)
      (fun d : {d : CircuitDart c // d.source = v} => dartIsUp d.1)
      (a := ⟨du, hdu⟩) (b := ⟨dd, hdd⟩) hup hdown
  have hxv : x.1.source = v := x.2
  have hrot : dartIsUp (r.rotation x.1) = false := by
    have : ((vertexRotation r v) x).1 = r.rotation x.1 := rfl
    rw [← this]
    exact hx2
  rw [switchCount, Finset.one_le_card]
  exact ⟨x.1, by simp [hxv, hx1, hrot]⟩

instance instDecidableIsGraphSource (v : Fin c.gateCount) :
    Decidable (IsGraphSource c v) := by
  unfold IsGraphSource
  infer_instance

instance instDecidableIsGraphSink (v : Fin c.gateCount) :
    Decidable (IsGraphSink c v) := by
  unfold IsGraphSink
  infer_instance

/-- Every internal vertex contributes at least one switch corner, so the number
of internal vertices is a lower bound for the total switch count. -/
theorem card_internal_le_sum_switchCount (hP : ProperLayered c)
    (hS : ∃! s, IsGraphSource c s) (hT : ∃! t, IsGraphSink c t)
    (r : OrientableRotation c) :
    (Finset.univ.filter fun v : Fin c.gateCount =>
        ¬ IsGraphSource c v ∧ ¬ IsGraphSink c v).card
      ≤ ∑ v : Fin c.gateCount, switchCount r v := by
  classical
  set S : Finset (Fin c.gateCount) :=
    Finset.univ.filter fun v : Fin c.gateCount =>
      ¬ IsGraphSource c v ∧ ¬ IsGraphSink c v with hSdef
  have h1 : S.card ≤ ∑ v ∈ S, switchCount r v := by
    have : ∑ _v ∈ S, 1 ≤ ∑ v ∈ S, switchCount r v := by
      refine Finset.sum_le_sum ?_
      intro v hv
      rw [hSdef, Finset.mem_filter] at hv
      exact one_le_switchCount_of_internal hP hS hT r hv.2.1 hv.2.2
    simpa using this
  exact h1.trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))

/-! ### Handshake counts for the up/down dichotomy -/

/-- Reversal is a bijection between up-darts and down-darts. -/
theorem card_upDarts_eq_card_downDarts (hP : ProperLayered c) :
    (Finset.univ.filter fun d : CircuitDart c => dartIsUp d = true).card
      = (Finset.univ.filter fun d : CircuitDart c => dartIsUp d = false).card := by
  classical
  refine Finset.card_nbij' (fun d => dartReverse c d) (fun d => dartReverse c d)
    ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hd ⊢
    rw [dartIsUp_dartReverse hP, hd]
    rfl
  · intro d hd
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hd ⊢
    rw [dartIsUp_dartReverse hP, hd]
    rfl
  · intro d _
    exact (dartReverse c).left_inv d
  · intro d _
    exact (dartReverse c).left_inv d

/-- Half of the darts are up-darts, so their number is the number of underlying
edges. -/
theorem card_upDarts_eq_edgeCount (hP : ProperLayered c) :
    (Finset.univ.filter fun d : CircuitDart c => dartIsUp d = true).card
      = underlyingEdgeCount c := by
  classical
  have hsplit :
      (Finset.univ.filter fun d : CircuitDart c => dartIsUp d = true).card
        + (Finset.univ.filter fun d : CircuitDart c => dartIsUp d = false).card
        = Fintype.card (CircuitDart c) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (CircuitDart c))) (fun d => dartIsUp d = true)
    have hneg : {a ∈ (Finset.univ : Finset (CircuitDart c)) | ¬ dartIsUp a = true}
        = Finset.univ.filter fun d : CircuitDart c => dartIsUp d = false := by
      ext d
      simp
    rw [hneg] at h
    simpa [Finset.card_univ] using h
  have htwo := two_mul_underlyingEdgeCount c
  rw [← card_upDarts_eq_card_downDarts hP] at hsplit
  omega

end Internal
end AllenderOQ3
