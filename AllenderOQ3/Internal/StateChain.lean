import AllenderOQ3.Internal.StateRelation

/-!
# The relation chain of a bounded-width circuit (§5–§6, §8)

`AllenderOQ3.Internal.StateRelation` reads a layered circuit of bounded width as
a machine whose configuration after `i` steps is the tuple of gate values on
layer `i`, and provides the purely local one-step relation `OneStep`.

This file closes the loop between that local reading and the global semantics of
the circuit:

* `InitState` is the local description of the layer-`0` configuration.  It is a
  relation on a single state, because in a well-formed circuit no gate on layer
  `0` has a predecessor.
* `Reach idx x i k s t` says that `t` is obtained from the layer-`i`
  configuration `s` by `k` local steps, so it is the layer-`(i + k)`
  configuration.  It is the *block relation* of §8.
* `reach_add` is the composition law that §9 blocks the chain with: a run of
  length `k₁ + k₂` splits at any intermediate point.
* `adrAccepts_iff_reach` is the payoff: the circuit accepts an input exactly when
  the initial configuration reaches, in `c.layer c.output` steps, a configuration
  whose output slot is set.  Together with `reach_deterministic` this is the
  chain-of-relations reformulation of `ADRAccepts` used from §8 on.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat}

/-! ## Layer zero has no predecessors -/

/-- In a well-formed circuit no edge enters a gate on layer `0`, since every edge
raises the layer by exactly one. -/
theorem edge_layer_zero_eq_false {c : ADRCircuit n} (hc : WellFormedADR c)
    {g h : Fin c.gateCount} (hg : c.layer g = 0) : c.edge h g = false := by
  cases he : c.edge h g with
  | false => rfl
  | true =>
      have := hc.1 h g he
      omega

/-! ## The initial configuration -/

/-- The local description of the layer-`0` configuration: every gate of layer `0`
takes the value its gate type dictates (its predecessor set is empty, so the
previous configuration is irrelevant and taken to be all-`false`), and every
unused slot is `false`. -/
def InitState {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    (t : State w) : Prop :=
  (∀ g, (c.kind g).isComputation = true → c.layer g = 0 →
      (t (idx.slot g) = true ↔ GateStepValue idx x (fun _ => false) g)) ∧
  (∀ j : Fin w, (¬ ∃ g, (c.kind g).isComputation = true ∧ c.layer g = 0 ∧ idx.slot g = j) → t j =
    false)

/-- The initial configuration is unique. -/
theorem initState_deterministic {c : ADRCircuit n} (idx : LayerIndexing c w)
    (x : Fin n → Bool) {t t' : State w}
    (h : InitState idx x t) (h' : InitState idx x t') : t = t' := by
  funext j
  by_cases hj : ∃ g, (c.kind g).isComputation = true ∧ c.layer g = 0 ∧ idx.slot g = j
  · obtain ⟨g, hcomp, hg, rfl⟩ := hj
    exact bool_eq_of_iff ((h.1 g hcomp hg).trans (h'.1 g hcomp hg).symm)
  · rw [h.2 j hj, h'.2 j hj]

/-- The layer-`0` configuration read off a genuine valuation satisfies the local
description. -/
theorem initState_stateOf {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation c x value) : InitState idx x (stateOf idx value 0) := by
  constructor
  · intro g hcomp hg
    have hgv := hval g
    have hnopred : ∀ h, c.edge h g = false := fun h => edge_layer_zero_eq_false hc hg
    rw [stateOf_slot idx value hg hcomp]
    unfold GateStepValue
    cases hk : c.kind g with
    | literal j b =>
        simp only [hk, ADRGate.isComputation] at hcomp
        contradiction
    | andGate =>
        simp only [hk] at hgv ⊢
        rw [hgv]
        constructor
        · intro _ h he; rw [hnopred h] at he; exact absurd he (by simp)
        · intro _ h he; rw [hnopred h] at he; exact absurd he (by simp)
    | orGate =>
        simp only [hk] at hgv ⊢
        rw [hgv]
        constructor
        · rintro ⟨h, he, -⟩; rw [hnopred h] at he; exact absurd he (by simp)
        · rintro ⟨h, he, -⟩; rw [hnopred h] at he; exact absurd he (by simp)
  · intro j hj
    unfold stateOf
    simp only [decide_eq_false_iff_not, not_exists]
    rintro g ⟨hcomp, hg, hslot, -⟩
    exact hj ⟨g, hcomp, hg, hslot⟩

/-! ## Block relations -/

/-- `Reach idx x i k s t`: starting from the layer-`i` configuration `s`, the
machine reaches the configuration `t` after `k` local steps, i.e. `t` is the
layer-`(i + k)` configuration.  This is the block relation of §8. -/
def Reach {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool) :
    Nat → Nat → State w → State w → Prop
  | _, 0, s, t => s = t
  | i, (k + 1), s, t => ∃ u, OneStep idx x i s u ∧ Reach idx x (i + 1) k u t

@[simp] theorem reach_zero {c : ADRCircuit n} (idx : LayerIndexing c w)
    (x : Fin n → Bool) (i : Nat) (s t : State w) :
    Reach idx x i 0 s t ↔ s = t := Iff.rfl

@[simp] theorem reach_succ {c : ADRCircuit n} (idx : LayerIndexing c w)
    (x : Fin n → Bool) (i k : Nat) (s t : State w) :
    Reach idx x i (k + 1) s t ↔ ∃ u, OneStep idx x i s u ∧ Reach idx x (i + 1) k u t :=
  Iff.rfl

/-- A one-step transition is a block of length one. -/
theorem reach_one {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    (i : Nat) {s t : State w} (h : OneStep idx x i s t) : Reach idx x i 1 s t :=
  ⟨t, h, rfl⟩

/-- Block relations compose: a run of length `k₁ + k₂` is a run of length `k₁`
followed by a run of length `k₂`.  This is the composition law that §9 uses to
block a long chain into a constant number of rounds. -/
theorem reach_add {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool) :
    ∀ (k₁ k₂ i : Nat) (s t : State w),
      Reach idx x i (k₁ + k₂) s t ↔
        ∃ u, Reach idx x i k₁ s u ∧ Reach idx x (i + k₁) k₂ u t := by
  intro k₁
  induction k₁ with
  | zero =>
      intro k₂ i s t
      simp only [Nat.zero_add, Nat.add_zero, reach_zero]
      constructor
      · intro h
        exact ⟨s, rfl, h⟩
      · rintro ⟨u, rfl, h⟩
        exact h
  | succ k ih =>
      intro k₂ i s t
      have hsum : k + 1 + k₂ = (k + k₂) + 1 := by omega
      have hi : i + (k + 1) = i + 1 + k := by omega
      rw [hsum]
      constructor
      · rintro ⟨u, hstep, hrest⟩
        obtain ⟨v, h1, h2⟩ := (ih k₂ (i + 1) u t).mp hrest
        exact ⟨v, ⟨u, hstep, h1⟩, by rw [hi]; exact h2⟩
      · rintro ⟨u, hsu, hut⟩
        obtain ⟨v, hstep, hv⟩ := hsu
        rw [hi] at hut
        exact ⟨v, hstep, (ih k₂ (i + 1) v t).mpr ⟨u, hv, hut⟩⟩

/-- Block relations are deterministic. -/
theorem reach_deterministic {c : ADRCircuit n} (idx : LayerIndexing c w)
    (x : Fin n → Bool) : ∀ (k i : Nat) {s t t' : State w},
      Reach idx x i k s t → Reach idx x i k s t' → t = t' := by
  intro k
  induction k with
  | zero => intro i s t t' h h'; rw [← h, ← h']
  | succ k ih =>
      rintro i s t t' ⟨u, hu, hut⟩ ⟨u', hu', hut'⟩
      have : u = u' := oneStep_deterministic idx x hu hu'
      subst this
      exact ih (i + 1) hut hut'

/-- The configurations read off a genuine valuation form a run of the block
relation. -/
theorem reach_stateOf {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation c x value) :
    ∀ (k i : Nat), Reach idx x i k (stateOf idx value i) (stateOf idx value (i + k)) := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih =>
      intro i
      refine ⟨stateOf idx value (i + 1), oneStep_stateOf hc idx hval i, ?_⟩
      have hi : i + 1 + k = i + (k + 1) := by omega
      have := ih (i + 1)
      rwa [hi] at this

/-! ## Totality of the transition relation -/

/-- The one-step relation is total: every configuration has a successor.  The successor
is read off the local gate conditions, using injectivity of the slot assignment on a
layer to make the definition consistent. -/
theorem exists_oneStep {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    (i : Nat) (s : State w) : ∃ t, OneStep idx x i s t := by
  classical
  refine ⟨fun j => decide (∃ g, (c.kind g).isComputation = true ∧ c.layer g = i + 1 ∧
      idx.slot g = j ∧ GateStepValue idx x s g), ?_, ?_⟩
  · intro g hcomp hg
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨g', hcomp', hg', hslot, hgsv⟩
      have : g' = g := idx.injOnLayer g' g hcomp' hcomp (by rw [hg', hg]) hslot
      subst this
      exact hgsv
    · intro h
      exact ⟨g, hcomp, hg, rfl, h⟩
  · intro j hj
    simp only [decide_eq_false_iff_not, not_exists]
    rintro g ⟨hcomp, hg, hslot, -⟩
    exact hj ⟨g, hcomp, hg, hslot⟩

/-- The block relation is total: from every configuration some configuration is reached
in `m` steps. -/
theorem exists_reach {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool) :
    ∀ (m i : Nat) (s : State w), ∃ t, Reach idx x i m s t := by
  intro m
  induction m with
  | zero => intro i s; exact ⟨s, rfl⟩
  | succ m ih =>
      intro i s
      obtain ⟨u, hu⟩ := exists_oneStep idx x i s
      obtain ⟨t, ht⟩ := ih (i + 1) u
      exact ⟨t, u, hu, ht⟩

/-- A slot not used by any computation gate of the target layer is `false` in every
configuration reached by a run of positive length. -/
theorem reach_padded {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    {i m : Nat} (hm : 1 ≤ m) {s t : State w} (h : Reach idx x i m s t) (j : Fin w)
    (hj : ¬ ∃ g, (c.kind g).isComputation = true ∧ c.layer g = i + m ∧ idx.slot g = j) :
    t j = false := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨u, hu, hut⟩ := (reach_add idx x m' 1 i s t).mp h
  obtain ⟨v, hstep, hvt⟩ := hut
  have hvt' : v = t := hvt
  subst hvt'
  refine hstep.2 j ?_
  rintro ⟨g, hcomp, hg, hslot⟩
  exact hj ⟨g, hcomp, by omega, hslot⟩

/-- **Bitwise characterisation of the block relation.**  Since the relation is
deterministic and total, a configuration `t` is the one reached from `s` in `m` steps
exactly when each of its bits agrees with the corresponding reachability bit. -/
theorem reach_iff_bits {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    (i m : Nat) (s t : State w) :
    Reach idx x i m s t ↔
      ∀ j : Fin w, (t j = true ↔ ∃ t', Reach idx x i m s t' ∧ t' j = true) := by
  constructor
  · intro h j
    constructor
    · intro hj; exact ⟨t, h, hj⟩
    · rintro ⟨t', h', hj⟩
      rwa [reach_deterministic idx x m i h' h] at hj
  · intro hbits
    obtain ⟨t₀, ht₀⟩ := exists_reach idx x m i s
    have hteq : t = t₀ := by
      funext j
      have hj := hbits j
      cases htj : t j with
      | true =>
          obtain ⟨t', h', hj'⟩ := hj.mp htj
          rw [reach_deterministic idx x m i h' ht₀] at hj'
          exact hj'.symm
      | false =>
          cases ht₀j : t₀ j with
          | true =>
              have hcontra := hj.mpr ⟨t₀, ht₀, ht₀j⟩
              rw [htj] at hcontra
              exact absurd hcontra (by simp)
          | false => rfl
    subst hteq
    exact ht₀

/-! ## Acceptance as a chain of state relations -/

/-- **Chain characterization of acceptance.**  A well-formed circuit accepts an
input exactly when the initial configuration reaches, in `c.layer c.output`
local steps, a configuration whose output slot is set.

This is the reformulation of `ADRAccepts` as a chain of constant-size state
relations: an initial relation, `c.layer c.output` one-step relations, and a
final output test. -/
theorem adrAccepts_iff_reach {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) (x : Fin n → Bool)
    (h_out_comp : (c.kind c.output).isComputation = true) :
    ADRAccepts c x ↔
      ∃ s t : State w, InitState idx x s ∧
        Reach idx x 0 (c.layer c.output) s t ∧ t (idx.slot c.output) = true := by
  constructor
  · rintro ⟨value, hval, hout⟩
    refine ⟨stateOf idx value 0, stateOf idx value (c.layer c.output),
      initState_stateOf hc idx hval, ?_, ?_⟩
    · have := reach_stateOf hc idx hval (c.layer c.output) 0
      simpa using this
    · rw [stateOf_slot idx value rfl h_out_comp]
      exact hout
  · rintro ⟨s, t, hinit, hreach, hout⟩
    refine ⟨evalADR c hc x, (adrValuation_iff_eq_evalADR hc).mpr rfl, ?_⟩
    have hval : ADRValuation c x (evalADR c hc x) :=
      (adrValuation_iff_eq_evalADR hc).mpr rfl
    have hs : s = stateOf idx (evalADR c hc x) 0 :=
      initState_deterministic idx x hinit (initState_stateOf hc idx hval)
    subst hs
    have hrun := reach_stateOf hc idx hval (c.layer c.output) 0
    have ht : t = stateOf idx (evalADR c hc x) (c.layer c.output) :=
      reach_deterministic idx x (c.layer c.output) 0 hreach (by simpa using hrun)
    subst ht
    rw [stateOf_slot idx (evalADR c hc x) rfl h_out_comp] at hout
    exact hout

end AllenderOQ3.Internal
