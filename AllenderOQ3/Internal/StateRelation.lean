import AllenderOQ3.Internal.Semantics

/-!
# Bounded-width states and the one-step transition relation

A layered ADR circuit of bounded width can be read as a machine whose
configuration after `i` steps is the tuple of values carried by the gates of
layer `i`.  This file sets up that reading.

* `LayerIndexing c w` assigns to every gate a *slot* in `Fin w`, injectively on
  each layer for computation gates.
* `State w` is a configuration: one Boolean per slot.
* `OneStep c idx x i s t` says that `t` is the layer-`(i+1)` configuration
  obtained from the layer-`i` configuration `s`.
* `oneStep_deterministic` — the relation is a partial function.
* `stateOf` and `oneStep_stateOf` — the configurations read off an actual
  valuation of the circuit do satisfy the transition relation.
* `paddedValid_stateOf` — if all computation gates of a layer use slots below `k`,
  the configuration of that layer is `false` on every slot from `k` on.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat}

/-- A configuration of a width-`w` machine: one Boolean per slot. -/
def State (w : Nat) := Fin w → Bool

/-- A slot assignment for the gates of a circuit which is injective on every
layer for computation gates. -/
structure LayerIndexing (c : ADRCircuit n) (w : Nat) where
  slot : Fin c.gateCount → Fin w
  injOnLayer : ∀ g h, (c.kind g).isComputation = true → (c.kind h).isComputation = true → c.layer g
    = c.layer h → slot g = slot h → g = h

/-- The configuration `s` is `false` on all slots from `activeSlots` on. -/
def PaddedValid (s : State w) (activeSlots : Nat) : Prop :=
  ∀ i : Fin w, activeSlots ≤ i.val → s i = false

/-- Evaluates a predecessor's value, reading from the state `s` if it's a
computation gate, or from the input `x` if it's a literal. -/
def predValue {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    (s : State w) (h : Fin c.gateCount) : Bool :=
  match c.kind h with
  | .literal i b => if b then !(x i) else x i
  | .andGate => s (idx.slot h)
  | .orGate => s (idx.slot h)

/-- The value that gate `g` must take, computed locally from the configuration
`s` holding the values of the previous layer and `x` for literal inputs. -/
def GateStepValue {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    (s : State w) (g : Fin c.gateCount) : Prop :=
  match c.kind g with
  | .literal i b => (if b then !(x i) else x i) = true
  | .andGate => ∀ h, c.edge h g = true → predValue idx x s h = true
  | .orGate => ∃ h, c.edge h g = true ∧ predValue idx x s h = true

/-- `t` is the configuration of layer `i + 1` produced from the configuration `s`
of layer `i`. -/
def OneStep {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    (i : Nat) (s t : State w) : Prop :=
  (∀ g, (c.kind g).isComputation = true → c.layer g = i + 1 →
    (t (idx.slot g) = true ↔ GateStepValue idx x s g)) ∧
  (∀ j : Fin w, (¬ ∃ g, (c.kind g).isComputation = true ∧ c.layer g = i + 1 ∧ idx.slot g = j) → t j
    = false)

/-- The one-step relation is deterministic: the successor configuration of a
given configuration is unique. -/
theorem oneStep_deterministic {c : ADRCircuit n} (idx : LayerIndexing c w)
    (x : Fin n → Bool) {i : Nat} {s t t' : State w}
    (h : OneStep idx x i s t) (h' : OneStep idx x i s t') : t = t' := by
  funext j
  by_cases hj : ∃ g, (c.kind g).isComputation = true ∧ c.layer g = i + 1 ∧ idx.slot g = j
  · obtain ⟨g, hg_comp, hg_layer, rfl⟩ := hj
    exact bool_eq_of_iff ((h.1 g hg_comp hg_layer).trans (h'.1 g hg_comp hg_layer).symm)
  · rw [h.2 j hj, h'.2 j hj]

/-- The configuration of layer `i` carried by a family of gate values. -/
def stateOf {c : ADRCircuit n} (idx : LayerIndexing c w)
    (value : Fin c.gateCount → Bool) (i : Nat) : State w :=
  fun j => decide
    (∃ g, (c.kind g).isComputation = true ∧ c.layer g = i ∧ idx.slot g = j ∧ value g = true)

/-- Reading the slot of a computation gate of layer `i` off the layer-`i` configuration
returns the value of that gate.  This is where injectivity of the slot
assignment on a layer is used. -/
theorem stateOf_slot {c : ADRCircuit n} (idx : LayerIndexing c w)
    (value : Fin c.gateCount → Bool) {i : Nat} {g : Fin c.gateCount}
    (hg : c.layer g = i) (hcomp : (c.kind g).isComputation = true) :
    stateOf idx value i (idx.slot g) = value g := by
  unfold stateOf
  cases hv : value g with
  | true => simp only [decide_eq_true_eq]; exact ⟨g, hcomp, hg, rfl, hv⟩
  | false =>
      simp only [decide_eq_false_iff_not, not_exists]
      rintro g' ⟨hcomp', hg', hslot, hv'⟩
      have : g' = g := idx.injOnLayer g' g hcomp' hcomp (by rw [hg', hg]) hslot
      rw [this, hv] at hv'
      exact Bool.noConfusion hv'

/-- If every computation gate of layer `i` uses a slot below `k`, then the configuration of
layer `i` is padded with `false` from slot `k` on. -/
theorem paddedValid_stateOf {c : ADRCircuit n} (idx : LayerIndexing c w)
    (value : Fin c.gateCount → Bool) {i k : Nat}
    (hk : ∀ g, (c.kind g).isComputation = true → c.layer g = i → (idx.slot g).val < k) :
    PaddedValid (stateOf idx value i) k := by
  intro j hj
  unfold stateOf
  simp only [decide_eq_false_iff_not, not_exists]
  rintro g ⟨hcomp, hg, hslot, -⟩
  have := hk g hcomp hg
  rw [hslot] at this
  omega

/-- The configurations read off a genuine valuation of the circuit satisfy the
local transition relation. -/
theorem oneStep_stateOf {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation c x value) (i : Nat) :
    OneStep idx x i (stateOf idx value i) (stateOf idx value (i + 1)) := by
  constructor
  · intro g hcomp hg
    have hgv := hval g
    have hpred : ∀ h, c.edge h g = true →
        predValue idx x (stateOf idx value i) h = value h := by
      intro h he
      have hlayer := hc.1 h g he
      unfold predValue
      cases hk : c.kind h with
      | literal j b =>
          have hh := hval h
          simp only [hk] at hh ⊢
          exact hh.symm
      | andGate =>
          have : (c.kind h).isComputation = true := by simp [hk, ADRGate.isComputation]
          exact stateOf_slot idx value (by omega) this
      | orGate =>
          have : (c.kind h).isComputation = true := by simp [hk, ADRGate.isComputation]
          exact stateOf_slot idx value (by omega) this
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
        · intro H h he; rw [hpred h he]; exact H h he
        · intro H h he; rw [← hpred h he]; exact H h he
    | orGate =>
        simp only [hk] at hgv ⊢
        rw [hgv]
        constructor
        · rintro ⟨h, he, hv⟩; exact ⟨h, he, by rw [hpred h he]; exact hv⟩
        · rintro ⟨h, he, hv⟩; exact ⟨h, he, by rw [← hpred h he]; exact hv⟩
  · intro j hj
    unfold stateOf
    simp only [decide_eq_false_iff_not, not_exists]
    rintro g ⟨hcomp, hg, hslot, -⟩
    exact hj ⟨g, hcomp, hg, hslot⟩

end AllenderOQ3.Internal
