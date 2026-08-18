import AllenderOQ3.Internal.NonCrossingEval
import AllenderOQ3.Internal.NonCrossingDefs

/-!
# Route-2 (certificate-aligned) evaluation semantics

`layerTransMap c cert x ell` is the transition of the *whole* layer, literal
ports included, indexed by the incidence certificate's own layer order.  This
file proves that it really evaluates the circuit:

* `fullState c cert value ell w` is the width-`w` configuration carried at layer
  `ell` by a valuation `value` of the circuit;
* `initConfig c cert x w` is the layer-`0` configuration, written directly in
  terms of the input (no valuation needed);
* `layerTransMap_fullState` — one layer transition takes the layer-`ell`
  configuration to the layer-`(ell+1)` configuration;
* `fullState_eq_runTrans_word` — iterating gives the word product of the layer
  letters applied to the initial configuration;
* `adrAccepts_iff_runTrans_word` — acceptance of the ADR circuit is the value of
  the output slot of that word product.

Everything is stated for a fixed width bound `TotalWidthAtMost c w`, which is
what guarantees that every layer vertex has a slot below `w`.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)

/-- The certificate's layer order for layer `ell` is no longer than the width
bound. -/
theorem layerOrder_length_le {w : Nat} (hW : TotalWidthAtMost c w) (ell : Nat) :
    (cert.layerOrder ell).entries.length ≤ w :=
  (layerOrder_length_eq_card c cert ell).le.trans (hW ell)

/-- The slot of a layer vertex is below the width bound. -/
theorem fullIndex_lt {w : Nat} (hW : TotalWidthAtMost c w) (ell : Nat)
    (v : LayerVertex c ell) : (FullLayerIndexing c cert ell v).val < w :=
  lt_of_lt_of_le (FullLayerIndexing c cert ell v).isLt (layerOrder_length_le c cert hW ell)

/-- The width-`w` configuration carried at layer `ell` by a valuation of the
circuit. -/
noncomputable def fullState (value : Fin c.gateCount → Bool) (ell w : Nat) : Config w :=
  fun j =>
    if h : j.val < (cert.layerOrder ell).entries.length then
      value ((FullLayerIndexing c cert ell).symm ⟨j.val, h⟩).val
    else false

/-- Reading the slot of a layer vertex off the layer configuration returns the
value of that vertex. -/
theorem fullState_apply {w : Nat} (value : Fin c.gateCount → Bool) {ell : Nat}
    (v : LayerVertex c ell) (j : Fin w)
    (hj : (FullLayerIndexing c cert ell v).val = j.val) :
    fullState c cert value ell w j = value v.val := by
  have hlt : j.val < (cert.layerOrder ell).entries.length := by
    rw [← hj]; exact (FullLayerIndexing c cert ell v).isLt
  have hsymm : (FullLayerIndexing c cert ell).symm ⟨j.val, hlt⟩ = v := by
    have : (⟨j.val, hlt⟩ : Fin (cert.layerOrder ell).entries.length)
        = FullLayerIndexing c cert ell v := Fin.ext hj.symm
    rw [this, Equiv.symm_apply_apply]
  simp only [fullState, dif_pos hlt, hsymm]

/-- The layer-`0` configuration, written directly in terms of the input.  A
layer-`0` `andGate` has no predecessors, hence value `true`; a layer-`0`
`orGate` has value `false`. -/
noncomputable def initConfig (x : Fin n → Bool) (w : Nat) : Config w :=
  fun j =>
    if h : j.val < (cert.layerOrder 0).entries.length then
      match c.kind ((FullLayerIndexing c cert 0).symm ⟨j.val, h⟩).val with
      | .literal i b => if b then !(x i) else x i
      | .andGate => true
      | .orGate => false
    else false

/-- **One layer transition evaluates one layer of the circuit.** -/
theorem layerTransMap_fullState {w : Nat} (hc : WellFormedADR c)
    (hW : TotalWidthAtMost c w) {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation c x value) (ell : Nat) :
    layerTransMap c cert x ell (fullState c cert value ell w)
      = fullState c cert value (ell + 1) w := by
  funext j
  by_cases h : j.val < (cert.layerOrder (ell + 1)).entries.length
  · set v : LayerVertex c (ell + 1) :=
      (FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, h⟩ with hv
    have hrhs : fullState c cert value (ell + 1) w j = value v.val := by
      simp only [fullState, dif_pos h, hv]
    -- predecessors of `v` live on layer `ell` and have a slot below `w`
    have hlay : ∀ u : Fin c.gateCount, c.edge u v.val = true → c.layer u = ell := by
      intro u hu
      have h1 := hc.1 u v.val hu
      have hv2 : c.layer v.val = ell + 1 := v.property
      omega
    have hslot : ∀ (u : Fin c.gateCount) (hu : c.layer u = ell),
        (FullLayerIndexing c cert ell ⟨u, hu⟩).val < w :=
      fun u hu => fullIndex_lt c cert hW ell ⟨u, hu⟩
    rw [hrhs]
    have hvalv := hval v.val
    cases hk : c.kind v.val with
    | literal i b =>
        simp only [hk] at hvalv
        simp only [layerTransMap, dif_pos h, ← hv, hk]
        exact hvalv.symm
    | andGate =>
        simp only [hk] at hvalv
        simp only [layerTransMap, dif_pos h, ← hv, hk]
        refine (bool_eq_of_iff ?_).symm
        rw [hvalv, decide_eq_true_eq]
        constructor
        · intro hall u hu
          rw [dif_pos (hlay u hu), dif_pos (hslot u (hlay u hu)),
            fullState_apply c cert value ⟨u, hlay u hu⟩
              ⟨(FullLayerIndexing c cert ell ⟨u, hlay u hu⟩).val, hslot u (hlay u hu)⟩ rfl]
          exact hall u hu
        · intro hall u hu
          have hu' := hall u hu
          rw [dif_pos (hlay u hu), dif_pos (hslot u (hlay u hu)),
            fullState_apply c cert value ⟨u, hlay u hu⟩
              ⟨(FullLayerIndexing c cert ell ⟨u, hlay u hu⟩).val, hslot u (hlay u hu)⟩ rfl] at hu'
          exact hu'
    | orGate =>
        simp only [hk] at hvalv
        simp only [layerTransMap, dif_pos h, ← hv, hk]
        refine (bool_eq_of_iff ?_).symm
        rw [hvalv, decide_eq_true_eq]
        constructor
        · rintro ⟨u, hu, huv⟩
          refine ⟨u, hu, ?_⟩
          rw [dif_pos (hlay u hu), dif_pos (hslot u (hlay u hu)),
            fullState_apply c cert value ⟨u, hlay u hu⟩
              ⟨(FullLayerIndexing c cert ell ⟨u, hlay u hu⟩).val, hslot u (hlay u hu)⟩ rfl]
          exact huv
        · rintro ⟨u, hu, huv⟩
          refine ⟨u, hu, ?_⟩
          rw [dif_pos (hlay u hu), dif_pos (hslot u (hlay u hu)),
            fullState_apply c cert value ⟨u, hlay u hu⟩
              ⟨(FullLayerIndexing c cert ell ⟨u, hlay u hu⟩).val, hslot u (hlay u hu)⟩ rfl] at huv
          exact huv
  · simp only [layerTransMap, fullState, dif_neg h]

/-- **The layer-`0` configuration of any valuation is the input configuration.** -/
theorem fullState_zero {w : Nat} (hc : WellFormedADR c) {x : Fin n → Bool}
    {value : Fin c.gateCount → Bool} (hval : ADRValuation c x value) :
    fullState c cert value 0 w = initConfig c cert x w := by
  funext j
  by_cases h : j.val < (cert.layerOrder 0).entries.length
  · set v : LayerVertex c 0 := (FullLayerIndexing c cert 0).symm ⟨j.val, h⟩ with hv
    have hnoedge : ∀ u, c.edge u v.val = false := by
      intro u
      by_contra hu
      simp only [Bool.not_eq_false] at hu
      have := hc.1 u v.val hu
      have hv0 : c.layer v.val = 0 := v.property
      omega
    have hvalv := hval v.val
    have hlhs : fullState c cert value 0 w j = value v.val := by
      simp only [fullState, dif_pos h, hv]
    rw [hlhs]
    cases hk : c.kind v.val with
    | literal i b =>
        simp only [hk] at hvalv
        simp only [initConfig, dif_pos h, ← hv, hk]
        exact hvalv
    | andGate =>
        simp only [hk] at hvalv
        simp only [initConfig, dif_pos h, ← hv, hk]
        rw [hvalv]
        intro u hu
        rw [hnoedge u] at hu
        exact absurd hu Bool.false_ne_true
    | orGate =>
        simp only [hk] at hvalv
        simp only [initConfig, dif_pos h, ← hv, hk]
        refine Bool.eq_false_iff.mpr fun hcon => ?_
        obtain ⟨u, hu, -⟩ := hvalv.mp hcon
        rw [hnoedge u] at hu
        exact Bool.false_ne_true hu
  · simp only [fullState, initConfig, dif_neg h]

/-- **Iterating the layer letters evaluates the circuit.**  The configuration at
layer `ell` is the product of the first `ell` layer letters applied to the input
configuration. -/
theorem fullState_eq_runTrans_word {w : Nat} (hc : WellFormedADR c)
    (hW : TotalWidthAtMost c w) {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation c x value) (ell : Nat) :
    fullState c cert value ell w
      = runTrans (wordEnd ((List.range ell).map (fun i => layerTrans c cert x i)))
          (initConfig c cert x w) := by
  induction ell with
  | zero => simpa using fullState_zero (w := w) c cert hc hval
  | succ ell ih =>
      rw [List.range_succ, List.map_append, wordEnd_append, runTrans_mul, ← ih]
      simp only [List.map_cons, List.map_nil, wordEnd_cons, wordEnd_nil, mul_one]
      rw [layerTrans, runTrans_ofConfigMap]
      exact (layerTransMap_fullState c cert hc hW hval ell).symm

/-- **Acceptance of the ADR circuit is a slot of the word product.**  With `j`
the slot of the output gate in its own layer, the circuit accepts `x` exactly
when the product of the layer letters, applied to the input configuration, is
`true` at slot `j`. -/
theorem adrAccepts_iff_runTrans_word {w : Nat} (hc : WellFormedADR c)
    (hW : TotalWidthAtMost c w) (x : Fin n → Bool) (j : Fin w)
    (hj : (FullLayerIndexing c cert (c.layer c.output) ⟨c.output, rfl⟩).val = j.val) :
    ADRAccepts c x ↔
      runTrans (wordEnd ((List.range (c.layer c.output)).map (fun i => layerTrans c cert x i)))
        (initConfig c cert x w) j = true := by
  obtain ⟨value, hval⟩ := adrValuation_exists c hc x
  have hstate := fullState_eq_runTrans_word c cert hc hW hval (c.layer c.output)
  have hslot : fullState c cert value (c.layer c.output) w j = value c.output :=
    fullState_apply c cert value ⟨c.output, rfl⟩ j hj
  rw [← congrFun hstate j, hslot]
  constructor
  · rintro ⟨value', hval', hout⟩
    rwa [adrValuation_unique hc hval' hval] at hout
  · intro hout
    exact ⟨value, hval, hout⟩

end AllenderOQ3.Internal
