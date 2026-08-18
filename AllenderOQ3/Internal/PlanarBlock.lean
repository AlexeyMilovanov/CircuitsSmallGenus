import AllenderOQ3.Internal.Assembly
import AllenderOQ3.Internal.StateRelation
import AllenderOQ3.Internal.Blocking
import AllenderOQ3.Internal.LayerPlanarizer
import AllenderOQ3.Internal.EdgeBudget
import AllenderOQ3.Internal.CountInvariance
import AllenderOQ3.Internal.BlockGenus
import AllenderOQ3.Internal.ACCLocal
import AllenderOQ3.Internal.ACCNot

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat}

/-!
# Planar block relations (§8)

For each planar interval and boundary pair (s,t), an ACC relation deciding the block
via B6 on each output bit, plus padded state equalities.
-/

def blockMask (c : ADRCircuit n) (P : Finset Nat) (k l : Nat) (a b : Fin c.gateCount) : Bool :=
  decide (k ≤ c.layer a ∧ c.layer b ≤ l ∧ c.layer a ∉ P ∧ c.layer b ∉ P ∧ c.layer b ≠ k)

def hardwireState (c : ADRCircuit n) (idx : LayerIndexing c w) (P : Finset Nat) (k l : Nat)
    (s : State w) (outGate : Fin c.gateCount) : ADRCircuit n :=
  let c' := maskCircuit c (blockMask c P k l)
  { c' with
    output := outGate
    kind := fun g =>
      if (c.kind g).isComputation = true ∧ c.layer g = k then
        if s (idx.slot g) then .andGate else .orGate
      else c.kind g }

theorem wellFormedADR_hardwireState {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) (P : Finset Nat) (k l : Nat) (s : State w)
    (outGate : Fin c.gateCount) :
    WellFormedADR (hardwireState c idx P k l s outGate) := by
  constructor
  · intro u v huv
    dsimp [hardwireState, blockMask, maskCircuit] at huv
    split at huv
    · exact hc.1 u v huv
    · contradiction
  · intro g hg huv
    dsimp [hardwireState, blockMask, maskCircuit] at hg huv ⊢
    split at hg
    · rename_i hk
      obtain ⟨i, b, hcon⟩ := hg
      by_cases hs : s (idx.slot g) = true
      · rw [if_pos hs] at hcon; contradiction
      · rw [if_neg hs] at hcon; contradiction
    · rename_i hk
      push_neg at hk
      have h1 := hc.2 g hg huv
      split
      · exact h1
      · rfl

theorem width_hardwireState {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    {wMax : Nat} (hw : TotalWidthAtMost c wMax) :
    TotalWidthAtMost (hardwireState c idx P k l s outGate) wMax := by
  intro ell
  change (Finset.univ.filter (fun g : Fin c.gateCount => c.layer g = ell)).card ≤ wMax
  exact hw ell

def dartEquiv_hardwireState {c : ADRCircuit n} (idx : LayerIndexing c w) (P : Finset Nat)
    (k l : Nat) (s : State w) (outGate : Fin c.gateCount) :
    CircuitDart (hardwireState c idx P k l s outGate)
      ≃ CircuitDart (maskCircuit c (blockMask c P k l)) where
  toFun d := ⟨d.1, d.2⟩
  invFun d := ⟨d.1, d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem genus_hardwireState {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount) :
    orientableCircuitGenus (hardwireState c idx P k l s outGate)
      = orientableCircuitGenus (maskCircuit c (blockMask c P k l)) := by
  classical
  set c₁ := hardwireState c idx P k l s outGate
  set c₂ := maskCircuit c (blockMask c P k l)
  set phi := dartEquiv_hardwireState idx P k l s outGate
  have hs : ∀ d e : CircuitDart c₁, (phi d).source = (phi e).source ↔ d.source = e.source := by
    intro d e; rfl
  have hs' : ∀ d e : CircuitDart c₂, (phi.symm d).source = (phi.symm e).source ↔ d.source = e.source := by
    intro d e; rfl
  have hr : ∀ d : CircuitDart c₁, phi (dartReverse c₁ d) = dartReverse c₂ (phi d) := by
    intro d; rfl
  have hr' : ∀ d : CircuitDart c₂, phi.symm (dartReverse c₂ d) = dartReverse c₁ (phi.symm d) := by
    intro d; rfl
  have harith : ∀ F : Nat,
      (2 * componentCount c₁ + underlyingEdgeCount c₁ - c₁.gateCount - (F + isolatedVertexCount c₁)) / 2
        = (2 * componentCount c₂ + underlyingEdgeCount c₂ - c₂.gateCount - (F + isolatedVertexCount c₂)) / 2 := by
    have hC : componentCount c₁ = componentCount c₂ := rfl
    have hI : isolatedVertexCount c₁ = isolatedVertexCount c₂ := rfl
    have hE : underlyingEdgeCount c₁ = underlyingEdgeCount c₂ := rfl
    have hV : c₁.gateCount = c₂.gateCount := rfl
    intro F; rw [hC, hI, hE, hV]
  have hfwd : ∀ r : OrientableRotation c₂, rotationGenus (transportRotation phi hs r) = rotationGenus r := by
    intro r
    have hface : permCycleCount (facePermutation (transportRotation phi hs r))
        = permCycleCount (facePermutation r) :=
      permCycleCount_facePermutation_transport phi hs hr r
    unfold rotationGenus
    simp only [hface]
    exact harith _
  have hbwd : ∀ r : OrientableRotation c₁, rotationGenus (transportRotation phi.symm hs' r) = rotationGenus r := by
    intro r
    have hface : permCycleCount (facePermutation (transportRotation phi.symm hs' r))
        = permCycleCount (facePermutation r) :=
      permCycleCount_facePermutation_transport phi.symm hs' hr' r
    unfold rotationGenus
    simp only [hface]
    exact (harith _).symm
  unfold orientableCircuitGenus
  congr 1
  ext g
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨transportRotation phi.symm hs' r, by rw [hbwd]; exact hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨transportRotation phi hs r, by rw [hfwd]; exact hr⟩

theorem rotationPlanar_hardwireState {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    (hplanar : RotationPlanar (maskCircuit c (blockMask c P k l))) :
    RotationPlanar (hardwireState c idx P k l s outGate) := by
  rw [rotationPlanar_iff_genus_zero] at hplanar ⊢
  rw [genus_hardwireState]
  exact hplanar

/-!
## Projection lemmas for `hardwireState`

`hardwireState` overrides only `output` (to `outGate`) and the `kind` of the hardwired
boundary gates; `gateCount`, `layer`, and the masked `edge` relation are inherited verbatim
from `maskCircuit c (blockMask c P k l)`.  These mirror the `maskCircuit_*` simp lemmas and are
the scaffolding a downstream evaluation (B2b) of the block uses.
-/

@[simp] theorem hardwireState_gateCount {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount) :
    (hardwireState c idx P k l s outGate).gateCount = c.gateCount := rfl

@[simp] theorem hardwireState_layer {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    (g : Fin c.gateCount) :
    (hardwireState c idx P k l s outGate).layer g = c.layer g := rfl

@[simp] theorem hardwireState_output {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount) :
    (hardwireState c idx P k l s outGate).output = outGate := rfl

@[simp] theorem hardwireState_edge {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    (a b : Fin c.gateCount) :
    (hardwireState c idx P k l s outGate).edge a b
      = (maskCircuit c (blockMask c P k l)).edge a b := rfl

/-- Hardwiring the boundary layer never turns a computation gate into a literal or vice
versa: a hardwired layer-`k` computation gate becomes an `and`/`or` gate, and every other
gate keeps its kind. -/
theorem hardwireState_isComputation {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    (g : Fin c.gateCount) :
    ((hardwireState c idx P k l s outGate).kind g).isComputation
      = (c.kind g).isComputation := by
  change (if (c.kind g).isComputation = true ∧ c.layer g = k then
      (if s (idx.slot g) then ADRGate.andGate else ADRGate.orGate)
      else c.kind g).isComputation = _
  split
  · rename_i h
    cases hs : s (idx.slot g) <;> simpa [ADRGate.isComputation] using h.1.symm
  · rfl

/-- Computation width (the notion consumed by `PlanarBridgeStatement`) is preserved by
`hardwireState`: layers and gate kinds' computation status are both unchanged. -/
theorem adrHasWidthAtMost_hardwireState {c : ADRCircuit n}
    (idx : LayerIndexing c w) (P : Finset Nat) (k l : Nat) (s : State w)
    (outGate : Fin c.gateCount) {wc : Nat} (hw : ADRHasWidthAtMost c wc) :
    ADRHasWidthAtMost (hardwireState c idx P k l s outGate) wc := by
  classical
  intro ell
  refine le_trans (le_of_eq ?_) (hw ell)
  refine card_filter_congr_of_iff _ _ _ _ ?_
  intro g
  rw [hardwireState_layer, hardwireState_isComputation]

/-- The block mask only keeps edges whose two endpoints lie on layers outside `P`, so the
masked block is a subgraph of the planarized circuit `deleteLayers c P`; masking never
increases the genus, so planarity transfers. -/
theorem rotationPlanar_maskCircuit_block {c : ADRCircuit n}
    (P : Finset Nat) (k l : Nat)
    (hplanar : RotationPlanar (deleteLayers c P)) :
    RotationPlanar (maskCircuit c (blockMask c P k l)) := by
  have heq : maskCircuit c (blockMask c P k l)
      = maskCircuit (deleteLayers c P) (blockMask c P k l) := by
    unfold maskCircuit deleteLayers
    congr 1
    funext a b
    by_cases h : blockMask c P k l a b = true
    · have h' := h
      simp only [blockMask, decide_eq_true_eq] at h'
      simp [h, h'.2.2.1, h'.2.2.2.1]
    · simp only [Bool.not_eq_true] at h
      simp [h]
  rw [rotationPlanar_iff_genus_zero] at hplanar ⊢
  rw [heq]
  exact Nat.le_zero.mp (le_trans (genus_maskCircuit_le _ _) (le_of_eq hplanar))

/-!
## Evaluating the hardwired boundary layer (B2b)

The mask deletes every edge into layer `k`, so the hardwired layer-`k` computation gates are
nullary; a nullary AND evaluates to `true` and a nullary OR to `false`, which is exactly the
start state `s` read through the slot indexing.
-/

/-- No edge of the hardwired block enters a layer-`k` gate. -/
theorem hardwireState_edge_into_k_false {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    (h g : Fin c.gateCount) (hg : c.layer g = k) :
    (hardwireState c idx P k l s outGate).edge h g = false := by
  have hmask : blockMask c P k l h g = false := by
    simp only [blockMask, decide_eq_false_iff_not, not_and]
    intro _ _ _ _ hne
    exact hne hg
  simp [hardwireState_edge, maskCircuit_edge, hmask]

/-- A layer-`k` computation gate of the hardwired block is the nullary gate dictated by the
start state `s`. -/
theorem hardwireState_kind_at_k {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    {g : Fin c.gateCount} (hg : c.layer g = k) (hcomp : (c.kind g).isComputation = true) :
    (hardwireState c idx P k l s outGate).kind g
      = if s (idx.slot g) then ADRGate.andGate else ADRGate.orGate := by
  change (if (c.kind g).isComputation = true ∧ c.layer g = k then
      (if s (idx.slot g) then ADRGate.andGate else ADRGate.orGate) else c.kind g) = _
  rw [if_pos ⟨hcomp, hg⟩]

/-- Any valuation of the hardwired block reads the start state at the boundary layer `k`. -/
theorem hardwireState_value_at_k {c : ADRCircuit n} (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation (hardwireState c idx P k l s outGate) x value)
    {g : Fin c.gateCount} (hg : c.layer g = k) (hcomp : (c.kind g).isComputation = true) :
    value g = s (idx.slot g) := by
  have hk := hardwireState_kind_at_k idx P k l s outGate hg hcomp
  have hg' := hval g
  cases hs : s (idx.slot g) with
  | true =>
      rw [hs, if_pos rfl] at hk
      rw [hk] at hg'
      exact hg'.mpr (fun h he => absurd he
        (by rw [hardwireState_edge_into_k_false idx P k l s outGate h g hg]; simp))
  | false =>
      rw [hs, if_neg Bool.false_ne_true] at hk
      rw [hk] at hg'
      have : ¬ (value g = true) := by
        intro hv
        obtain ⟨h, he, _⟩ := hg'.mp hv
        rw [hardwireState_edge_into_k_false idx P k l s outGate h g hg] at he
        exact Bool.noConfusion he
      simpa using this

section BlockEval

variable {c : ADRCircuit n}

/-!
## Interior evaluation of the block (B2b)

Inside a `P`-free interval `[k, l]` the hardwired block computes exactly the run of the
one-step relation of `c` started from the hardwired boundary state `s`: the mask keeps
every edge of `c` whose endpoints lie on interior layers, gate kinds are untouched away
from layer `k`, and the layer-`k` gates are pinned to `s` by `hardwireState_value_at_k`.
-/

/-- `s` carries the values of `value` on the computation gates of layer `j`. -/
def AgreeOnLayer (idx : LayerIndexing c w) (value : Fin c.gateCount → Bool)
    (j : Nat) (s : State w) : Prop :=
  ∀ g, (c.kind g).isComputation = true → c.layer g = j → s (idx.slot g) = value g

/-- Away from the hardwired layer `k`, the block keeps the gate kinds of `c`. -/
theorem hardwireState_kind_eq (idx : LayerIndexing c w) (P : Finset Nat) (k l : Nat)
    (s : State w) (outGate : Fin c.gateCount) {g : Fin c.gateCount}
    (hne : ¬ ((c.kind g).isComputation = true ∧ c.layer g = k)) :
    (hardwireState c idx P k l s outGate).kind g = c.kind g := by
  change (if (c.kind g).isComputation = true ∧ c.layer g = k then _ else c.kind g) = _
  rw [if_neg hne]

/-- On a `P`-free interval the block keeps every edge of `c` into an interior gate. -/
theorem hardwireState_edge_eq_interior (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    {j : Nat} (hk : k ≤ j) (hl : j + 1 ≤ l) (hP : ∀ i, k ≤ i → i ≤ l → i ∉ P)
    {g : Fin c.gateCount} (hg : c.layer g = j + 1) (h : Fin c.gateCount) :
    (hardwireState c idx P k l s outGate).edge h g = c.edge h g := by
  cases he : c.edge h g with
  | false => simp [hardwireState_edge, maskCircuit_edge, he]
  | true =>
      have hh : c.layer h = j := by have := hc.1 h g he; omega
      have hmask : blockMask c P k l h g = true := by
        simp only [blockMask, decide_eq_true_eq]
        refine ⟨by omega, by omega, ?_, ?_, by omega⟩
        · rw [hh]; exact hP j hk (by omega)
        · rw [hg]; exact hP (j + 1) (by omega) hl
      simp [hardwireState_edge, maskCircuit_edge, hmask, he]

/-- A predecessor's contribution read off an agreeing state is its value in the block. -/
theorem predValue_of_agree (idx : LayerIndexing c w) (P : Finset Nat) (k l : Nat)
    (s : State w) (outGate : Fin c.gateCount) {x : Fin n → Bool}
    {value : Fin c.gateCount → Bool}
    (hval : ADRValuation (hardwireState c idx P k l s outGate) x value)
    {j : Nat} {sj : State w} (hagree : AgreeOnLayer idx value j sj)
    {h : Fin c.gateCount} (hh : c.layer h = j) :
    predValue idx x sj h = value h := by
  cases hk : c.kind h with
  | literal i b =>
      have hnc : ¬ ((c.kind h).isComputation = true ∧ c.layer h = k) := by
        rw [hk]; simp [ADRGate.isComputation]
      have hkind : (hardwireState c idx P k l s outGate).kind h = ADRGate.literal i b := by
        rw [hardwireState_kind_eq idx P k l s outGate hnc, hk]
      have hgv := hval h
      rw [hkind] at hgv
      simp only [predValue, hk, hgv]
  | andGate => simpa [predValue, hk] using hagree h (by rw [hk]; rfl) hh
  | orGate => simpa [predValue, hk] using hagree h (by rw [hk]; rfl) hh

/-- The local step value of an interior gate, computed from an agreeing state, is exactly
its value in the block. -/
theorem gateStepValue_iff_value (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation (hardwireState c idx P k l s outGate) x value)
    {j : Nat} (hk : k ≤ j) (hl : j + 1 ≤ l) (hP : ∀ i, k ≤ i → i ≤ l → i ∉ P)
    {sj : State w} (hagree : AgreeOnLayer idx value j sj)
    {g : Fin c.gateCount} (hg : c.layer g = j + 1) :
    GateStepValue idx x sj g ↔ value g = true := by
  have hkind : (hardwireState c idx P k l s outGate).kind g = c.kind g :=
    hardwireState_kind_eq idx P k l s outGate (fun h => by omega)
  have hedge : ∀ h, (hardwireState c idx P k l s outGate).edge h g = c.edge h g :=
    hardwireState_edge_eq_interior hc idx P k l s outGate hk hl hP hg
  have hgv := hval g
  rw [hkind] at hgv
  have hpred : ∀ h, c.edge h g = true → predValue idx x sj h = value h := by
    intro h he
    have hh : c.layer h = j := by have := hc.1 h g he; omega
    exact predValue_of_agree idx P k l s outGate hval hagree hh
  cases hk2 : c.kind g with
  | literal i b =>
      simp only [hk2] at hgv
      simp only [GateStepValue, hk2, hgv]
  | andGate =>
      simp only [hk2] at hgv
      simp only [GateStepValue, hk2, hgv]
      constructor
      · intro h1 h he
        rw [hedge] at he
        rw [← hpred h he]
        exact h1 h he
      · intro h1 h he
        rw [hpred h he]
        exact h1 h (by rw [hedge]; exact he)
  | orGate =>
      simp only [hk2] at hgv
      simp only [GateStepValue, hk2, hgv]
      constructor
      · rintro ⟨h, he, hv⟩
        exact ⟨h, by rw [hedge]; exact he, by rw [← hpred h he]; exact hv⟩
      · rintro ⟨h, he, hv⟩
        rw [hedge] at he
        exact ⟨h, he, by rw [hpred h he]; exact hv⟩

/-- From an agreeing state the machine steps to the next layer of the block. -/
theorem oneStep_of_agree (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation (hardwireState c idx P k l s outGate) x value)
    {j : Nat} (hk : k ≤ j) (hl : j + 1 ≤ l) (hP : ∀ i, k ≤ i → i ≤ l → i ∉ P)
    {sj : State w} (hagree : AgreeOnLayer idx value j sj) :
    OneStep idx x j sj (stateOf idx value (j + 1)) := by
  constructor
  · intro g hcomp hg
    rw [stateOf_slot idx value hg hcomp]
    exact (gateStepValue_iff_value hc idx P k l s outGate hval hk hl hP hagree hg).symm
  · intro j' hj'
    unfold stateOf
    simp only [decide_eq_false_iff_not, not_exists]
    rintro g ⟨hcomp, hg, hslot, -⟩
    exact hj' ⟨g, hcomp, hg, hslot⟩

/-- Agreement with the block valuation propagates along a one-step transition. -/
theorem agree_of_oneStep (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation (hardwireState c idx P k l s outGate) x value)
    {j : Nat} (hk : k ≤ j) (hl : j + 1 ≤ l) (hP : ∀ i, k ≤ i → i ≤ l → i ∉ P)
    {sj u : State w} (hagree : AgreeOnLayer idx value j sj)
    (hstep : OneStep idx x j sj u) :
    AgreeOnLayer idx value (j + 1) u := by
  intro g hcomp hg
  exact bool_eq_of_iff ((hstep.1 g hcomp hg).trans
    (gateStepValue_iff_value hc idx P k l s outGate hval hk hl hP hagree hg))

/-- Existence half of the interior evaluation: the block valuation provides a run of the
one-step relation from the boundary state through the whole interval. -/
theorem exists_reach_of_agree (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation (hardwireState c idx P k l s outGate) x value)
    (hP : ∀ i, k ≤ i → i ≤ l → i ∉ P)
    {sk : State w} (hagree : AgreeOnLayer idx value k sk) :
    ∀ m, k + m ≤ l → ∃ t, Reach idx x k m sk t ∧ AgreeOnLayer idx value (k + m) t := by
  intro m
  induction m with
  | zero => intro _; exact ⟨sk, rfl, by simpa using hagree⟩
  | succ m ih =>
      intro hm
      obtain ⟨t, hreach, hagree_t⟩ := ih (by omega)
      refine ⟨stateOf idx value (k + m + 1), ?_, ?_⟩
      · exact (reach_add idx x m 1 k sk _).mpr
          ⟨t, hreach, reach_one idx x (k + m)
            (oneStep_of_agree hc idx P k l s outGate hval (by omega) (by omega) hP hagree_t)⟩
      · have := agree_of_oneStep hc idx P k l s outGate hval
          (j := k + m) (by omega) (by omega) hP hagree_t
          (oneStep_of_agree hc idx P k l s outGate hval (by omega) (by omega) hP hagree_t)
        simpa [Nat.add_assoc] using this

/-- Uniqueness half of the interior evaluation: any run of the one-step relation from an
agreeing boundary state stays in agreement with the block valuation. -/
theorem agree_of_reach (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (s : State w) (outGate : Fin c.gateCount)
    {x : Fin n → Bool} {value : Fin c.gateCount → Bool}
    (hval : ADRValuation (hardwireState c idx P k l s outGate) x value)
    (hP : ∀ i, k ≤ i → i ≤ l → i ∉ P)
    {sk : State w} (hagree : AgreeOnLayer idx value k sk) :
    ∀ m, k + m ≤ l → ∀ t, Reach idx x k m sk t → AgreeOnLayer idx value (k + m) t := by
  intro m
  induction m with
  | zero =>
      intro _ t hreach
      have hst : sk = t := hreach
      subst hst
      simpa using hagree
  | succ m ih =>
      intro hm t hreach
      obtain ⟨u, hu, hut⟩ := (reach_add idx x m 1 k sk t).mp hreach
      obtain ⟨v, hstep, hvt⟩ := hut
      have hvt' : v = t := hvt
      subst hvt'
      have hau := ih (by omega) u hu
      have := agree_of_oneStep hc idx P k l s outGate hval
        (j := k + m) (by omega) (by omega) hP hau hstep
      simpa [Nat.add_assoc] using this

/-- **Interior evaluation of the block.**  On a `P`-free interval `[k, l]`, the hardwired
block with output gate `outGate` on layer `l` accepts `x` exactly when the boundary state
`s` reaches, in `l - k` steps of the one-step relation of `c`, a state whose `outGate`
slot is set. -/
theorem adrAccepts_hardwireState_iff_reach (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (P : Finset Nat) (k l : Nat) (hkl : k ≤ l) (hP : ∀ i, k ≤ i → i ≤ l → i ∉ P)
    (s : State w) (outGate : Fin c.gateCount)
    (hout : c.layer outGate = l) (houtcomp : (c.kind outGate).isComputation = true)
    (x : Fin n → Bool) :
    ADRAccepts (hardwireState c idx P k l s outGate) x ↔
      ∃ t : State w, Reach idx x k (l - k) s t ∧ t (idx.slot outGate) = true := by
  have hbase : ∀ value : Fin c.gateCount → Bool,
      ADRValuation (hardwireState c idx P k l s outGate) x value →
      AgreeOnLayer idx value k s := by
    intro value hval g hcomp hg
    exact (hardwireState_value_at_k idx P k l s outGate hval hg hcomp).symm
  have hkm : k + (l - k) = l := by omega
  constructor
  · rintro ⟨value, hval, hvout⟩
    obtain ⟨t, hreach, hagree⟩ :=
      exists_reach_of_agree hc idx P k l s outGate hval hP (hbase value hval) (l - k) (by omega)
    refine ⟨t, hreach, ?_⟩
    rw [hkm] at hagree
    rw [hagree outGate houtcomp hout]
    exact hvout
  · rintro ⟨t, hreach, ht⟩
    have hc' := wellFormedADR_hardwireState hc idx P k l s outGate
    refine ⟨evalADR (hardwireState c idx P k l s outGate) hc' x,
      (adrValuation_iff_eq_evalADR hc').mpr rfl, ?_⟩
    have hval : ADRValuation (hardwireState c idx P k l s outGate) x
        (evalADR (hardwireState c idx P k l s outGate) hc' x) :=
      (adrValuation_iff_eq_evalADR hc').mpr rfl
    have hagree := agree_of_reach hc idx P k l s outGate hval hP (hbase _ hval) (l - k)
      (by omega) t hreach
    rw [hkm] at hagree
    have hfin := hagree outGate houtcomp hout
    change evalADR (hardwireState c idx P k l s outGate) hc' x outGate = true
    rw [← hfin]
    exact ht

/-- **Single-bit block relation (B2c for one output bit).**  Given the planar bridge, a
`P`-free interval `[k, l]` of a well-formed circuit whose `P`-deleted graph is planar
yields, uniformly in the interval, the boundary state and the output gate, an `ACC[M]`
circuit deciding whether the block run from `s` sets the slot of `outGate`.  The
parameters `M`, `d`, `e` are extracted from the bridge at width `wc` once, before the
interval and the boundary state are quantified. -/
theorem planarBlockBit_at {wc M d e : Nat} (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (P : Finset Nat) (hplanar : RotationPlanar (deleteLayers c P))
    (hw : ADRHasWidthAtMost c wc) (hbridge : PlanarBridgeAt wc M d e) :
      ∀ (k l : Nat), k ≤ l → (∀ i, k ≤ i → i ≤ l → i ∉ P) →
        ∀ (s : State w) (outGate : Fin c.gateCount),
          c.layer outGate = l → (c.kind outGate).isComputation = true →
          ∃ a : ACCCircuit n M, WellFormedACC a ∧ (∀ g, a.layer g ≤ d) ∧
            a.gateCount ≤ (c.gateCount + 1) ^ e ∧
            (∀ x, ACCAccepts a x ↔
              ∃ t : State w, Reach idx x k (l - k) s t ∧ t (idx.slot outGate) = true) := by
  intro k l hkl hP s outGate hout houtcomp
  obtain ⟨a, hwf, hd, hsize, hsem⟩ :=
    hbridge (hardwireState c idx P k l s outGate)
      (wellFormedADR_hardwireState hc idx P k l s outGate)
      (rotationPlanar_hardwireState idx P k l s outGate
        (rotationPlanar_maskCircuit_block P k l hplanar))
      (adrHasWidthAtMost_hardwireState idx P k l s outGate hw)
  refine ⟨a, hwf, hd, hsize, ?_⟩
  intro x
  rw [hsem x]
  exact adrAccepts_hardwireState_iff_reach hc idx P k l hkl hP s outGate hout houtcomp x

/-- `planarBlockBit_at` with the bridge parameters extracted from the bridge statement. -/
theorem planarBlockBit {wc : Nat} (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (P : Finset Nat) (hplanar : RotationPlanar (deleteLayers c P))
    (hw : ADRHasWidthAtMost c wc) (pb : PlanarBridgeStatement) :
    ∃ M d e : Nat, 2 ≤ M ∧
      ∀ (k l : Nat), k ≤ l → (∀ i, k ≤ i → i ≤ l → i ∉ P) →
        ∀ (s : State w) (outGate : Fin c.gateCount),
          c.layer outGate = l → (c.kind outGate).isComputation = true →
          ∃ a : ACCCircuit n M, WellFormedACC a ∧ (∀ g, a.layer g ≤ d) ∧
            a.gateCount ≤ (c.gateCount + 1) ^ e ∧
            (∀ x, ACCAccepts a x ↔
              ∃ t : State w, Reach idx x k (l - k) s t ∧ t (idx.slot outGate) = true) := by
  obtain ⟨M, d, e, hM, hbridge⟩ := pb wc
  exact ⟨M, d, e, hM, planarBlockBit_at (wc := wc) hc idx P hplanar hw hbridge⟩

end BlockEval

/-- A size-absorption inequality: `w` copies of a circuit of size `(S+1)^e₀` plus
constant overhead still fit inside `(S+1)^(e₀ + (2w+1))` as soon as `S ≥ 1`. -/
theorem pow_absorb (S w e₀ : Nat) (hS : 0 < S) :
    w * ((S + 1) ^ e₀ + 1) + 1 ≤ (S + 1) ^ (e₀ + (2 * w + 1)) := by
  have hp : 1 ≤ (S + 1) ^ e₀ := Nat.one_le_pow _ _ (by omega)
  have hlin : 2 * w + 1 ≤ (S + 1) ^ (2 * w + 1) := by
    have h1 : 2 * w + 1 < 2 ^ (2 * w + 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ (2 * w + 1) ≤ (S + 1) ^ (2 * w + 1) :=
      Nat.pow_le_pow_left (by omega) _
    omega
  calc w * ((S + 1) ^ e₀ + 1) + 1
      = w * (S + 1) ^ e₀ + (w + 1) := by ring
    _ ≤ w * (S + 1) ^ e₀ + (w + 1) * (S + 1) ^ e₀ :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (by omega)) _
    _ = (2 * w + 1) * (S + 1) ^ e₀ := by ring
    _ ≤ (S + 1) ^ (2 * w + 1) * (S + 1) ^ e₀ := Nat.mul_le_mul_right _ hlin
    _ = (S + 1) ^ (e₀ + (2 * w + 1)) := by rw [← pow_add, Nat.add_comm (2 * w + 1) e₀]

/-- B2c: The parameters `M, d, e` can be chosen uniformly over all state pairs `(s, t)`
and all interval boundaries `k, l`.  This is the real §8 content: from the single-bit
relation `planarBlockBit` (proved) one builds, uniformly in the interval and boundary
pair, an `ACC[M]` circuit deciding the whole planar block relation.  See the iteration-12
Aristotle blueprint for the intended construction (a width-`w` conjunction of, per slot,
either a `planarBlockBit` circuit or its negation or a constant). -/
theorem planarBlockRelation_at {wc M d₀ e₀ : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) (P : Finset Nat)
    (hplanar : RotationPlanar (deleteLayers c P))
    (hw : ADRHasWidthAtMost c wc)
    (hbridge : PlanarBridgeAt wc M d₀ e₀) :
      ∀ (k l : Nat), k ≤ l → (∀ i, k ≤ i → i ≤ l → i ∉ P) →
      ∀ (s t : State w),
        ∃ a : ACCCircuit n M, WellFormedACC a ∧ (∀ g, a.layer g ≤ d₀ + 2) ∧
          a.gateCount ≤ (c.gateCount + 1) ^ (e₀ + (2 * w + 1)) ∧
          (∀ x, ACCAccepts a x ↔ Reach idx x k (l - k) s t) := by
  classical
  have Hbit := planarBlockBit_at (wc := wc) hc idx P hplanar hw hbridge
  intro k l hkl hP s t
  have hS : 0 < c.gateCount := lt_of_le_of_lt (Nat.zero_le _) c.output.isLt
  by_cases hlk : l = k
  · subst hlk
    refine ⟨accConst n M (decide (s = t)), wellFormedACC_accConst n M _, ?_, ?_, ?_⟩
    · intro g; rw [accConst_layer]; omega
    · rw [accConst_gateCount]; exact Nat.one_le_pow _ _ (by omega)
    · intro x
      rw [accAccepts_accConst, Nat.sub_self]
      simp
  · have hm : 1 ≤ l - k := by omega
    have key : ∀ j : Fin w, ∃ b : ACCCircuit n M, WellFormedACC b ∧
        (∀ g, b.layer g ≤ d₀ + 1) ∧ b.gateCount ≤ (c.gateCount + 1) ^ e₀ + 1 ∧
        (∀ x, ACCAccepts b x ↔
          (t j = true ↔ ∃ t', Reach idx x k (l - k) s t' ∧ t' j = true)) := by
      intro j
      by_cases hocc : ∃ g : Fin c.gateCount,
          (c.kind g).isComputation = true ∧ c.layer g = l ∧ idx.slot g = j
      · obtain ⟨g, hcomp, hlay, hslot⟩ := hocc
        obtain ⟨a, hwf, hd, hsize, hsem⟩ := Hbit k l hkl hP s g hlay hcomp
        subst hslot
        cases htj : t (idx.slot g) with
        | true =>
            exact ⟨a, hwf, fun g' => le_trans (hd g') (Nat.le_succ _),
              le_trans hsize (Nat.le_succ _), fun x => by rw [hsem x]; simp⟩
        | false =>
            refine ⟨accNot a d₀, wellFormedACC_accNot hwf hd, accNot_layer_le hd, ?_, ?_⟩
            · rw [accNot_gateCount]; omega
            · intro x
              rw [accAccepts_accNot hwf hd x, hsem x]
              simp
      · refine ⟨accConst n M (!(t j)), wellFormedACC_accConst n M _, ?_, ?_, ?_⟩
        · intro g; rw [accConst_layer]; omega
        · rw [accConst_gateCount]
          have := Nat.one_le_pow e₀ (c.gateCount + 1) (by omega)
          omega
        · intro x
          have hno : ¬ ∃ t', Reach idx x k (l - k) s t' ∧ t' j = true := by
            rintro ⟨t', hr, ht'⟩
            have hfalse := reach_padded idx x hm hr j (by
              rintro ⟨g, hcomp, hg, hs⟩
              exact hocc ⟨g, hcomp, by omega, hs⟩)
            rw [hfalse] at ht'
            exact Bool.false_ne_true ht'
          rw [accAccepts_accConst]
          cases htj : t j with
          | true => simp [hno]
          | false => simp [hno]
    choose blk hblkwf hblkd hblksize hblksem using key
    have hlayers : ∀ (i : Fin w) (b : Fin (blk i).gateCount), (blk i).layer b ≤ d₀ + 1 :=
      fun i b => hblkd i b
    refine ⟨accJoin blk (d₀ + 1) .andGate,
      wellFormedACC_accJoin hblkwf hlayers (by intro i b; simp) (by simp),
      accJoin_layer_le hlayers, ?_, ?_⟩
    · have hsum : (∑ j : Fin w, (blk j).gateCount) ≤ w * ((c.gateCount + 1) ^ e₀ + 1) := by
        have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin w))
          (fun j => (blk j).gateCount) ((c.gateCount + 1) ^ e₀ + 1) (fun j _ => hblksize j)
        simpa [Finset.card_univ, smul_eq_mul] using h
      calc (accJoin blk (d₀ + 1) (ACCGate.andGate : ACCGate n M)).gateCount
          = (∑ j : Fin w, (blk j).gateCount) + 1 := rfl
        _ ≤ w * ((c.gateCount + 1) ^ e₀ + 1) + 1 := by omega
        _ ≤ (c.gateCount + 1) ^ (e₀ + (2 * w + 1)) := pow_absorb c.gateCount w e₀ hS
    · intro x
      rw [accAccepts_accJoin_and hblkwf hlayers x, reach_iff_bits idx x k (l - k) s t]
      exact forall_congr' fun j => hblksem j x

/-- `planarBlockRelation_at` with the bridge parameters extracted from the bridge
statement. -/
theorem planarBlockRelation {wc : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) (P : Finset Nat)
    (hplanar : RotationPlanar (deleteLayers c P))
    (hw : ADRHasWidthAtMost c wc)
    (pb : PlanarBridgeStatement) :
    ∃ (M d e : Nat), 2 ≤ M ∧
      ∀ (k l : Nat), k ≤ l → (∀ i, k ≤ i → i ≤ l → i ∉ P) →
      ∀ (s t : State w),
        ∃ a : ACCCircuit n M, WellFormedACC a ∧ (∀ g, a.layer g ≤ d) ∧
          a.gateCount ≤ (c.gateCount + 1) ^ e ∧
          (∀ x, ACCAccepts a x ↔ Reach idx x k (l - k) s t) := by
  obtain ⟨M, d₀, e₀, hM, hbridge⟩ := pb wc
  exact ⟨M, d₀ + 2, e₀ + (2 * w + 1), hM,
    planarBlockRelation_at (wc := wc) hc idx P hplanar hw hbridge⟩

/-- B2b: For a fixed boundary pair `(s, t)`, the block relation can be decided by an ACC circuit
using the planar bridge.  This is the specialization of the uniform relation
`planarBlockRelation` (B2c) to a single interval and boundary pair, so it carries no
independent proof obligation. -/
theorem exists_acc_planarBlock {wc : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (idx : LayerIndexing c w) (P : Finset Nat)
    (hplanar : RotationPlanar (deleteLayers c P))
    (hw : ADRHasWidthAtMost c wc)
    (k l : Nat) (hkl : k ≤ l) (hP : ∀ i, k ≤ i → i ≤ l → i ∉ P)
    (s t : State w)
    (pb : PlanarBridgeStatement) :
    ∃ (M d e : Nat) (a : ACCCircuit n M), 2 ≤ M ∧
      WellFormedACC a ∧ (∀ g, a.layer g ≤ d) ∧
      a.gateCount ≤ (c.gateCount + 1) ^ e ∧
      (∀ x, ACCAccepts a x ↔ Reach idx x k (l - k) s t) := by
  obtain ⟨M, d, e, hM, H⟩ := planarBlockRelation hc idx P hplanar hw pb
  obtain ⟨a, hwf, hd, hsize, hsem⟩ := H k l hkl hP s t
  exact ⟨M, d, e, a, hM, hwf, hd, hsize, hsem⟩

end AllenderOQ3.Internal
