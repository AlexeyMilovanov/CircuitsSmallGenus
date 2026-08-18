import AllenderOQ3.Internal.Blocking
import AllenderOQ3.Incidence
/-!
# Locality of the block relations (§9)

The blocking lemma of `AllenderOQ3.Internal.Blocking` writes acceptance as an
unbounded fan-in `OR` of an unbounded fan-in `AND` of block relations
`Reach idx x (B * j) B s t`.  For that shape to be realised by a *small* ACC
circuit, each block relation must depend on only a bounded number of input bits.

This file proves exactly that:

* `gateStepValue_congr`, `oneStep_congr` — the local transition relation only
  reads the inputs through the literal gates of the layer it produces;
* `reach_congr` — hence a block of `k` steps starting at layer `i` only reads the
  inputs occurring as literals on layers `i + 1, …, i + k`;
* `relevantInputs` — those input positions, as a `Finset`;
* `reach_congr_relevantInputs` — the block relation is determined by the
  restriction of the input to `relevantInputs`;
* `card_layerGates_le` and `card_relevantInputs_le` — in a circuit of width `w`
  there are at most `w` gates per layer, so a block of length `k` reads at most
  `k * w` input positions.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat}

/-! ## The transition relation only reads the literals of the layer it produces -/

theorem predValue_congr {c : ADRCircuit n} (idx : LayerIndexing c w)
    {x y : Fin n → Bool} {s : State w} {h : Fin c.gateCount}
    (hx : ∀ (j : Fin n) (b : Bool), c.kind h = .literal j b → x j = y j) :
    predValue idx x s h = predValue idx y s h := by
  unfold predValue
  cases hk : c.kind h with
  | literal j b => simp only; rw [hx j b hk]
  | andGate => rfl
  | orGate => rfl

theorem gateStepValue_congr {c : ADRCircuit n} (idx : LayerIndexing c w)
    {x y : Fin n → Bool} {s : State w} {g : Fin c.gateCount}
    (h_self : ∀ (j : Fin n) (b : Bool), c.kind g = .literal j b → x j = y j)
    (h_pred : ∀ h, c.edge h g = true → ∀ (j : Fin n) (b : Bool), c.kind h = .literal j b → x j = y j) :
    GateStepValue idx x s g ↔ GateStepValue idx y s g := by
  unfold GateStepValue
  cases hk : c.kind g with
  | literal j b => dsimp only; rw [h_self j b hk]
  | andGate =>
      refine forall_congr' fun h => ?_
      refine imp_congr_right fun he => ?_
      rw [predValue_congr idx (h_pred h he)]
  | orGate =>
      refine exists_congr fun h => ?_
      refine and_congr_right fun he => ?_
      rw [predValue_congr idx (h_pred h he)]

theorem oneStep_congr {c : ADRCircuit n} (hc : WellFormedADR c) (idx : LayerIndexing c w)
    {x y : Fin n → Bool} {i : Nat} {s t : State w}
    (h : ∀ g, i ≤ c.layer g → c.layer g ≤ i + 1 → ∀ (j : Fin n) (b : Bool),
      c.kind g = .literal j b → x j = y j) :
    OneStep idx x i s t ↔ OneStep idx y i s t := by
  unfold OneStep
  refine and_congr (forall_congr' fun g => ?_) Iff.rfl
  refine imp_congr_right fun hcomp => ?_
  refine forall_congr' fun hg => ?_
  refine iff_congr Iff.rfl (gateStepValue_congr idx ?_ ?_)
  · intro j b hk
    exact h g (by omega) (by omega) j b hk
  · intro h_pred he j b hk
    have hl := hc.1 h_pred g he
    exact h h_pred (by omega) (by omega) j b hk

/-- **Locality of a block.**  A run of `k` steps starting at layer `i` reads the
input only through the literal gates on layers `i, …, i + k`. -/
theorem reach_congr {c : ADRCircuit n} (hc : WellFormedADR c) (idx : LayerIndexing c w) {x y : Fin n → Bool} :
    ∀ (k i : Nat) (s t : State w),
      (∀ g, i ≤ c.layer g → c.layer g ≤ i + k → ∀ (j : Fin n) (b : Bool),
        c.kind g = .literal j b → x j = y j) →
      (Reach idx x i k s t ↔ Reach idx y i k s t) := by
  intro k
  induction k with
  | zero => intro i s t _; simp
  | succ k ih =>
      intro i s t h
      simp only [reach_succ]
      refine exists_congr fun u => and_congr ?_ ?_
      · refine oneStep_congr hc idx ?_
        intro g h1 h2 j b hk
        exact h g (by omega) (by omega) j b hk
      · refine ih (i + 1) u t ?_
        intro g h1 h2 j b hk
        exact h g (by omega) (by omega) j b hk

/-! ## The relevant input positions -/

open Classical in
/-- The input positions a block of length `k` starting at layer `i` can read:
the indices of the literal gates on layers `i, …, i + k`. -/
noncomputable def relevantInputs (c : ADRCircuit n) (i k : Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∃ (g : Fin c.gateCount) (b : Bool),
    i ≤ c.layer g ∧ c.layer g ≤ i + k ∧ c.kind g = .literal j b)

theorem mem_relevantInputs {c : ADRCircuit n} {i k : Nat} {j : Fin n} :
    j ∈ relevantInputs c i k ↔ ∃ (g : Fin c.gateCount) (b : Bool),
      i ≤ c.layer g ∧ c.layer g ≤ i + k ∧ c.kind g = .literal j b := by
  classical
  simp [relevantInputs]

/-- The block relation only depends on the input through `relevantInputs`. -/
theorem reach_congr_relevantInputs {c : ADRCircuit n} (hc : WellFormedADR c) (idx : LayerIndexing c w)
    {x y : Fin n → Bool} (k i : Nat) (s t : State w)
    (h : ∀ j ∈ relevantInputs c i k, x j = y j) :
    Reach idx x i k s t ↔ Reach idx y i k s t := by
  refine reach_congr hc idx k i s t ?_
  intro g h1 h2 j b hk
  exact h j (mem_relevantInputs.mpr ⟨g, b, h1, h2, hk⟩)

/-! ## Counting the relevant input positions -/

open Classical in
/-- The gates on a given layer. -/
noncomputable def layerGates (c : ADRCircuit n) (l : Nat) : Finset (Fin c.gateCount) :=
  Finset.univ.filter (fun g => c.layer g = l)

theorem mem_layerGates {c : ADRCircuit n} {l : Nat} {g : Fin c.gateCount} :
    g ∈ layerGates c l ↔ c.layer g = l := by
  classical
  simp [layerGates]

/-- A circuit with total width `w` has at most `w` gates per layer. -/
theorem card_layerGates_le {c : ADRCircuit n} {w : Nat} (hw : TotalWidthAtMost c w) (l : Nat) :
    (layerGates c l).card ≤ w := by
  classical
  exact hw l

/-- The gates that a block of length `k` starting at layer `i` produces. -/
noncomputable def blockGates (c : ADRCircuit n) (i k : Nat) : Finset (Fin c.gateCount) :=
  (Finset.Ico i (i + k + 1)).biUnion (fun l => layerGates c l)

theorem mem_blockGates {c : ADRCircuit n} {i k : Nat} {g : Fin c.gateCount} :
    g ∈ blockGates c i k ↔ i ≤ c.layer g ∧ c.layer g ≤ i + k := by
  classical
  simp only [blockGates, Finset.mem_biUnion, Finset.mem_Ico, mem_layerGates]
  constructor
  · rintro ⟨l, ⟨h1, h2⟩, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨c.layer g, ⟨by omega, by omega⟩, rfl⟩

theorem card_blockGates_le {c : ADRCircuit n} {w : Nat} (hw : TotalWidthAtMost c w) (i k : Nat) :
    (blockGates c i k).card ≤ (k + 1) * w := by
  classical
  rw [blockGates]
  have h := Finset.card_biUnion_le (s := Finset.Ico i (i + k + 1))
    (t := fun l => layerGates c l)
  have h2 : (Finset.Ico i (i + k + 1)).card = k + 1 := by
    rw [Nat.card_Ico]
    omega
  calc
    ((Finset.Ico i (i + k + 1)).biUnion fun l => layerGates c l).card
      ≤ ∑ l ∈ Finset.Ico i (i + k + 1), (layerGates c l).card := h
    _ ≤ ∑ l ∈ Finset.Ico i (i + k + 1), w := Finset.sum_le_sum (fun l _ => card_layerGates_le hw l)
    _ = (Finset.Ico i (i + k + 1)).card * w := by simp
    _ = (k + 1) * w := by rw [h2]

/-- **A block reads boundedly many inputs.**  In a circuit with total width `w`, 
a block of length `k` reads at most `(k + 1) * w` input positions. -/
theorem card_relevantInputs_le {c : ADRCircuit n} {w : Nat} (hw : TotalWidthAtMost c w) (i k : Nat) :
    (relevantInputs c i k).card ≤ (k + 1) * w := by
  classical
  refine le_trans ?_ (card_blockGates_le hw i k)
  rcases Finset.eq_empty_or_nonempty (relevantInputs c i k) with hE | ⟨j0, hj0⟩
  · simp [hE]
  · obtain ⟨g0, -, -, -, -⟩ := mem_relevantInputs.mp hj0
    set F : Fin n → Fin c.gateCount := fun j =>
      if h : ∃ (g : Fin c.gateCount) (b : Bool),
          i ≤ c.layer g ∧ c.layer g ≤ i + k ∧ c.kind g = .literal j b
        then h.choose else g0 with hF
    refine Finset.card_le_card_of_injOn F ?_ ?_
    · intro j hj
      have hex := mem_relevantInputs.mp hj
      have hspec := hex.choose_spec
      have hFj : F j = hex.choose := by rw [hF]; simp only [dif_pos hex]
      obtain ⟨b, hb1, hb2, -⟩ := hspec
      rw [hFj]
      exact mem_blockGates.mpr ⟨hb1, hb2⟩
    · intro j₁ h₁ j₂ h₂ heq
      have hex₁ := mem_relevantInputs.mp h₁
      have hex₂ := mem_relevantInputs.mp h₂
      have hF₁ : F j₁ = hex₁.choose := by rw [hF]; simp only [dif_pos hex₁]
      have hF₂ : F j₂ = hex₂.choose := by rw [hF]; simp only [dif_pos hex₂]
      obtain ⟨b₁, -, -, hk₁⟩ := hex₁.choose_spec
      obtain ⟨b₂, -, -, hk₂⟩ := hex₂.choose_spec
      rw [hF₁, hF₂] at heq
      rw [heq] at hk₁
      rw [hk₁] at hk₂
      exact (ADRGate.literal.inj hk₂).1

end AllenderOQ3.Internal
