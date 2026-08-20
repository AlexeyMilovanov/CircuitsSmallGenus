import AllenderOQ3.Internal.StateChain
import AllenderOQ3.Internal.LayerPlanarizer

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat}

/-!
# Half-open cut decomposition (§6)

The decomposition of a chain of relations by cutting at the deleted layers `P`.
-/

/-- The layers adjacent to the deleted layers form the cut set X. -/
def cutSet (P : Finset Nat) : Finset Nat :=
  P.biUnion (fun i => {i, i + 1})

/-- Membership in the cut set: `cutSet P = P ∪ (P + 1)`. -/
theorem mem_cutSet {P : Finset Nat} {i : Nat} :
    i ∈ cutSet P ↔ ∃ j ∈ P, i = j ∨ i = j + 1 := by
  simp only [cutSet, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]

/-- The size of the cut set is at most twice the size of P. -/
theorem card_cutSet_le (P : Finset Nat) : (cutSet P).card ≤ 2 * P.card := by
  unfold cutSet
  calc
    (P.biUnion fun i => {i, i + 1}).card ≤
        ∑ i ∈ P, ({i, i + 1} : Finset Nat).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ P, 2 := by
      exact Finset.sum_le_sum fun i _hi => by
        simp
    _ = 2 * P.card := by
      simp [Nat.mul_comm]

/-- A cut sequence decomposes the interval `[i, j]` into one-step relations at indices `∈ X`
and maximal gap relations `[k, l]` avoiding `X`. -/
inductive CutSequence (X : Finset Nat) : Nat → Nat → Type
  | empty (i : Nat) : CutSequence X i i
  | step {i j : Nat} (hX : i ∈ X) (rest : CutSequence X (i + 1) j) : CutSequence X i j
  | gap {i k j : Nat} (h_lt : i < k) (h_not : ∀ l, i < l → l < k → l ∉ X)
      (rest : CutSequence X k j) : CutSequence X i j

/-- The composition of a cut sequence with intermediate states. -/
inductive ComposeChain {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
  {X : Finset Nat} :
    ∀ {i j : Nat}, CutSequence X i j → State w → State w → Prop
  | empty {i : Nat} (s : State w) :
      ComposeChain idx x (CutSequence.empty i) s s
  | step {i j : Nat} {hX : i ∈ X} {rest : CutSequence X (i + 1) j} {s u t : State w}
      (h_step : OneStep idx x i s u)
      (h_rest : ComposeChain idx x rest u t) :
      ComposeChain idx x (CutSequence.step hX rest) s t
  | gap {i k j : Nat} {h_lt : i < k} {h_not : ∀ l, i < l → l < k → l ∉ X} {rest : CutSequence X k j}
      {s u t : State w}
      (h_gap : Reach idx x i (k - i) s u)
      (h_rest : ComposeChain idx x rest u t) :
      ComposeChain idx x (CutSequence.gap h_lt h_not rest) s t

/-- A cut sequence only runs forward: its start index is at most its end index. -/
theorem cutSequence_le {X : Finset Nat} {i j : Nat} (seq : CutSequence X i j) : i ≤ j := by
  induction seq with
  | empty i => omega
  | step hX rest ih => omega
  | gap h_lt h_not rest ih => omega

/-- Every composition along a cut sequence is a run of the block relation. -/
theorem reach_of_composeChain {c : ADRCircuit n} {idx : LayerIndexing c w} {x : Fin n → Bool}
    {X : Finset Nat} {i j : Nat} {seq : CutSequence X i j} {s t : State w}
    (h : ComposeChain idx x seq s t) : Reach idx x i (j - i) s t := by
  induction h with
  | empty s => simp
  | @step i j hX rest s u t h_step _ ih =>
      have hle : i + 1 ≤ j := cutSequence_le rest
      have hj : j - i = (j - (i + 1)) + 1 := by omega
      rw [hj]
      exact ⟨u, h_step, ih⟩
  | @gap i k j h_lt h_not rest s u t h_gap _ ih =>
      have hkj : k ≤ j := cutSequence_le rest
      have hj : j - i = (k - i) + (j - k) := by omega
      rw [hj]
      refine (reach_add idx x (k - i) (j - k) i s t).mpr ⟨u, h_gap, ?_⟩
      have hik : i + (k - i) = k := by omega
      rw [hik]
      exact ih

/-- Every run of the block relation decomposes along any cut sequence. -/
theorem composeChain_of_reach {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    {X : Finset Nat} {i j : Nat} (seq : CutSequence X i j) :
    ∀ s t : State w, Reach idx x i (j - i) s t → ComposeChain idx x seq s t := by
  induction seq with
  | empty i =>
      intro s t h
      rw [Nat.sub_self] at h
      cases h
      exact ComposeChain.empty s
  | @step i j hX rest ih =>
      intro s t h
      have hle : i + 1 ≤ j := cutSequence_le rest
      have hj : j - i = (j - (i + 1)) + 1 := by omega
      rw [hj] at h
      obtain ⟨u, h_step, h_rest⟩ := h
      exact ComposeChain.step h_step (ih u t h_rest)
  | @gap i k j h_lt h_not rest ih =>
      intro s t h
      have hkj : k ≤ j := cutSequence_le rest
      have hj : j - i = (k - i) + (j - k) := by omega
      rw [hj] at h
      obtain ⟨u, h1, h2⟩ := (reach_add idx x (k - i) (j - k) i s t).mp h
      have hik : i + (k - i) = k := by omega
      rw [hik] at h2
      exact ComposeChain.gap h1 (ih u t h2)

/-- ComposeChain is equivalent to Reach. -/
theorem composeChain_iff_reach {c : ADRCircuit n} (idx : LayerIndexing c w) (x : Fin n → Bool)
    (X : Finset Nat) (i j : Nat) (seq : CutSequence X i j) (s t : State w) :
    ComposeChain idx x seq s t ↔ Reach idx x i (j - i) s t :=
  ⟨reach_of_composeChain, composeChain_of_reach idx x seq s t⟩

/-- A sequence of cuts can always be formed: repeatedly take a length-one gap. -/
theorem exists_cutSequence (X : Finset Nat) (i j : Nat) (hle : i ≤ j) :
    Nonempty (CutSequence X i j) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hle
  clear hle
  induction d generalizing i with
  | zero => exact ⟨CutSequence.empty i⟩
  | succ d ih =>
      obtain ⟨rest⟩ := ih (i + 1)
      have heq : i + 1 + d = i + (d + 1) := by omega
      rw [heq] at rest
      exact ⟨CutSequence.gap (Nat.lt_succ_self i)
        (fun l hl1 hl2 => absurd hl2 (by omega)) rest⟩

/-! ## Counting the relations of a cut sequence (B1c) -/

/-- The number of relations (one-step or gap) composing a cut sequence. -/
def numRel {X : Finset Nat} : {i j : Nat} → CutSequence X i j → Nat
  | _, _, .empty _ => 0
  | _, _, .step _ rest => numRel rest + 1
  | _, _, .gap _ _ rest => numRel rest + 1

/-- The number of cut points of `X` inside the half-open interval `[i, j)`. -/
def cutCount (X : Finset Nat) (i j : Nat) : Nat :=
  (X.filter (fun p => i ≤ p ∧ p < j)).card

/-- Removing a cut point at the left endpoint decreases the cut count by one. -/
theorem cutCount_succ_of_mem {X : Finset Nat} {i j : Nat} (hi : i ∈ X) (hij : i < j) :
    cutCount X i j = cutCount X (i + 1) j + 1 := by
  classical
  have hset : X.filter (fun p => i ≤ p ∧ p < j)
      = insert i (X.filter (fun p => i + 1 ≤ p ∧ p < j)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hp, h1, h2⟩
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨hp, h, h2⟩
    · rintro (rfl | ⟨hp, h1, h2⟩)
      · exact ⟨hi, le_refl _, hij⟩
      · exact ⟨hp, by omega, h2⟩
  have hnot : i ∉ X.filter (fun p => i + 1 ≤ p ∧ p < j) := by
    intro hmem
    have := (Finset.mem_filter.mp hmem).2.1
    omega
  unfold cutCount
  rw [hset, Finset.card_insert_of_notMem hnot]

/-- Shrinking the interval past a region free of cut points does not change the cut count. -/
theorem cutCount_eq_of_gap {X : Finset Nat} {i m j : Nat} (him : i ≤ m)
    (h : ∀ l, i ≤ l → l < m → l ∉ X) : cutCount X i j = cutCount X m j := by
  classical
  unfold cutCount
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, h1, h2⟩
    refine ⟨hp, ?_, h2⟩
    by_contra hc
    exact h p h1 (by omega) hp
  · rintro ⟨hp, h1, h2⟩
    exact ⟨hp, by omega, h2⟩

/-- There is a cut sequence on `[i, j]` using at most `2 * |X ∩ [i, j)| + 1` relations:
gaps are taken maximally, so each one-step relation is charged to a distinct cut point. -/
theorem exists_cutSequence_le (X : Finset Nat) (i j : Nat) (hle : i ≤ j) :
    ∃ seq : CutSequence X i j, numRel seq ≤ 2 * cutCount X i j + 1 := by
  classical
  suffices h : ∀ d i j, j - i = d → i ≤ j →
      ∃ seq : CutSequence X i j, numRel seq ≤ 2 * cutCount X i j + 1 from h (j - i) i j rfl hle
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hd hij
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact ⟨CutSequence.empty i, by simp [numRel]⟩
    by_cases hiX : i ∈ X
    · obtain ⟨rest, hrest⟩ := ih (j - (i + 1)) (by omega) (i + 1) j rfl (by omega)
      refine ⟨CutSequence.step hiX rest, ?_⟩
      have hc := cutCount_succ_of_mem hiX hlt
      have hnum : numRel (CutSequence.step hiX rest) = numRel rest + 1 := rfl
      omega
    · by_cases hSne : (X.filter (fun p => i < p ∧ p < j)).Nonempty
      · set S := X.filter (fun p => i < p ∧ p < j) with hS
        have hmS : S.min' hSne ∈ S := S.min'_mem hSne
        obtain ⟨hmX, hmi, hmj⟩ := Finset.mem_filter.mp hmS
        set m := S.min' hSne with hm
        have hmin : ∀ l, i < l → l < m → l ∉ X := by
          intro l h1 h2 hlX
          have hlS : l ∈ S := Finset.mem_filter.mpr ⟨hlX, h1, by omega⟩
          have := S.min'_le l hlS
          omega
        obtain ⟨rest, hrest⟩ := ih (j - (m + 1)) (by omega) (m + 1) j rfl (by omega)
        refine ⟨CutSequence.gap hmi hmin (CutSequence.step hmX rest), ?_⟩
        have h1 : cutCount X i j = cutCount X m j := by
          refine cutCount_eq_of_gap (le_of_lt hmi) ?_
          intro l hl1 hl2 hlX
          rcases Nat.eq_or_lt_of_le hl1 with rfl | h
          · exact hiX hlX
          · exact hmin l h hl2 hlX
        have h2 := cutCount_succ_of_mem hmX hmj
        have hnum : numRel (CutSequence.gap hmi hmin (CutSequence.step hmX rest))
            = numRel rest + 2 := rfl
        omega
      · refine ⟨CutSequence.gap hlt
          (fun l h1 h2 hlX => hSne ⟨l, Finset.mem_filter.mpr ⟨hlX, h1, h2⟩⟩)
          (CutSequence.empty j), ?_⟩
        have hnum : numRel (CutSequence.gap hlt
            (fun l h1 h2 hlX => hSne ⟨l, Finset.mem_filter.mpr ⟨hlX, h1, h2⟩⟩)
            (CutSequence.empty j)) = 1 := rfl
        omega

/-- With the canonical cut set `cutSet P`, the cut sequence uses `O(|P|)` relations. -/
theorem exists_cutSequence_cutSet_le (P : Finset Nat) (i j : Nat) (hle : i ≤ j) :
    ∃ seq : CutSequence (cutSet P) i j, numRel seq ≤ 4 * P.card + 1 := by
  classical
  obtain ⟨seq, hseq⟩ := exists_cutSequence_le (cutSet P) i j hle
  refine ⟨seq, hseq.trans ?_⟩
  have h1 : cutCount (cutSet P) i j ≤ (cutSet P).card := Finset.card_filter_le _ _
  have h2 := card_cutSet_le P
  omega

end AllenderOQ3.Internal
