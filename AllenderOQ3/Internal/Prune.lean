import AllenderOQ3.Internal.LayerPath
import AllenderOQ3.Internal.Subcircuit

/-!
# Ancestor pruning

Every gate that cannot reach the output gate along directed edges is irrelevant
for acceptance.  This file builds the predecessor-closed subcircuit spanned by
the *ancestor cone* of the output and shows that pruning to it preserves
acceptance and does not increase either the total width or the computation
width.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

open Classical in
/-- Any predecessor-closed finite set of gates induces a `SubEmbedding`. -/
noncomputable def subEmbeddingOfFinset {n : Nat} {c : ADRCircuit n}
    (S : Finset (Fin c.gateCount))
    (hS : ∀ v ∈ S, ∀ u, c.edge u v = true → u ∈ S) : SubEmbedding c S.card where
  toFun := fun a => (S.equivFin.symm a : Fin c.gateCount)
  inj := fun a b h => by
    have : S.equivFin.symm a = S.equivFin.symm b := Subtype.ext h
    exact S.equivFin.symm.injective this
  predClosed := fun a u hu =>
    ⟨S.equivFin ⟨u, hS _ (S.equivFin.symm a).2 u hu⟩, by simp⟩

@[simp] theorem subEmbeddingOfFinset_apply_mem {n : Nat} {c : ADRCircuit n}
    (S : Finset (Fin c.gateCount))
    (hS : ∀ v ∈ S, ∀ u, c.edge u v = true → u ∈ S) (a : Fin S.card) :
    (subEmbeddingOfFinset S hS).toFun a ∈ S :=
  (S.equivFin.symm a).2

/-- Restriction does not increase the computation width either. -/
theorem width_restrict {n : Nat} {c : ADRCircuit n} {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) {w : Nat}
    (hw : ADRHasWidthAtMost c w) :
    ADRHasWidthAtMost (restrict c f out) w := by
  intro ell
  refine le_trans ?_ (hw ell)
  refine Finset.card_le_card_of_injOn f.toFun ?_ (Function.Injective.injOn f.inj)
  intro a ha
  simpa using ha

open Classical in
/-- The set of gates from which the output gate is reachable. -/
noncomputable def ancestorSet {n : Nat} (c : ADRCircuit n) :
    Finset (Fin c.gateCount) :=
  Finset.univ.filter (fun v => EdgeReach c v c.output)

theorem mem_ancestorSet {n : Nat} (c : ADRCircuit n) (v : Fin c.gateCount) :
    v ∈ ancestorSet c ↔ EdgeReach c v c.output := by
  classical
  simp [ancestorSet]

/-- The ancestor cone of the output is closed under taking predecessors. -/
theorem ancestorSet_predClosed {n : Nat} (c : ADRCircuit n) :
    ∀ v ∈ ancestorSet c, ∀ u, c.edge u v = true → u ∈ ancestorSet c := by
  intro v hv u hu
  rw [mem_ancestorSet] at hv ⊢
  exact Relation.ReflTransGen.head hu hv

theorem output_mem_ancestorSet {n : Nat} (c : ADRCircuit n) :
    c.output ∈ ancestorSet c := by
  rw [mem_ancestorSet]
  exact edgeReach_refl c c.output

/-- The embedding of the ancestor cone of the output gate. -/
noncomputable def ancestorEmbedding {n : Nat} (c : ADRCircuit n) :
    SubEmbedding c (ancestorSet c).card :=
  subEmbeddingOfFinset (ancestorSet c) (ancestorSet_predClosed c)

/-- The index of the output gate inside the ancestor cone. -/
noncomputable def ancestorOutput {n : Nat} (c : ADRCircuit n) :
    Fin (ancestorSet c).card :=
  (ancestorSet c).equivFin ⟨c.output, output_mem_ancestorSet c⟩

theorem ancestorEmbedding_ancestorOutput {n : Nat} (c : ADRCircuit n) :
    (ancestorEmbedding c).toFun (ancestorOutput c) = c.output := by
  classical
  simp [ancestorEmbedding, ancestorOutput, subEmbeddingOfFinset]

/-- The circuit obtained by discarding every gate that cannot reach the
output. -/
noncomputable def prunedCircuit {n : Nat} (c : ADRCircuit n) : ADRCircuit n :=
  restrict c (ancestorEmbedding c) (ancestorOutput c)

theorem wellFormed_prunedCircuit {n : Nat} {c : ADRCircuit n}
    (hc : WellFormedADR c) : WellFormedADR (prunedCircuit c) :=
  wellFormed_restrict hc _ _

/-- Pruning preserves acceptance. -/
theorem adrAccepts_prunedCircuit {n : Nat} {c : ADRCircuit n}
    (hc : WellFormedADR c) (x : Fin n → Bool) :
    ADRAccepts (prunedCircuit c) x ↔ ADRAccepts c x := by
  rw [prunedCircuit, adrAccepts_restrict hc, ancestorEmbedding_ancestorOutput,
    adrAccepts_iff hc]

/-- Pruning preserves the total-width bound. -/
theorem totalWidth_prunedCircuit {n : Nat} {c : ADRCircuit n} {w : Nat}
    (hw : AllenderOQ3.TotalWidthAtMost c w) :
    AllenderOQ3.TotalWidthAtMost (prunedCircuit c) w :=
  totalWidth_restrict _ _ hw

/-- Pruning preserves the computation-width bound. -/
theorem width_prunedCircuit {n : Nat} {c : ADRCircuit n} {w : Nat}
    (hw : ADRHasWidthAtMost c w) : ADRHasWidthAtMost (prunedCircuit c) w :=
  width_restrict _ _ hw

/-- Pruning does not increase the number of gates. -/
theorem gateCount_prunedCircuit_le {n : Nat} (c : ADRCircuit n) :
    (prunedCircuit c).gateCount ≤ c.gateCount := by
  classical
  simpa [prunedCircuit, restrict, ancestorSet] using
    Finset.card_le_card (Finset.subset_univ (ancestorSet c))

/-- Every gate of the pruned circuit reaches the output of the original one. -/
theorem edgeReach_output_of_pruned {n : Nat} (c : ADRCircuit n)
    (a : Fin (prunedCircuit c).gateCount) :
    EdgeReach c ((ancestorEmbedding c).toFun a) c.output := by
  have := (ancestorSet c).equivFin.symm a |>.2
  exact (mem_ancestorSet c _).mp this

/-- In the pruned circuit no gate sits above the layer of the original output. -/
theorem layer_le_output_of_pruned {n : Nat} {c : ADRCircuit n}
    (hc : WellFormedADR c) (a : Fin (prunedCircuit c).gateCount) :
    (prunedCircuit c).layer a ≤ c.layer c.output :=
  edgeReach_layer_le hc (edgeReach_output_of_pruned c a)

/-- A circuit of total width `w` all of whose layers are at most `L` has at most
`(L + 1) * w` gates. -/
theorem gateCount_le_of_totalWidth {n : Nat} (c : ADRCircuit n) {w L : Nat}
    (hw : AllenderOQ3.TotalWidthAtMost c w) (hL : ∀ g, c.layer g ≤ L) :
    c.gateCount ≤ (L + 1) * w := by
  classical
  have hsub : (Finset.univ : Finset (Fin c.gateCount)) ⊆
      (Finset.range (L + 1)).biUnion
        (fun ell => Finset.univ.filter (fun g : Fin c.gateCount => c.layer g = ell)) := by
    intro g _
    exact Finset.mem_biUnion.mpr
      ⟨c.layer g, Finset.mem_range.mpr (Nat.lt_succ_of_le (hL g)), by simp⟩
  have hcard := Finset.card_le_card hsub
  have hbi := Finset.card_biUnion_le
    (s := Finset.range (L + 1))
    (t := fun ell => Finset.univ.filter (fun g : Fin c.gateCount => c.layer g = ell))
  have hsum : (∑ ell ∈ Finset.range (L + 1),
      (Finset.univ.filter (fun g : Fin c.gateCount => c.layer g = ell)).card)
      ≤ (L + 1) * w := by
    calc (∑ ell ∈ Finset.range (L + 1),
            (Finset.univ.filter (fun g : Fin c.gateCount => c.layer g = ell)).card)
          ≤ ∑ _ell ∈ Finset.range (L + 1), w :=
            Finset.sum_le_sum (fun ell _ => hw ell)
      _ = (L + 1) * w := by simp [Finset.sum_const, mul_comm]
  have hu : (Finset.univ : Finset (Fin c.gateCount)).card = c.gateCount := by simp
  omega

/-- Size bound for the pruned circuit in terms of the total width and the layer
of the output gate. -/
theorem gateCount_prunedCircuit_le_of_totalWidth {n : Nat} {c : ADRCircuit n}
    (hc : WellFormedADR c) {w : Nat} (hw : AllenderOQ3.TotalWidthAtMost c w) :
    (prunedCircuit c).gateCount ≤ (c.layer c.output + 1) * w :=
  gateCount_le_of_totalWidth _ (totalWidth_prunedCircuit hw)
    (layer_le_output_of_pruned hc)

end AllenderOQ3.Internal
