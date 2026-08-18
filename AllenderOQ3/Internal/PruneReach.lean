import AllenderOQ3.Internal.Prune

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# Reachability inside the pruned circuit

`Prune.edgeReach_output_of_pruned` records that every gate retained by ancestor pruning
reaches the output *in the original circuit*.  The §7.2 core extraction
(`CoreExtract.exists_core_width_lt`) needs the same statement *inside* the pruned circuit,
which is what this file supplies: a directed path to the output only passes through gates
that reach the output, so it is entirely contained in the ancestor cone and lifts to
`prunedCircuit c`.
-/

variable {n : Nat}

/-- A directed path to the output lifts to the pruned circuit. -/
theorem edgeReach_prunedCircuit_of_edgeReach (c : ADRCircuit n) {u : Fin c.gateCount}
    (h : EdgeReach c u c.output) :
    ∀ a : Fin (prunedCircuit c).gateCount, (ancestorEmbedding c).toFun a = u →
      EdgeReach (prunedCircuit c) a (prunedCircuit c).output := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro a ha
      have hout : (ancestorEmbedding c).toFun (ancestorOutput c) = c.output :=
        ancestorEmbedding_ancestorOutput c
      have : a = ancestorOutput c := (ancestorEmbedding c).inj (ha.trans hout.symm)
      rw [this]
      exact edgeReach_refl _ _
  | @head p q hedge hrest ih =>
      intro a ha
      have hz : q ∈ ancestorSet c := (mem_ancestorSet c q).mpr hrest
      have hb : (ancestorEmbedding c).toFun ((ancestorSet c).equivFin ⟨q, hz⟩) = q := by
        simp [ancestorEmbedding, subEmbeddingOfFinset]
      refine Relation.ReflTransGen.head (b := (ancestorSet c).equivFin ⟨q, hz⟩) ?_ ?_
      · change c.edge ((ancestorEmbedding c).toFun a)
          ((ancestorEmbedding c).toFun ((ancestorSet c).equivFin ⟨q, hz⟩)) = true
        rw [ha, hb]
        exact hedge
      · exact ih _ (by simp [ancestorEmbedding, subEmbeddingOfFinset])

/-- Every gate of the pruned circuit reaches its output. -/
theorem edgeReach_output_prunedCircuit (c : ADRCircuit n)
    (a : Fin (prunedCircuit c).gateCount) :
    EdgeReach (prunedCircuit c) a (prunedCircuit c).output :=
  edgeReach_prunedCircuit_of_edgeReach c (edgeReach_output_of_pruned c a) a rfl

end AllenderOQ3.Internal
