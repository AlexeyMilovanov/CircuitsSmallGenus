import AllenderOQ3.Internal.CorePorts
import AllenderOQ3.Internal.SetOutput
import AllenderOQ3.Internal.TotalWidth
import AllenderOQ3.Principles

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n : Nat}

/-- (B6) Ancestor of external predecessor is not in the core. -/
theorem ancestor_of_external_notMem_coreSet {c : ADRCircuit n}
    (hc : WellFormedADR c) {v o g h : Fin c.gateCount}
    (hg : g ∈ coreSet c v o) (h_edge : c.edge h g = true) (h_ext : h ∉ coreSet c v o) :
    ∀ a, EdgeReach c a h → a ∉ coreSet c v o := by
  intro a ha h_in
  have hgo := (mem_coreSet.mp hg).2.2
  have hho : EdgeReach c h o :=
    Relation.ReflTransGen.head h_edge hgo
  have H := coreSet_forward hc h_in ha hho
  rcases H with H1 | H2
  · exact h_ext H1
  · subst H2
    exact h_ext h_in

theorem width_ancestorCone_lt {c : ADRCircuit n}
    (hc : WellFormedADR c) {w : Nat}
    {v : Fin c.gateCount}
    (hv : ∀ ell : Nat,
        (Finset.univ.filter fun g : Fin c.gateCount =>
          c.layer g = ell ∧ (c.kind g).isComputation = true ∧
            g ∉ coreSet c v c.output).card + 1 ≤ w)
    {g h : Fin c.gateCount}
    (hg : g ∈ coreSet c v c.output) (h_edge : c.edge h g = true)
    (h_ext : h ∉ coreSet c v c.output) :
    ADRHasWidthAtMost (ancestorCone c h) (w - 1) := by
  intro ell
  have H_R := hv ell
  have h_w_pos : 1 ≤ w := by omega
  have h_bound : (Finset.univ.filter fun g : Fin c.gateCount =>
      c.layer g = ell ∧ (c.kind g).isComputation = true ∧
        g ∉ coreSet c v c.output).card ≤ w - 1 := by omega
  
  -- The gates of `ancestorCone c h` are embedded via `ancestorEmbedding (setOutput c h)`
  let emb := ancestorEmbedding (setOutput c h)
  -- The computation gates of `ancestorCone c h` at layer `ell` inject into `R`
  refine le_trans (Finset.card_le_card_of_injOn emb.toFun ?_ (Function.Injective.injOn emb.inj))
    h_bound
  intro a ha
  simp only [ancestorCone, prunedCircuit, restrict_layer, restrict_kind, Finset.coe_filter,
    Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
  refine ⟨by exact ha.1, by exact ha.2, ?_⟩
  have ha_reach := (mem_ancestorSet (setOutput c h) (emb.toFun a)).mp
    (subEmbeddingOfFinset_apply_mem (ancestorSet (setOutput c h)) _ a)
  have ha_reach_c : EdgeReach c (emb.toFun a) h := ha_reach
  exact ancestor_of_external_notMem_coreSet hc hg h_edge h_ext (emb.toFun a) ha_reach_c

/-- **Fan-in bound for the core** (§7.2/§7.4 input).  Every gate of the extracted core has
at most `w` predecessors, where `w` is a computation-width bound for the source circuit:
the core consists of computation gates only, so its total width is bounded by `w`, and in a
properly layered circuit the predecessors of a gate all lie on one layer. -/
theorem predecessorCount_coreWithPorts_le_width {c : ADRCircuit n}
    {v o : Fin c.gateCount} (ho : o ∈ coreSet c v o) (hwf : WellFormedADR c)
    {w : Nat} (hw : ADRHasWidthAtMost c w) (g : Fin (coreWithPorts c v o ho).gateCount) :
    predecessorCount (coreWithPorts c v o ho) g ≤ w :=
  predecessorCount_le_of_totalWidth (wellFormedADR_coreWithPorts c v o ho hwf).1
    (totalWidthAtMost_coreWithPorts_of_widthAtMost c v o ho hw) g

/-- **The core carries an incidence cylinder** (§7.2).  The extracted core of a
rotation-planar well-formed circuit is properly layered, rotation planar and has a unique
graph source and a unique graph sink, so External Fact 2 applies to it. -/
theorem incidenceCylinder_coreWithPorts (h2 : AllenderOQ3.HansenArcOrderPrinciple)
    {c : ADRCircuit n} {v o : Fin c.gateCount} (ho : o ∈ coreSet c v o)
    (hv : v ∈ coreSet c v o) (hwf : WellFormedADR c) (hplanar : RotationPlanar c) :
    Nonempty (IncidenceCylinder (coreWithPorts c v o ho)) :=
  h2 _ (wellFormedADR_coreWithPorts c v o ho hwf).1
    (rotationPlanar_coreWithPorts c v o ho hplanar)
    (uniqueSource_coreWithPorts c v o ho hwf hv)
    (uniqueSink_coreWithPorts c v o ho hwf)

end AllenderOQ3.Internal
