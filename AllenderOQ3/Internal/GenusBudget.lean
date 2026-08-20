import AllenderOQ3.Incidence
import AllenderOQ3.Internal.RotationExists
import AllenderOQ3.Internal.BlockGenus

/-!
# Genus budget: the planarity/genus characterisation (§3)

This file opens the genus budget of `docs/MATHEMATICAL_PROOF.md` §3.  The first,
purely elementary, ingredient is the bridge between the finite predicate
`RotationPlanar` and the numeric invariant `orientableCircuitGenus`: a circuit is
rotation-planar exactly when its minimum orientable rotation genus is zero.

Consequently a circuit that is *not* rotation-planar has minimum genus at least
one.  That is the per-component base contribution used by the packing argument
for vertex-disjoint nonplanar subgraphs (each such subgraph, once isolated as a
distinct component, contributes at least one to the total genus).

These two lemmas depend only on the frozen model and on
`AllenderOQ3.Internal.RotationExists` (nonemptiness/attainment of the genus set);
they add no `sorry` and no external assumption.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- A circuit is rotation-planar iff its minimum orientable rotation genus is
zero.

* Forward: a zero-genus rotation puts `0` in the genus set, so the infimum
  `orientableCircuitGenus` is at most `0`, hence equal to `0`.
* Backward: the infimum is attained by some rotation (`exists_rotation_genus_eq`),
  so genus `0` produces a rotation of genus `0`, i.e. rotation-planarity. -/
theorem rotationPlanar_iff_genus_zero {n : Nat} (c : ADRCircuit n) :
    RotationPlanar c ↔ orientableCircuitGenus c = 0 := by
  constructor
  · rintro ⟨r, hr⟩
    have hle : orientableCircuitGenus c ≤ 0 := Nat.sInf_le ⟨r, hr⟩
    omega
  · intro h
    obtain ⟨r, hr⟩ := exists_rotation_genus_eq c
    rw [h] at hr
    exact ⟨r, hr⟩

/-- A circuit that is not rotation-planar has minimum orientable genus at least
one.  This is the base contribution of one nonplanar component in the §3 genus
budget. -/
theorem not_rotationPlanar_imp_genus_pos {n : Nat} (c : ADRCircuit n) :
    ¬ RotationPlanar c → 1 ≤ orientableCircuitGenus c := by
  intro hnp
  by_contra hlt
  apply hnp
  rw [rotationPlanar_iff_genus_zero]
  omega

/-!
The §3 genus packing capstone (`r` vertex-disjoint non-rotation-planar connected
subgraphs imply `r ≤ orientableCircuitGenus c`) is stated below. We define the
subgraph induced by a set of vertices by removing all edges with an endpoint
outside the set.
-/

/-- The circuit obtained by deleting all edges with at least one endpoint outside `S`. -/
noncomputable def induceSubgraph {n : Nat} (c : ADRCircuit n) (S : Finset (Fin c.gateCount)) :
  ADRCircuit n :=
  { c with edge := fun a b => if a ∈ S ∧ b ∈ S then c.edge a b else false }

@[simp] theorem induceSubgraph_gateCount {n : Nat} (c : ADRCircuit n)
  (S : Finset (Fin c.gateCount)) :
    (induceSubgraph c S).gateCount = c.gateCount := rfl

@[simp] theorem induceSubgraph_edge {n : Nat} (c : ADRCircuit n) (S : Finset (Fin c.gateCount))
  (a b : Fin c.gateCount) :
    (induceSubgraph c S).edge a b = if a ∈ S ∧ b ∈ S then c.edge a b else false := rfl

@[simp] theorem induceSubgraph_layer {n : Nat} (c : ADRCircuit n) (S : Finset (Fin c.gateCount))
    (g : Fin c.gateCount) : (induceSubgraph c S).layer g = c.layer g := rfl

/-- An edge of an induced subgraph is an edge of the original circuit. -/
theorem induceSubgraph_edge_imp {n : Nat} {c : ADRCircuit n} {S : Finset (Fin c.gateCount)}
    {a b : Fin c.gateCount} (h : (induceSubgraph c S).edge a b = true) : c.edge a b = true := by
  rw [induceSubgraph_edge] at h
  split at h
  · exact h
  · exact absurd h (by simp)

/-- Both endpoints of an edge of an induced subgraph lie in the inducing set. -/
theorem induceSubgraph_edge_mem {n : Nat} {c : ADRCircuit n} {S : Finset (Fin c.gateCount)}
    {a b : Fin c.gateCount} (h : (induceSubgraph c S).edge a b = true) : a ∈ S ∧ b ∈ S := by
  by_cases hcond : a ∈ S ∧ b ∈ S
  · exact hcond
  · rw [induceSubgraph_edge, if_neg hcond] at h
    exact absurd h (by simp)

/-- The induced subgraph of a well-formed circuit is well-formed: it only deletes
edges (never lowers a layer gap) and inherits the kind/layer data unchanged. -/
theorem wellFormed_induceSubgraph {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (S : Finset (Fin c.gateCount)) : WellFormedADR (induceSubgraph c S) := by
  refine ⟨?_, ?_⟩
  · intro u v h
    exact hc.1 u v (induceSubgraph_edge_imp h)
  · intro g hg h
    rw [induceSubgraph_edge]
    split
    · exact hc.2 g hg h
    · rfl

/-- Reachability inside an induced subgraph never leaves the inducing set: every
vertex reachable from a vertex of `S` (using only `S`-internal edges) is in `S`. -/
theorem reachable_induceSubgraph_mem {n : Nat} (c : ADRCircuit n) (S : Finset (Fin c.gateCount))
    {a w : Fin c.gateCount} (ha : a ∈ S)
    (h : VertexReachable (induceSubgraph c S) a w) : w ∈ S := by
  induction h with
  | refl => exact ha
  | @tail b d _hab hbd _ih =>
      rcases hbd.1 with hedge | hedge
      · exact (induceSubgraph_edge_mem hedge).2
      · exact (induceSubgraph_edge_mem hedge).1

/-- The subgraph induced by a set of vertices is the block spanned by the edges
inside that set. -/
theorem induceSubgraph_eq_blockIn {n : Nat} (c : ADRCircuit n) (S : Finset (Fin c.gateCount)) :
    induceSubgraph c S = blockIn c S := by
  unfold induceSubgraph blockIn maskCircuit
  congr 1
  funext a b
  by_cases hab : a ∈ S ∧ b ∈ S
  · simp [hab]
  · simp [hab]

/-- If `r` vertex-disjoint connected subgraphs are non-planar, the genus is at least `r`.

The connectivity hypothesis `_h_conn` is kept because it is part of the intended
reading of the statement; the proof does not need it, since the genus is already
superadditive over vertex-disjoint subgraphs whether or not they are connected. -/
theorem genus_packing {n : Nat} (c : ADRCircuit n) (r : Nat)
    (S : Fin r → Finset (Fin c.gateCount))
    (h_disj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (_h_conn : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, VertexReachable (induceSubgraph c (S i)) u v)
    (h_nonplanar : ∀ i, ¬ RotationPlanar (induceSubgraph c (S i))) :
    r ≤ orientableCircuitGenus c := by
  classical
  have hdisj : (List.ofFn S).Pairwise Disjoint :=
    List.pairwise_ofFn.mpr (fun i j hij => h_disj i j (Fin.ne_of_lt hij))
  have hnp : ∀ A ∈ List.ofFn S, ¬ RotationPlanar (blockIn c A) := by
    intro A hA
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
    rw [← induceSubgraph_eq_blockIn]
    exact h_nonplanar i
  have hle := length_le_genus_of_blocks c (List.ofFn S) hdisj hnp
  rwa [List.length_ofFn] at hle

end AllenderOQ3.Internal
