import AllenderOQ3.Model
import AllenderOQ3.Internal.Surgery
import AllenderOQ3.Internal.IntervalPiercing
import AllenderOQ3.Internal.Subcircuit
import AllenderOQ3.Internal.GenusBudget
import AllenderOQ3.Internal.LayerPath
import AllenderOQ3.Internal.ComponentBlock

set_option autoImplicit false
namespace AllenderOQ3.Internal

/-!
# The layer planarizer (§4)

If a circuit has orientable genus at most `g`, then deleting all gates on at
most `g` suitably chosen layers makes it rotation-planar.

The argument is the classical greedy interval-piercing one.  Every nonempty
vertex set that induces a *connected* non-planar subgraph spans a layer interval
`[layerLo, layerHi]`; `greedy_pierce` extracts from this finite family a pairwise
disjoint subfamily `J` together with an equinumerous piercing set `P`.  Disjoint
layer intervals give vertex-disjoint subgraphs
(`disjoint_intervals_imp_vertex_disjoint`), so the §3 packing bound
`genus_packing` yields `|P| = |J| ≤ g`.  Conversely, if `deleteLayers c P` were
still non-planar it would have a non-planar connected component
(`exists_nonplanar_component`), whose interval is pierced by some layer of `P`;
by the discrete intermediate value theorem (`connected_meets_interval`) that
component would then contain a gate on a deleted layer, which is isolated after
the deletion — contradicting the component's non-planarity.
-/

/-- Creates a circuit by deleting all gates on the specified layers.

Deletion is realised, as everywhere else in this development (compare
`deleteEdge` and `genus_restrict_isolated`), by removing every edge incident to a
deleted gate: the gates on the layers in `P` survive as isolated vertices, which
changes neither the genus nor the planarity of the underlying graph, and the
remaining graph is exactly the induced subgraph on the surviving layers. -/
noncomputable def deleteLayers {n : Nat} (c : ADRCircuit n) (P : Finset Nat) : ADRCircuit n :=
  { c with edge := fun a b => if c.layer a ∈ P ∨ c.layer b ∈ P then false else c.edge a b }

@[simp] theorem deleteLayers_gateCount {n : Nat} (c : ADRCircuit n) (P : Finset Nat) :
    (deleteLayers c P).gateCount = c.gateCount := rfl

@[simp] theorem deleteLayers_output {n : Nat} (c : ADRCircuit n) (P : Finset Nat) :
    (deleteLayers c P).output = c.output := rfl

@[simp] theorem deleteLayers_kind {n : Nat} (c : ADRCircuit n) (P : Finset Nat)
    (g : Fin c.gateCount) : (deleteLayers c P).kind g = c.kind g := rfl

@[simp] theorem deleteLayers_layer {n : Nat} (c : ADRCircuit n) (P : Finset Nat)
    (g : Fin c.gateCount) : (deleteLayers c P).layer g = c.layer g := rfl

@[simp] theorem deleteLayers_edge {n : Nat} (c : ADRCircuit n) (P : Finset Nat)
    (a b : Fin c.gateCount) :
    (deleteLayers c P).edge a b =
      if c.layer a ∈ P ∨ c.layer b ∈ P then false else c.edge a b := rfl

/-- An edge of the layer-deleted circuit is an edge of the original circuit. -/
theorem deleteLayers_edge_imp {n : Nat} {c : ADRCircuit n} {P : Finset Nat}
    {a b : Fin c.gateCount} (h : (deleteLayers c P).edge a b = true) : c.edge a b = true := by
  rw [deleteLayers_edge] at h
  split at h
  · exact absurd h (by simp)
  · exact h

/-- Deleting layers preserves well-formedness. -/
theorem wellFormed_deleteLayers {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (P : Finset Nat) : WellFormedADR (deleteLayers c P) := by
  refine ⟨?_, ?_⟩
  · intro u v h
    exact hc.1 u v (deleteLayers_edge_imp h)
  · intro g hg h
    rw [deleteLayers_edge]
    split
    · rfl
    · exact hc.2 g hg h

/-- Deleting layers preserves the width bound. -/
theorem width_deleteLayers {n : Nat} {c : ADRCircuit n} {w : Nat}
    (hw : ADRHasWidthAtMost c w) (P : Finset Nat) :
    ADRHasWidthAtMost (deleteLayers c P) w := fun ell => hw ell

/-!
### Sub-lemmas for Layer Planarizer
-/

/-- The set of layers met by a subgraph. -/
def layerImage {n : Nat} (c : ADRCircuit n) (S : Finset (Fin c.gateCount)) : Finset Nat :=
  S.image c.layer

/-- A connected subgraph meets every integer layer between its minimum and maximum layers. -/
theorem connected_meets_interval {n : Nat} (c : ADRCircuit n) (hc : WellFormedADR c)
    (S : Finset (Fin c.gateCount))
    (h_conn : ∀ u ∈ S, ∀ v ∈ S, VertexReachable (induceSubgraph c S) u v)
    (a b : Fin c.gateCount) (ha : a ∈ S) (hb : b ∈ S)
    (ell : Nat) (hle : c.layer a ≤ ell) (hge : ell ≤ c.layer b) :
    ell ∈ layerImage c S := by
  have hwf : WellFormedADR (induceSubgraph c S) := wellFormed_induceSubgraph hc S
  have hreach : VertexReachable (induceSubgraph c S) a b := h_conn a ha b hb
  have hlo : min ((induceSubgraph c S).layer a) ((induceSubgraph c S).layer b) ≤ ell := by
    simp only [induceSubgraph_layer]; omega
  have hhi : ell ≤ max ((induceSubgraph c S).layer a) ((induceSubgraph c S).layer b) := by
    simp only [induceSubgraph_layer]; omega
  obtain ⟨w, hw1, hw2⟩ := connected_meets_layer hwf hreach hlo hhi
  have hwS : w ∈ S := reachable_induceSubgraph_mem c S ha hw1
  have hwl : c.layer w = ell := hw2
  show ell ∈ S.image c.layer
  exact Finset.mem_image.mpr ⟨w, hwS, hwl⟩

/-- Disjoint layer images imply vertex-disjoint subgraphs. -/
theorem disjoint_intervals_imp_vertex_disjoint {n : Nat} (c : ADRCircuit n)
    (S₁ S₂ : Finset (Fin c.gateCount))
    (h : Disjoint (layerImage c S₁) (layerImage c S₂)) :
    Disjoint S₁ S₂ := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  exact Finset.disjoint_left.mp h (Finset.mem_image_of_mem c.layer hv1)
    (Finset.mem_image_of_mem c.layer hv2)

/-!
### Layer intervals of a vertex set
-/

/-- The least layer met by a vertex set (`0` for the empty set). -/
noncomputable def layerLo {n : Nat} (c : ADRCircuit n) (S : Finset (Fin c.gateCount)) : Nat := by
  classical
  exact if h : (layerImage c S).Nonempty then (layerImage c S).min' h else 0

/-- The greatest layer met by a vertex set (`0` for the empty set). -/
noncomputable def layerHi {n : Nat} (c : ADRCircuit n) (S : Finset (Fin c.gateCount)) : Nat := by
  classical
  exact if h : (layerImage c S).Nonempty then (layerImage c S).max' h else 0

theorem layerLo_of_nonempty {n : Nat} (c : ADRCircuit n) {S : Finset (Fin c.gateCount)}
    (h : S.Nonempty) : layerLo c S = (layerImage c S).min' (h.image c.layer) := by
  classical
  have hne : (layerImage c S).Nonempty := h.image c.layer
  rw [layerLo, dif_pos hne]

theorem layerHi_of_nonempty {n : Nat} (c : ADRCircuit n) {S : Finset (Fin c.gateCount)}
    (h : S.Nonempty) : layerHi c S = (layerImage c S).max' (h.image c.layer) := by
  classical
  have hne : (layerImage c S).Nonempty := h.image c.layer
  rw [layerHi, dif_pos hne]

theorem layerLo_le_of_mem {n : Nat} (c : ADRCircuit n) {S : Finset (Fin c.gateCount)}
    {v : Fin c.gateCount} (hv : v ∈ S) : layerLo c S ≤ c.layer v := by
  rw [layerLo_of_nonempty c ⟨v, hv⟩]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem c.layer hv)

theorem le_layerHi_of_mem {n : Nat} (c : ADRCircuit n) {S : Finset (Fin c.gateCount)}
    {v : Fin c.gateCount} (hv : v ∈ S) : c.layer v ≤ layerHi c S := by
  rw [layerHi_of_nonempty c ⟨v, hv⟩]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem c.layer hv)

theorem exists_mem_layerLo {n : Nat} (c : ADRCircuit n) {S : Finset (Fin c.gateCount)}
    (h : S.Nonempty) : ∃ v ∈ S, c.layer v = layerLo c S := by
  have hmem := Finset.min'_mem (layerImage c S) (h.image c.layer)
  obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hmem
  exact ⟨v, hv, by rw [layerLo_of_nonempty c h]; exact hveq⟩

theorem exists_mem_layerHi {n : Nat} (c : ADRCircuit n) {S : Finset (Fin c.gateCount)}
    (h : S.Nonempty) : ∃ v ∈ S, c.layer v = layerHi c S := by
  have hmem := Finset.max'_mem (layerImage c S) (h.image c.layer)
  obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hmem
  exact ⟨v, hv, by rw [layerHi_of_nonempty c h]; exact hveq⟩

theorem layerLo_le_layerHi {n : Nat} (c : ADRCircuit n) (S : Finset (Fin c.gateCount))
    (h : S.Nonempty) : layerLo c S ≤ layerHi c S := by
  obtain ⟨v, hv, hveq⟩ := exists_mem_layerLo c h
  exact hveq ▸ le_layerHi_of_mem c hv

/-!
### The family of connected non-planar subgraphs
-/

/-- The nonempty vertex sets that induce a connected non-rotation-planar subgraph. -/
noncomputable def nonplanarConnectedSets {n : Nat} (c : ADRCircuit n) :
    Finset (Finset (Fin c.gateCount)) := by
  classical
  exact Finset.univ.filter (fun S => S.Nonempty ∧
    (∀ u ∈ S, ∀ x ∈ S, VertexReachable (induceSubgraph c S) u x) ∧
    ¬ RotationPlanar (induceSubgraph c S))

theorem mem_nonplanarConnectedSets {n : Nat} (c : ADRCircuit n)
    (S : Finset (Fin c.gateCount)) :
    S ∈ nonplanarConnectedSets c ↔ (S.Nonempty ∧
      (∀ u ∈ S, ∀ x ∈ S, VertexReachable (induceSubgraph c S) u x) ∧
      ¬ RotationPlanar (induceSubgraph c S)) := by
  classical
  simp [nonplanarConnectedSets]

/-- The layer intervals spanned by those subgraphs. -/
noncomputable def nonplanarIntervals {n : Nat} (c : ADRCircuit n) : Finset (Nat × Nat) :=
  (nonplanarConnectedSets c).image (fun S => (layerLo c S, layerHi c S))

/-!
### Compatibility of layer deletion with blocks
-/

/-- An adjacency surviving the deletion of layers is an adjacency of the block. -/
theorem underlyingAdj_blockIn_deleteLayers {n : Nat} {c : ADRCircuit n} {P : Finset Nat}
    {B : Finset (Fin c.gateCount)} {a b : Fin c.gateCount}
    (h : UnderlyingAdj (blockIn (deleteLayers c P) B) a b) :
    UnderlyingAdj (blockIn c B) a b := by
  obtain ⟨h1, hne⟩ := h
  refine ⟨?_, hne⟩
  rcases h1 with he | he
  · obtain ⟨he', ha, hb⟩ := blockIn_edge_true he
    exact Or.inl (by rw [blockIn_edge, if_pos ⟨ha, hb⟩]; exact deleteLayers_edge_imp he')
  · obtain ⟨he', hb, ha⟩ := blockIn_edge_true he
    exact Or.inr (by rw [blockIn_edge, if_pos ⟨hb, ha⟩]; exact deleteLayers_edge_imp he')

/-- Reachability inside a block survives passing from the layer-deleted circuit
back to the original one. -/
theorem reach_blockIn_deleteLayers {n : Nat} {c : ADRCircuit n} {P : Finset Nat}
    {B : Finset (Fin c.gateCount)} {u x : Fin c.gateCount}
    (h : VertexReachable (blockIn (deleteLayers c P) B) u x) :
    VertexReachable (blockIn c B) u x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hadj ih => exact ih.tail (underlyingAdj_blockIn_deleteLayers hadj)

/-- Deleting layers inside a block is a mask of the block. -/
theorem blockIn_deleteLayers_eq_mask {n : Nat} (c : ADRCircuit n) (P : Finset Nat)
    (B : Finset (Fin c.gateCount)) :
    blockIn (deleteLayers c P) B
      = maskCircuit (blockIn c B)
          (fun a b => !(decide (c.layer a ∈ P) || decide (c.layer b ∈ P))) := by
  classical
  unfold blockIn maskCircuit deleteLayers
  congr 1
  funext a b
  by_cases hB : a ∈ B ∧ b ∈ B
  · by_cases hP : c.layer a ∈ P ∨ c.layer b ∈ P
    · rcases hP with hP | hP <;> simp [hB.1, hB.2, hP]
    · push_neg at hP
      simp [hB.1, hB.2, hP.1, hP.2]
  · rw [not_and_or] at hB
    rcases hB with hB | hB <;> simp [hB]

/-- A block of the layer-deleted circuit that is non-planar makes the corresponding
block of the original circuit non-planar. -/
theorem not_rotationPlanar_blockIn_of_deleteLayers {n : Nat} {c : ADRCircuit n}
    {P : Finset Nat} {B : Finset (Fin c.gateCount)}
    (h : ¬ RotationPlanar (blockIn (deleteLayers c P) B)) :
    ¬ RotationPlanar (blockIn c B) := by
  classical
  intro hpl
  apply h
  have hle := genus_maskCircuit_le (blockIn c B)
    (fun a b => !(decide (c.layer a ∈ P) || decide (c.layer b ∈ P)))
  rw [← blockIn_deleteLayers_eq_mask] at hle
  rw [rotationPlanar_iff_genus_zero] at hpl ⊢
  omega

/-- Every gate on a deleted layer is isolated after the deletion. -/
theorem isolated_of_layer_mem {n : Nat} (c : ADRCircuit n) (P : Finset Nat)
    {w : Fin c.gateCount} (hw : c.layer w ∈ P) (y : Fin c.gateCount) :
    ¬ UnderlyingAdj (deleteLayers c P) w y := by
  rintro ⟨h1, -⟩
  have h2 : (deleteLayers c P).edge w y = false := by
    rw [deleteLayers_edge, if_pos (Or.inl hw)]
  have h3 : (deleteLayers c P).edge y w = false := by
    rw [deleteLayers_edge, if_pos (Or.inr hw)]
  rcases h1 with h | h
  · rw [h2] at h; exact Bool.noConfusion h
  · rw [h3] at h; exact Bool.noConfusion h

/-- Reachability transfers from the block description to the induced subgraph. -/
theorem reach_induceSubgraph_of_blockIn {n : Nat} {c : ADRCircuit n}
    {S : Finset (Fin c.gateCount)} {u x : Fin c.gateCount}
    (h : VertexReachable (blockIn c S) u x) : VertexReachable (induceSubgraph c S) u x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hadj ih =>
      refine ih.tail ?_
      obtain ⟨h1, hne⟩ := hadj
      refine ⟨?_, hne⟩
      rcases h1 with he | he
      · obtain ⟨he', ha, hb⟩ := blockIn_edge_true he
        exact Or.inl (by rw [induceSubgraph_edge, if_pos ⟨ha, hb⟩]; exact he')
      · obtain ⟨he', hb, ha⟩ := blockIn_edge_true he
        exact Or.inr (by rw [induceSubgraph_edge, if_pos ⟨hb, ha⟩]; exact he')

/-- Non-planarity transfers from the block description to the induced subgraph. -/
theorem not_rotationPlanar_induceSubgraph_of_blockIn {n : Nat} {c : ADRCircuit n}
    {S : Finset (Fin c.gateCount)} (h : ¬ RotationPlanar (blockIn c S)) :
    ¬ RotationPlanar (induceSubgraph c S) := by
  rw [induceSubgraph_eq_blockIn]
  exact h

/-- For well-formed `c` with `orientableCircuitGenus c ≤ g`, there is a layer set `P`,
`|P| ≤ g`, such that deleting all gates on layers in `P` yields a rotation-planar circuit. -/
theorem layerPlanarizer {n : Nat} (c : ADRCircuit n) (hc : WellFormedADR c) (g : Nat)
    (hg : orientableCircuitGenus c ≤ g) :
    ∃ P : Finset Nat, P.card ≤ g ∧ RotationPlanar (deleteLayers c P) := by
  classical
  have hIle : ∀ p ∈ nonplanarIntervals c, p.1 ≤ p.2 := by
    intro p hp
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hp
    exact layerLo_le_layerHi c S ((mem_nonplanarConnectedSets c S).mp hS).1
  obtain ⟨P, J, hJsub, hJdisj, hPcard, hpierce⟩ := greedy_pierce (nonplanarIntervals c) hIle
  have hexS : ∀ p : Nat × Nat, ∃ S : Finset (Fin c.gateCount),
      p ∈ nonplanarIntervals c →
        (S ∈ nonplanarConnectedSets c ∧ layerLo c S = p.1 ∧ layerHi c S = p.2) := by
    intro p
    by_cases hp : p ∈ nonplanarIntervals c
    · obtain ⟨S, hS, hSp⟩ := Finset.mem_image.mp hp
      exact ⟨S, fun _ => ⟨hS, by rw [← hSp], by rw [← hSp]⟩⟩
    · exact ⟨∅, fun h => absurd h hp⟩
  choose F hF using hexS
  set e := J.equivFin
  have hFmem : ∀ i : Fin J.card,
      F ((e.symm i : {x // x ∈ J}) : Nat × Nat) ∈ nonplanarConnectedSets c ∧
        layerLo c (F ((e.symm i : {x // x ∈ J}) : Nat × Nat))
            = ((e.symm i : {x // x ∈ J}) : Nat × Nat).1 ∧
        layerHi c (F ((e.symm i : {x // x ∈ J}) : Nat × Nat))
            = ((e.symm i : {x // x ∈ J}) : Nat × Nat).2 :=
    fun i => hF _ (hJsub (e.symm i).2)
  have hlayer : ∀ (i : Fin J.card) (v : Fin c.gateCount),
      v ∈ F ((e.symm i : {x // x ∈ J}) : Nat × Nat) →
        ((e.symm i : {x // x ∈ J}) : Nat × Nat).1 ≤ c.layer v ∧
          c.layer v ≤ ((e.symm i : {x // x ∈ J}) : Nat × Nat).2 := by
    intro i v hv
    obtain ⟨-, h1, h2⟩ := hFmem i
    exact ⟨h1 ▸ layerLo_le_of_mem c hv, h2 ▸ le_layerHi_of_mem c hv⟩
  have hJcard : J.card ≤ orientableCircuitGenus c := by
    refine genus_packing c J.card (fun i => F ((e.symm i : {x // x ∈ J}) : Nat × Nat)) ?_ ?_ ?_
    · intro i j hij
      have hne : ((e.symm i : {x // x ∈ J}) : Nat × Nat)
          ≠ ((e.symm j : {x // x ∈ J}) : Nat × Nat) := by
        intro hcon
        exact hij (e.symm.injective (Subtype.ext hcon))
      rw [Finset.disjoint_left]
      intro v hvi hvj
      obtain ⟨pi1, pi2⟩ := hlayer i v hvi
      obtain ⟨pj1, pj2⟩ := hlayer j v hvj
      rcases hJdisj _ (e.symm i).2 _ (e.symm j).2 hne with hlt | hlt <;> omega
    · intro i u hu x hx
      exact ((mem_nonplanarConnectedSets c _).mp (hFmem i).1).2.1 u hu x hx
    · intro i
      exact ((mem_nonplanarConnectedSets c _).mp (hFmem i).1).2.2
  refine ⟨P, by omega, ?_⟩
  by_contra hnp
  obtain ⟨v, hv⟩ := exists_nonplanar_component hnp
  have hBne : (compOf (deleteLayers c P) v).Nonempty :=
    ⟨v, self_mem_compOf (deleteLayers c P) v⟩
  have hconn : ∀ u ∈ compOf (deleteLayers c P) v, ∀ x ∈ compOf (deleteLayers c P) v,
      VertexReachable (induceSubgraph c (compOf (deleteLayers c P) v)) u x := by
    intro u hu x hx
    exact reach_induceSubgraph_of_blockIn
      (reach_blockIn_deleteLayers (reach_blockIn_compOf (deleteLayers c P) v hu hx))
  have hnpB : ¬ RotationPlanar (induceSubgraph c (compOf (deleteLayers c P) v)) := by
    exact not_rotationPlanar_induceSubgraph_of_blockIn
      (not_rotationPlanar_blockIn_of_deleteLayers hv)
  have hBCand : compOf (deleteLayers c P) v ∈ nonplanarConnectedSets c :=
    (mem_nonplanarConnectedSets c _).mpr ⟨hBne, hconn, hnpB⟩
  obtain ⟨x, hxP, hx1, hx2⟩ := hpierce _
    (Finset.mem_image_of_mem (fun S => (layerLo c S, layerHi c S)) hBCand)
  obtain ⟨a, haB, hae⟩ := exists_mem_layerLo c hBne
  obtain ⟨b, hbB, hbe⟩ := exists_mem_layerHi c hBne
  have hmeet := connected_meets_interval c hc (compOf (deleteLayers c P) v) hconn a b haB hbB x
    (by simp only [hae]; exact hx1) (by simp only [hbe]; exact hx2)
  simp only [layerImage] at hmeet
  obtain ⟨w, hwB, hwl⟩ := Finset.mem_image.mp hmeet
  have hiso : ∀ y, ¬ UnderlyingAdj (deleteLayers c P) w y :=
    isolated_of_layer_mem c P (by rw [show c.layer w = x from hwl]; exact hxP)
  have hvw : v = w :=
    eq_of_reachable_isolated hiso
      ((vertexReachable_equiv (deleteLayers c P)).symm (mem_compOf.mp hwB))
  apply hv
  refine rotationPlanar_of_no_adj (fun q r hqr => ?_)
  have hstep := (underlyingAdj_blockIn
    (separatedBy_compOf (deleteLayers c P) v) q r).mp hqr
  have hisov : ∀ y, ¬ UnderlyingAdj (deleteLayers c P) v y := by
    rw [hvw]; exact hiso
  have hqreach : VertexReachable (deleteLayers c P) v q := mem_compOf.mp hstep.2
  have hqv : q = v := eq_of_reachable_isolated (c := deleteLayers c P) hisov hqreach
  exact hisov r (hqv ▸ hstep.1)


end AllenderOQ3.Internal
