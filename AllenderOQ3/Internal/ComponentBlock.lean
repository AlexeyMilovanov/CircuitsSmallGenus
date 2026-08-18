import AllenderOQ3.Internal.BlockMerge

/-!
# Connected components as blocks

A connected component of the underlying graph of a circuit is a separating
vertex set, so it induces a block.  Using the gluing construction of
`AllenderOQ3.Internal.BlockMerge`, a circuit all of whose component blocks are
rotation-planar is itself rotation-planar.  Contrapositively, a non-planar
circuit always contains a *connected* non-planar induced subgraph, namely one of
its components.  This is the ingredient that turns the genus packing bound into
the layer planarizer of §4.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

variable {n : Nat}

/-- The connected component of a vertex, as a finite set of vertices. -/
noncomputable def compOf (c : ADRCircuit n) (v : Fin c.gateCount) :
    Finset (Fin c.gateCount) := by
  classical
  exact Finset.univ.filter (fun u => VertexReachable c v u)

theorem mem_compOf {c : ADRCircuit n} {v u : Fin c.gateCount} :
    u ∈ compOf c v ↔ VertexReachable c v u := by
  classical
  simp [compOf]

theorem self_mem_compOf (c : ADRCircuit n) (v : Fin c.gateCount) : v ∈ compOf c v :=
  mem_compOf.mpr Relation.ReflTransGen.refl

/-- A component is a separating vertex set: no edge leaves it. -/
theorem separatedBy_compOf (c : ADRCircuit n) (v : Fin c.gateCount) :
    SeparatedBy c (compOf c v) := by
  intro a b hab
  by_cases hne : a = b
  · subst hne; exact Iff.rfl
  · have hadj : UnderlyingAdj c a b := ⟨Or.inl hab, hne⟩
    constructor
    · intro ha
      exact mem_compOf.mpr ((mem_compOf.mp ha).tail hadj)
    · intro hb
      exact mem_compOf.mpr ((mem_compOf.mp hb).tail
        ((underlyingAdj_comm (c := c) a b).mp hadj))

/-- Two components are equal or disjoint. -/
theorem compOf_disjoint (c : ADRCircuit n) (v w : Fin c.gateCount)
    (h : w ∉ compOf c v) : Disjoint (compOf c v) (compOf c w) := by
  rw [Finset.disjoint_left]
  intro x hxv hxw
  apply h
  refine mem_compOf.mpr ((mem_compOf.mp hxv).trans ?_)
  exact (vertexReachable_equiv c).symm (mem_compOf.mp hxw)

/-- Every vertex of a component is reachable from every other one inside the block
induced by the component. -/
theorem reach_blockIn_compOf (c : ADRCircuit n) (v : Fin c.gateCount)
    {u x : Fin c.gateCount} (hu : u ∈ compOf c v) (hx : x ∈ compOf c v) :
    VertexReachable (blockIn c (compOf c v)) u x := by
  have hc : VertexReachable c u x :=
    ((vertexReachable_equiv c).symm (mem_compOf.mp hu)).trans (mem_compOf.mp hx)
  exact (reach_blockIn_of_reach (separatedBy_compOf c v) hu hc).1

/-- Reachability from an isolated vertex is trivial. -/
theorem eq_of_reachable_isolated {c : ADRCircuit n} {w x : Fin c.gateCount}
    (hiso : ∀ y, ¬ UnderlyingAdj c w y) (h : VertexReachable c w x) : x = w := by
  induction h with
  | refl => rfl
  | @tail b d _hwb hbd ih => exact absurd (ih ▸ hbd) (hiso d)

/-- An edgeless circuit is rotation-planar. -/
theorem rotationPlanar_of_no_adj {c : ADRCircuit n} (h : ∀ u v, ¬ UnderlyingAdj c u v) :
    RotationPlanar c := by
  obtain ⟨rot, _⟩ := exists_rotation_genus_eq c
  refine ⟨rot, ?_⟩
  obtain ⟨hI, hC, hE, hF⟩ := counts_of_no_adj h rot
  change (2 * componentCount c + underlyingEdgeCount c - c.gateCount -
    (permCycleCount (facePermutation rot) + isolatedVertexCount c)) / 2 = 0
  omega

/-- The vertices of `c` that have at least one neighbour. -/
noncomputable def nonIsolatedSet (c : ADRCircuit n) : Finset (Fin c.gateCount) := by
  classical
  exact Finset.univ.filter (fun u => ∃ v, UnderlyingAdj c u v)

theorem mem_nonIsolatedSet {c : ADRCircuit n} {u : Fin c.gateCount} :
    u ∈ nonIsolatedSet c ↔ ∃ v, UnderlyingAdj c u v := by
  classical
  simp [nonIsolatedSet]

/-- If every component block of `c` is rotation-planar, then so is `c`. -/
theorem rotationPlanar_of_component_blocks_aux : ∀ (k : Nat) (c : ADRCircuit n),
    (nonIsolatedSet c).card ≤ k →
    (∀ v, RotationPlanar (blockIn c (compOf c v))) → RotationPlanar c := by
  intro k
  induction k with
  | zero =>
      intro c hcard _
      refine rotationPlanar_of_no_adj (fun u v hadj => ?_)
      have : u ∈ nonIsolatedSet c := mem_nonIsolatedSet.mpr ⟨v, hadj⟩
      have : 0 < (nonIsolatedSet c).card := Finset.card_pos.mpr ⟨u, this⟩
      omega
  | succ k ih =>
      intro c hcard hcomp
      by_cases hno : ∀ u v, ¬ UnderlyingAdj c u v
      · exact rotationPlanar_of_no_adj hno
      push_neg at hno
      obtain ⟨u₀, v₀, hadj⟩ := hno
      set A : Finset (Fin c.gateCount) := compOf c u₀ with hA
      have hsep : SeparatedBy c A := separatedBy_compOf c u₀
      have hu₀A : u₀ ∈ A := self_mem_compOf c u₀
      -- the second block has strictly fewer non-isolated vertices
      have hsub : nonIsolatedSet (blockOut c A) ⊆ nonIsolatedSet c := by
        intro x hx
        obtain ⟨y, hy⟩ := mem_nonIsolatedSet.mp hx
        exact mem_nonIsolatedSet.mpr ⟨y, ((underlyingAdj_blockOut hsep x y).mp hy).1⟩
      have hu₀not : u₀ ∉ nonIsolatedSet (blockOut c A) := by
        intro hmem
        obtain ⟨y, hy⟩ := mem_nonIsolatedSet.mp hmem
        exact ((underlyingAdj_blockOut hsep u₀ y).mp hy).2 hu₀A
      have hu₀in : u₀ ∈ nonIsolatedSet c := mem_nonIsolatedSet.mpr ⟨v₀, hadj⟩
      have hlt : (nonIsolatedSet (blockOut c A)).card < (nonIsolatedSet c).card :=
        Finset.card_lt_card ⟨hsub, fun hcon => hu₀not (hcon hu₀in)⟩
      -- every component block of the second block is planar
      have hcompOut : ∀ w, RotationPlanar (blockIn (blockOut c A) (compOf (blockOut c A) w)) := by
        intro w
        by_cases hw : w ∈ A
        · refine rotationPlanar_of_no_adj (fun x y hxy => ?_)
          have hiso : ∀ y, ¬ UnderlyingAdj (blockOut c A) w y := by
            intro y hy
            exact ((underlyingAdj_blockOut hsep w y).mp hy).2 hw
          have hstep := (underlyingAdj_blockIn
            (separatedBy_compOf (blockOut c A) w) x y).mp hxy
          have hreach : VertexReachable (blockOut c A) w x := mem_compOf.mp hstep.2
          have hxw : x = w := eq_of_reachable_isolated (c := blockOut c A) hiso hreach
          exact hiso y (hxw ▸ hstep.1)
        · have hcompeq : compOf (blockOut c A) w = compOf c w := by
            ext x
            constructor
            · intro hx
              exact mem_compOf.mpr (reach_of_reach_blockOut hsep (mem_compOf.mp hx))
            · intro hx
              exact mem_compOf.mpr (reach_blockOut_of_reach hsep hw (mem_compOf.mp hx)).1
          rw [hcompeq, blockIn_blockOut_of_disjoint (compOf_disjoint c u₀ w hw)]
          exact hcomp w
      have hOut : RotationPlanar (blockOut c A) :=
        ih (blockOut c A) (by omega) hcompOut
      exact rotationPlanar_of_blocks hsep (hcomp u₀) hOut

/-- A non-planar circuit has a non-planar connected component. -/
theorem exists_nonplanar_component {c : ADRCircuit n} (h : ¬ RotationPlanar c) :
    ∃ v, ¬ RotationPlanar (blockIn c (compOf c v)) := by
  by_contra hcon
  push_neg at hcon
  exact h (rotationPlanar_of_component_blocks_aux (nonIsolatedSet c).card c (Nat.le_refl _) hcon)

end AllenderOQ3.Internal
