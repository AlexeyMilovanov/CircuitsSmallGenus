import AllenderOQ3.Internal.BlockGenus

/-!
# Euler's formula for rotation systems

`rotationGenus` is defined by the truncated natural-number expression

```text
(2 * componentCount c + underlyingEdgeCount c - c.gateCount - (faces)) / 2.
```

This file proves that the quantity being halved, the *Euler defect*, is genuinely
a nonnegative even number:

```text
2 * C + E = V + (F + I) + 2 * k.
```

The proof is Euler's classical induction on the number of edges.  The base case
is an edgeless circuit, where `C = V`, `I = V`, `E = 0` and there are no darts,
so the defect vanishes.  The inductive step deletes one directed edge and uses
the exact surgery counts of `AllenderOQ3.Internal.DeleteEdge`: deleting an edge
whose reverse is also present changes nothing at all, and deleting a genuine edge
changes the defect by `0` or `2`.

Two consequences are recorded: the defect of a rotation is exactly twice its
genus, and a rotation of genus zero has defect exactly zero.  These are what
turns the *inequality* bookkeeping of the block decomposition into an *identity*.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n : Nat}

/-- Reachability only depends on the underlying adjacency. -/
theorem reach_congr_of_adj_eq {c : ADRCircuit n} {u v : Fin c.gateCount}
    (h : ∀ a b, UnderlyingAdj (deleteEdge c u v) a b ↔ UnderlyingAdj c a b)
    (a b : Fin c.gateCount) :
    VertexReachable (deleteEdge c u v) a b ↔ VertexReachable c a b := by
  constructor
  · intro hh
    induction hh with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hadj ih => exact ih.tail ((h _ _).mp hadj)
  · intro hh
    induction hh with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hadj ih => exact ih.tail ((h _ _).mpr hadj)

/-- A deletion that does not change the underlying graph changes none of the three
vertex/edge counts. -/
theorem counts_deleteEdge_of_adj_eq (c : ADRCircuit n) (u v : Fin c.gateCount)
    (h : ∀ a b, UnderlyingAdj (deleteEdge c u v) a b ↔ UnderlyingAdj c a b) :
    componentCount (deleteEdge c u v) = componentCount c ∧
      isolatedVertexCount (deleteEdge c u v) = isolatedVertexCount c ∧
      underlyingEdgeCount (deleteEdge c u v) = underlyingEdgeCount c := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · unfold componentCount
    refine card_filter_congr_of_iff (N := c.gateCount) _ _ _ _ (fun w => ?_)
    exact forall_congr' (fun x => imp_congr_left (reach_congr_of_adj_eq h w x))
  · unfold isolatedVertexCount
    refine card_filter_congr_of_iff (N := c.gateCount) _ _ _ _ (fun w => ?_)
    exact forall_congr' (fun x => not_congr (h w x))
  · have h1 := two_mul_underlyingEdgeCount (deleteEdge c u v)
    have h2 := two_mul_underlyingEdgeCount c
    have h3 : Fintype.card (CircuitDart (deleteEdge c u v)) = Fintype.card (CircuitDart c) :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun p => h p.1 p.2))
    omega

/-- A deletion that does not change the underlying graph transports rotations
without changing the face count. -/
theorem exists_transport_deleteEdge (c : ADRCircuit n) (u v : Fin c.gateCount)
    (h : ∀ a b, UnderlyingAdj (deleteEdge c u v) a b ↔ UnderlyingAdj c a b)
    (r : OrientableRotation c) :
    ∃ r' : OrientableRotation (deleteEdge c u v),
      permCycleCount (facePermutation r') = permCycleCount (facePermutation r) := by
  classical
  set phi : CircuitDart (deleteEdge c u v) ≃ CircuitDart c :=
    Equiv.subtypeEquivRight (fun p => h p.1 p.2) with hphi
  have hs : ∀ d e : CircuitDart (deleteEdge c u v),
      (phi d).source = (phi e).source ↔ d.source = e.source := fun _ _ => Iff.rfl
  have hrev : ∀ d : CircuitDart (deleteEdge c u v),
      phi (dartReverse (deleteEdge c u v) d) = dartReverse c (phi d) := fun _ => rfl
  exact ⟨transportRotation phi hs r, permCycleCount_facePermutation_transport phi hs hrev r⟩

/-- Deleting a directed edge that is present strictly decreases the number of
directed edges. -/
theorem card_directed_deleteEdge_lt (c : ADRCircuit n) (u v : Fin c.gateCount)
    (huv : c.edge u v = true) :
    (Finset.univ.filter (fun p : Fin c.gateCount × Fin c.gateCount =>
        (deleteEdge c u v).edge p.1 p.2 = true)).card
      < (Finset.univ.filter (fun p : Fin c.gateCount × Fin c.gateCount =>
        c.edge p.1 p.2 = true)).card := by
  classical
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, deleteEdge_edge] at hp ⊢
    split at hp
    · exact absurd hp (by simp)
    · exact hp
  · intro hcon
    have hmem : ((u, v) : Fin c.gateCount × Fin c.gateCount) ∈
        Finset.univ.filter
          (fun p : Fin c.gateCount × Fin c.gateCount => c.edge p.1 p.2 = true) := by
      simp [huv]
    have hmem' := hcon hmem
    simp [deleteEdge_edge] at hmem'

/-- Euler's formula, by induction on the number of directed edges. -/
theorem exists_euler_defect_aux : ∀ (m : Nat) (c : ADRCircuit n) (r : OrientableRotation c),
    (Finset.univ.filter (fun p : Fin c.gateCount × Fin c.gateCount =>
      c.edge p.1 p.2 = true)).card ≤ m →
    ∃ k : Nat, 2 * componentCount c + underlyingEdgeCount c
      = c.gateCount + (permCycleCount (facePermutation r) + isolatedVertexCount c) + 2 * k := by
  intro m
  induction m with
  | zero =>
      intro c r hcard
      have hnoedge : ∀ a b : Fin c.gateCount, c.edge a b = false := by
        intro a b
        by_contra hab
        have hab' : c.edge a b = true := by simpa using hab
        have hmem : ((a, b) : Fin c.gateCount × Fin c.gateCount) ∈
            Finset.univ.filter
              (fun p : Fin c.gateCount × Fin c.gateCount => c.edge p.1 p.2 = true) := by
          simp [hab']
        have := Finset.card_pos.mpr ⟨_, hmem⟩
        omega
      have hno : ∀ a b : Fin c.gateCount, ¬ UnderlyingAdj c a b := by
        intro a b hadj
        rcases hadj.1 with he | he
        · rw [hnoedge a b] at he; exact Bool.noConfusion he
        · rw [hnoedge b a] at he; exact Bool.noConfusion he
      obtain ⟨hI, hC, hE, hF⟩ := counts_of_no_adj hno r
      exact ⟨0, by omega⟩
  | succ m ih =>
      intro c r hcard
      by_cases hex : ∃ u v : Fin c.gateCount, c.edge u v = true
      · obtain ⟨u, v, huv⟩ := hex
        have hcard' : (Finset.univ.filter (fun p : Fin c.gateCount × Fin c.gateCount =>
            (deleteEdge c u v).edge p.1 p.2 = true)).card ≤ m := by
          have := card_directed_deleteEdge_lt c u v huv
          omega
        by_cases hdeg : c.edge v u = true ∨ u = v
        · have hadj := adj_deleteEdge_iff_of_degenerate c u v (Or.inr hdeg)
          obtain ⟨r', hF⟩ := exists_transport_deleteEdge c u v hadj r
          obtain ⟨hC, hI, hE⟩ := counts_deleteEdge_of_adj_eq c u v hadj
          obtain ⟨k, hk⟩ := ih (deleteEdge c u v) r' hcard'
          simp only [deleteEdge_gateCount] at hk
          exact ⟨k, by omega⟩
        · push_neg at hdeg
          have hvu : c.edge v u = false := by simpa using hdeg.1
          have hne : u ≠ v := hdeg.2
          obtain ⟨k, hk⟩ := ih (deleteEdge c u v) (deleteRotation huv hvu hne r) hcard'
          simp only [deleteEdge_gateCount] at hk
          have hsplit := permCycleCount_faceSplice_split r.rotation (deletedDart huv hne)
          have hface := permCycleCount_faceSplice r (deletedDart huv hne)
          have hfaceNew := permCycleCount_facePermutation_deleteRotation huv hvu hne r
          have hiso := isolatedVertexCount_deleteEdge huv hvu hne
          have hcardd := card_dart_deleteEdge huv hvu hne
          have hE1 := two_mul_underlyingEdgeCount (deleteEdge c u v)
          have hE2 := two_mul_underlyingEdgeCount c
          have hu : ((facePermutation r)⁻¹ (deletedDart huv hne)
                = dartReverse c (deletedDart huv hne))
              ↔ (∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) u w) := by
            refine Iff.trans ?_
              (rotation_fixed_iff_isolated huv hvu hne r (deletedDart huv hne) (Or.inl rfl))
            rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
            have h2 : facePermutation r (dartReverse c (deletedDart huv hne))
                = r.rotation (deletedDart huv hne) := by
              change r.rotation (dartReverse c (dartReverse c (deletedDart huv hne)))
                = r.rotation (deletedDart huv hne)
              rw [dartReverse_reverse]
            rw [h2]
            exact ⟨fun h => h.symm, fun h => h.symm⟩
          have hv : ((facePermutation r)⁻¹ (dartReverse c (deletedDart huv hne))
                = deletedDart huv hne)
              ↔ (∀ w : Fin c.gateCount, ¬ UnderlyingAdj (deleteEdge c u v) v w) := by
            refine Iff.trans ?_ (rotation_fixed_iff_isolated huv hvu hne r
              (dartReverse c (deletedDart huv hne)) (Or.inr rfl))
            rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
            have h2 : facePermutation r (deletedDart huv hne)
                = r.rotation (dartReverse c (deletedDart huv hne)) := rfl
            rw [h2]
            exact ⟨fun h => h.symm, fun h => h.symm⟩
          simp only [hu, hv] at hface
          by_cases hreach : VertexReachable (deleteEdge c u v) u v
          · have hC := componentCount_deleteEdge_of_reach hvu hreach
            by_cases hsc : (facePermutation r).SameCycle (deletedDart huv hne)
                (dartReverse c (deletedDart huv hne))
            · rw [if_pos hsc] at hface
              exact ⟨k + 1, by omega⟩
            · rw [if_neg hsc] at hface
              exact ⟨k, by omega⟩
          · have hC := componentCount_deleteEdge_of_not_reach huv hvu hne hreach
            have hsc := sameCycle_of_not_reach huv hvu hne r hreach
            rw [if_pos hsc] at hface
            exact ⟨k, by omega⟩
      · push_neg at hex
        have hnoedge : ∀ a b : Fin c.gateCount, c.edge a b = false := by
          intro a b
          simpa using hex a b
        have hno : ∀ a b : Fin c.gateCount, ¬ UnderlyingAdj c a b := by
          intro a b hadj
          rcases hadj.1 with he | he
          · rw [hnoedge a b] at he; exact Bool.noConfusion he
          · rw [hnoedge b a] at he; exact Bool.noConfusion he
        obtain ⟨hI, hC, hE, hF⟩ := counts_of_no_adj hno r
        exact ⟨0, by omega⟩

/-- **Euler's formula.** The Euler defect of any rotation system is twice a
natural number, namely twice the genus of that rotation system. -/
theorem exists_euler_defect (c : ADRCircuit n) (r : OrientableRotation c) :
    ∃ k : Nat, 2 * componentCount c + underlyingEdgeCount c
      = c.gateCount + (permCycleCount (facePermutation r) + isolatedVertexCount c) + 2 * k :=
  exists_euler_defect_aux _ c r (Nat.le_refl _)

/-- The Euler defect of a rotation system is exactly twice its genus. -/
theorem euler_defect_eq_two_mul_genus (c : ADRCircuit n) (r : OrientableRotation c) :
    2 * componentCount c + underlyingEdgeCount c
      = c.gateCount + (permCycleCount (facePermutation r) + isolatedVertexCount c)
        + 2 * rotationGenus r := by
  obtain ⟨k, hk⟩ := exists_euler_defect c r
  have hg : rotationGenus r = (2 * componentCount c + underlyingEdgeCount c - c.gateCount -
      (permCycleCount (facePermutation r) + isolatedVertexCount c)) / 2 := rfl
  omega

/-- A rotation system of genus zero has Euler defect exactly zero. -/
theorem defect_eq_of_rotationGenus_zero {c : ADRCircuit n} {r : OrientableRotation c}
    (h : rotationGenus r = 0) :
    2 * componentCount c + underlyingEdgeCount c
      = c.gateCount + (permCycleCount (facePermutation r) + isolatedVertexCount c) := by
  have := euler_defect_eq_two_mul_genus c r
  omega

end AllenderOQ3.Internal
