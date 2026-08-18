import AllenderOQ3.Internal.Surgery
import AllenderOQ3.Internal.GenusBudget

/-!
# Deleting a whole set of edges

`AllenderOQ3.Internal.Surgery` shows that deleting one directed edge never
increases the rotation genus (`genus_deleteEdge_le`).  The genus budget of
`docs/MATHEMATICAL_PROOF.md` §3 needs the iterated form: deleting *any* list of
edges never increases the genus, and in particular a rotation-planar circuit
stays rotation-planar after any set of deletions.

Iterating `deleteEdge` is awkward because its edge arguments live in
`Fin c.gateCount`, a type that mentions the circuit being modified.  Since
deletion never changes the gate count, we phrase the deletion by raw indices
(`deleteEdgeNat`), which is literally `deleteEdge` when the indices are in range
and the identity otherwise, and can therefore be folded over a list.

All results here are `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n : Nat}

/-- Delete the directed edge with the given raw endpoint indices.  Out-of-range
indices delete nothing. -/
def deleteEdgeNat (c : ADRCircuit n) (p : Nat × Nat) : ADRCircuit n :=
  { c with edge := fun a b => if a.val = p.1 ∧ b.val = p.2 then false else c.edge a b }

@[simp] theorem deleteEdgeNat_gateCount (c : ADRCircuit n) (p : Nat × Nat) :
    (deleteEdgeNat c p).gateCount = c.gateCount := rfl

@[simp] theorem deleteEdgeNat_layer (c : ADRCircuit n) (p : Nat × Nat)
    (g : Fin c.gateCount) : (deleteEdgeNat c p).layer g = c.layer g := rfl

@[simp] theorem deleteEdgeNat_kind (c : ADRCircuit n) (p : Nat × Nat)
    (g : Fin c.gateCount) : (deleteEdgeNat c p).kind g = c.kind g := rfl

@[simp] theorem deleteEdgeNat_output (c : ADRCircuit n) (p : Nat × Nat) :
    (deleteEdgeNat c p).output = c.output := rfl

/-- With in-range indices, `deleteEdgeNat` is exactly `deleteEdge`. -/
theorem deleteEdgeNat_eq_deleteEdge (c : ADRCircuit n) (p : Nat × Nat)
    (u v : Fin c.gateCount) (hu : u.val = p.1) (hv : v.val = p.2) :
    deleteEdgeNat c p = deleteEdge c u v := by
  unfold deleteEdgeNat deleteEdge
  congr 1
  funext a b
  have h : (a.val = p.1 ∧ b.val = p.2) ↔ (a = u ∧ b = v) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨hu, hv⟩
  by_cases hc : a.val = p.1 ∧ b.val = p.2
  · rw [if_pos hc, if_pos (h.mp hc)]
  · rw [if_neg hc, if_neg (fun hh => hc (h.mpr hh))]

/-- With an out-of-range index, `deleteEdgeNat` changes nothing. -/
theorem deleteEdgeNat_eq_self (c : ADRCircuit n) (p : Nat × Nat)
    (hp : c.gateCount ≤ p.1 ∨ c.gateCount ≤ p.2) : deleteEdgeNat c p = c := by
  unfold deleteEdgeNat
  congr 1
  funext a b
  have hc : ¬ (a.val = p.1 ∧ b.val = p.2) := by
    rintro ⟨h1, h2⟩
    have ha := a.isLt
    have hb := b.isLt
    rcases hp with hp | hp <;> omega
  rw [if_neg hc]

/-- Deleting one edge, addressed by raw indices, never increases the genus. -/
theorem genus_deleteEdgeNat_le (c : ADRCircuit n) (p : Nat × Nat) :
    orientableCircuitGenus (deleteEdgeNat c p) ≤ orientableCircuitGenus c := by
  by_cases hp : p.1 < c.gateCount ∧ p.2 < c.gateCount
  · rw [deleteEdgeNat_eq_deleteEdge c p ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩ rfl rfl]
    exact genus_deleteEdge_le c _ _
  · rw [deleteEdgeNat_eq_self c p (by omega)]

/-- Well-formedness survives deletion by raw indices. -/
theorem wellFormed_deleteEdgeNat {c : ADRCircuit n} (hc : WellFormedADR c)
    (p : Nat × Nat) : WellFormedADR (deleteEdgeNat c p) := by
  constructor
  · intro a b hab
    dsimp [deleteEdgeNat] at hab
    split at hab
    · contradiction
    · exact hc.1 a b hab
  · intro g hg h
    dsimp [deleteEdgeNat]
    split
    · rfl
    · exact hc.2 g hg h

/-- The computation width is unchanged by deletion. -/
theorem width_deleteEdgeNat {c : ADRCircuit n} {p : Nat × Nat} {w : Nat}
    (hw : ADRHasWidthAtMost c w) : ADRHasWidthAtMost (deleteEdgeNat c p) w :=
  fun ell => hw ell

/-- Delete a whole list of edges, addressed by raw endpoint indices. -/
def deleteEdges (c : ADRCircuit n) (es : List (Nat × Nat)) : ADRCircuit n :=
  es.foldl deleteEdgeNat c

@[simp] theorem deleteEdges_nil (c : ADRCircuit n) : deleteEdges c [] = c := rfl

@[simp] theorem deleteEdges_cons (c : ADRCircuit n) (p : Nat × Nat)
    (es : List (Nat × Nat)) :
    deleteEdges c (p :: es) = deleteEdges (deleteEdgeNat c p) es := rfl

@[simp] theorem deleteEdges_gateCount (c : ADRCircuit n) (es : List (Nat × Nat)) :
    (deleteEdges c es).gateCount = c.gateCount := by
  induction es generalizing c with
  | nil => rfl
  | cons p es ih => simpa using ih (deleteEdgeNat c p)

/-- Deleting any set of edges never increases the rotation genus. -/
theorem genus_deleteEdges_le (c : ADRCircuit n) (es : List (Nat × Nat)) :
    orientableCircuitGenus (deleteEdges c es) ≤ orientableCircuitGenus c := by
  induction es generalizing c with
  | nil => exact le_refl _
  | cons p es ih =>
      exact le_trans (ih (deleteEdgeNat c p)) (genus_deleteEdgeNat_le c p)

/-- Well-formedness survives deleting any set of edges. -/
theorem wellFormed_deleteEdges {c : ADRCircuit n} (hc : WellFormedADR c)
    (es : List (Nat × Nat)) : WellFormedADR (deleteEdges c es) := by
  induction es generalizing c with
  | nil => exact hc
  | cons p es ih => exact ih (wellFormed_deleteEdgeNat hc p)

/-- The computation width survives deleting any set of edges. -/
theorem width_deleteEdges {c : ADRCircuit n} {w : Nat} (hw : ADRHasWidthAtMost c w)
    (es : List (Nat × Nat)) : ADRHasWidthAtMost (deleteEdges c es) w := by
  induction es generalizing c with
  | nil => exact hw
  | cons p es ih => exact ih (width_deleteEdgeNat hw)

/-- A rotation-planar circuit stays rotation-planar after deleting any set of
edges. -/
theorem rotationPlanar_deleteEdges {c : ADRCircuit n} (hplanar : RotationPlanar c)
    (es : List (Nat × Nat)) : RotationPlanar (deleteEdges c es) := by
  rw [rotationPlanar_iff_genus_zero] at hplanar ⊢
  have := genus_deleteEdges_le c es
  omega

end AllenderOQ3.Internal
