import AllenderOQ3.Model

/-!
# Finite incidence certificates for cylindrical layered circuits

This file deliberately avoids geometric circles and the weaker vertex-only
predicate printed in HMV.  A certificate records one cyclic word of arcs for
every transition.  Grouping that word first by tails and then by heads must
give the same word up to cyclic rotation.  This is exactly the finite datum
used by the incidence-refinement lemma in the mathematical proof.
-/

set_option autoImplicit false

namespace AllenderOQ3

abbrev LayerVertex {n : Nat} (c : ADRCircuit n) (ell : Nat) :=
  {v : Fin c.gateCount // c.layer v = ell}

abbrev TransitionArc {n : Nat} (c : ADRCircuit n) (ell : Nat) :=
  {e : Fin c.gateCount × Fin c.gateCount //
    c.edge e.1 e.2 = true ∧
    c.layer e.1 = ell ∧
    c.layer e.2 = ell + 1}

/-- A rooted representative of a finite cyclic order. -/
structure CyclicListing (alpha : Type) [DecidableEq alpha] where
  entries : List alpha
  nodup : entries.Nodup
  complete : ∀ a : alpha, a ∈ entries

/-- Two finite words represent the same cyclic word. -/
def CyclicRotation {alpha : Type} (xs ys : List alpha) : Prop :=
  ∃ p q : List alpha, xs = p ++ q ∧ ys = q ++ p

/--
The source-major and target-major descriptions of one transition have one
common cyclic arc word.  Empty vertex fibres are represented by empty lists.
-/
structure ArcOrderCertificate {n : Nat} (c : ADRCircuit n) (ell : Nat)
    (sourceOrder : CyclicListing (LayerVertex c ell))
    (targetOrder : CyclicListing (LayerVertex c (ell + 1))) where
  outgoing : LayerVertex c ell → List (TransitionArc c ell)
  incoming : LayerVertex c (ell + 1) → List (TransitionArc c ell)
  outgoing_nodup : ∀ u, (outgoing u).Nodup
  incoming_nodup : ∀ v, (incoming v).Nodup
  outgoing_exact :
    ∀ u e, e ∈ outgoing u ↔ e.1.1 = u.1
  incoming_exact :
    ∀ v e, e ∈ incoming v ↔ e.1.2 = v.1
  commonArcWord :
    CyclicRotation
      (sourceOrder.entries.flatMap outgoing)
      (targetOrder.entries.flatMap incoming)

/-- A coherent incidence order for every layer and every adjacent transition. -/
structure IncidenceCylinder {n : Nat} (c : ADRCircuit n) where
  layerOrder : ∀ ell, CyclicListing (LayerVertex c ell)
  transitionOrder : ∀ ell, ArcOrderCertificate c ell
    (layerOrder ell) (layerOrder (ell + 1))

/-- Combinatorial planarity in the rotation model used by the candidate. -/
def RotationPlanar {n : Nat} (c : ADRCircuit n) : Prop :=
  ∃ r : OrientableRotation c, rotationGenus r = 0

def ProperLayered {n : Nat} (c : ADRCircuit n) : Prop :=
  ∀ u v, c.edge u v = true → c.layer u + 1 = c.layer v

def IsGraphSource {n : Nat} (c : ADRCircuit n)
    (v : Fin c.gateCount) : Prop :=
  ∀ u, c.edge u v = false

def IsGraphSink {n : Nat} (c : ADRCircuit n)
    (v : Fin c.gateCount) : Prop :=
  ∀ u, c.edge v u = false

noncomputable def predecessorCount {n : Nat}
    (c : ADRCircuit n) (g : Fin c.gateCount) : Nat := by
  classical
  exact (Finset.univ.filter fun h => c.edge h g = true).card

/-- The fan-in-two basis used after incidence refinement. -/
def HMVNormal {n : Nat} (c : ADRCircuit n) : Prop :=
  WellFormedADR c ∧
  ∀ g, (c.kind g).isComputation = true → predecessorCount c g ≤ 2

/-- Unlike `ADRHasWidthAtMost`, this counts every node, including ports. -/
def TotalWidthAtMost {n : Nat}
    (c : ADRCircuit n) (width : Nat) : Prop :=
  ∀ ell,
    (Finset.univ.filter fun g : Fin c.gateCount =>
      c.layer g = ell).card ≤ width

end AllenderOQ3
