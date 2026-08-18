import AllenderOQ3.Incidence
import AllenderOQ3.Internal.FullLayerIndexing
import AllenderOQ3.Internal.TransitionMonoid
import AllenderOQ3.Internal.StateChain
import AllenderOQ3.Internal.Prune

set_option autoImplicit false
set_option linter.unusedVariables false

namespace AllenderOQ3.Internal

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)

noncomputable def layerTransMap (x : Fin n → Bool) (ell : Nat) (s : Config w) : Config w :=
  fun (j : Fin w) =>
    if h : j.val < (cert.layerOrder (ell + 1)).entries.length then
      let v : LayerVertex c (ell + 1) := (FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, h⟩
      match c.kind v.val with
      | .literal i b => if b then !(x i) else x i
      | .andGate =>
          decide (∀ u : Fin c.gateCount, c.edge u v.val = true →
            if hu : c.layer u = ell then
              let u_vert : LayerVertex c ell := ⟨u, hu⟩
              let i := FullLayerIndexing c cert ell u_vert
              if hi : i.val < w then s ⟨i.val, hi⟩ else false
            else false)
      | .orGate =>
          decide (∃ u : Fin c.gateCount, c.edge u v.val = true ∧
            if hu : c.layer u = ell then
              let u_vert : LayerVertex c ell := ⟨u, hu⟩
              let i := FullLayerIndexing c cert ell u_vert
              if hi : i.val < w then s ⟨i.val, hi⟩ else false
            else false)
    else false

noncomputable def layerTrans (x : Fin n → Bool) (ell : Nat) : TransMonoid w :=
  ofConfigMap (layerTransMap c cert x ell)

noncomputable def wordOf (x : Fin n → Bool) : List (TransMonoid w) :=
  List.map (layerTrans c cert x) (List.range (Finset.univ.sup c.layer + 1))

def isNonCrossingMap (w : Nat) (f : TransMonoid w) : Prop :=
  ∃ (n : Nat) (c : ADRCircuit n) (cert : IncidenceCylinder c) (ell : Nat) (x : Fin n → Bool),
    HMVNormal c ∧ TotalWidthAtMost c w ∧ layerTrans c cert x ell = f

def NonCrossing (w : Nat) : Submonoid (TransMonoid w) :=
  Submonoid.closure { f | isNonCrossingMap w f }

theorem layerTrans_mem_nonCrossing {n w : Nat} (c : ADRCircuit n)
    (cert : IncidenceCylinder c) (x : Fin n → Bool) (ell : Nat)
    (hN : HMVNormal c) (hW : TotalWidthAtMost c w) :
    layerTrans c cert x ell ∈ NonCrossing w :=
  Submonoid.subset_closure ⟨n, c, cert, ell, x, hN, hW, rfl⟩

/-- The full width-`w` transition monoid is non-commutative once `w ≥ 3`
(indeed once `w ≥ 1`): the two constant configuration maps absorb each other on
opposite sides.  This is the guard warning that the unrestricted transition
monoid is *not* the object to run the Barrington--Thérien argument on; only the
incidence-constrained submonoid `NonCrossing w` may be used. -/
theorem non_solvable_guard (w : Nat) (hw : 3 ≤ w) :
    ¬ (∀ g h : TransMonoid w, g * h = h * g) := by
  intro hcomm
  have h0 : 0 < w := by omega
  have h := congrArg (fun t : TransMonoid w => runTrans t (fun _ => false) ⟨0, h0⟩)
    (hcomm (ofConfigMap (fun _ _ => false)) (ofConfigMap (fun _ _ => true)))
  simp at h

end AllenderOQ3.Internal
