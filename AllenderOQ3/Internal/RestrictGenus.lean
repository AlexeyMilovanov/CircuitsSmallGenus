import AllenderOQ3.Internal.Surgery
import AllenderOQ3.Internal.BlockGenus
import AllenderOQ3.Internal.GenusBudget
import AllenderOQ3.Internal.SetOutput

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# Genus monotonicity under restriction

Restricting a circuit to a predecessor-closed subfamily of its gates never increases the
rotation genus: first mask away every edge with an endpoint outside the subfamily (this
does not increase the genus, `genus_maskCircuit_le`), and then delete the — now isolated —
outside gates (this does not change the genus, `genus_restrict_isolated`).

Consequences: a subcircuit of a rotation-planar circuit is rotation planar; in particular
the pruned circuit and the ancestor cone of a gate are rotation planar.
-/

variable {n : Nat}

open Classical in
/-- The mask keeping exactly the edges with both endpoints in the image of `f`. -/
noncomputable def imageMask {c : ADRCircuit n} {m : Nat} (f : SubEmbedding c m) :
    Fin c.gateCount → Fin c.gateCount → Bool :=
  fun a b => decide ((∃ u, f.toFun u = a) ∧ (∃ u, f.toFun u = b))

open Classical in
/-- `f` is still predecessor closed in the masked circuit. -/
noncomputable def maskedSubEmbedding {c : ADRCircuit n} {m : Nat} (f : SubEmbedding c m) :
    SubEmbedding (maskCircuit c (imageMask f)) m where
  toFun := f.toFun
  inj := f.inj
  predClosed := by
    intro a u hedge
    rw [maskCircuit_edge] at hedge
    by_cases hk : imageMask f u (f.toFun a) = true
    · have := (of_decide_eq_true hk).1
      exact this
    · rw [if_neg hk] at hedge
      exact absurd hedge (by simp)

open Classical in
theorem restrict_maskCircuit_imageMask {c : ADRCircuit n} {m : Nat} (f : SubEmbedding c m)
    (out : Fin m) :
    restrict (maskCircuit c (imageMask f)) (maskedSubEmbedding f) out = restrict c f out := by
  have hedge : ∀ a b : Fin m, (maskCircuit c (imageMask f)).edge (f.toFun a) (f.toFun b)
      = c.edge (f.toFun a) (f.toFun b) := by
    intro a b
    rw [maskCircuit_edge, if_pos]
    simp [imageMask]
  unfold restrict
  simp only [ADRCircuit.mk.injEq, heq_eq_eq, true_and]
  exact ⟨rfl, rfl, funext fun a => funext fun b => hedge a b⟩

/-- **Restriction never increases the genus.** -/
theorem genus_restrict_le {c : ADRCircuit n} {m : Nat} (f : SubEmbedding c m) (out : Fin m) :
    orientableCircuitGenus (restrict c f out) ≤ orientableCircuitGenus c := by
  classical
  have hiso : ∀ g : Fin (maskCircuit c (imageMask f)).gateCount,
      (∀ a, (maskedSubEmbedding f).toFun a ≠ g) →
      ∀ h, (maskCircuit c (imageMask f)).edge g h = false ∧
        (maskCircuit c (imageMask f)).edge h g = false := by
    intro g hg h
    have hnot : ¬ (∃ u, f.toFun u = g) := by
      rintro ⟨u, hu⟩
      exact hg u hu
    constructor
    · rw [maskCircuit_edge, if_neg]
      intro hk
      exact hnot (of_decide_eq_true hk).1
    · rw [maskCircuit_edge, if_neg]
      intro hk
      exact hnot (of_decide_eq_true hk).2
  have h1 : orientableCircuitGenus
      (restrict (maskCircuit c (imageMask f)) (maskedSubEmbedding f) out)
      = orientableCircuitGenus (maskCircuit c (imageMask f)) :=
    genus_restrict_isolated _ _ _ hiso
  rw [restrict_maskCircuit_imageMask] at h1
  rw [h1]
  exact genus_maskCircuit_le c _

/-- **A subcircuit of a rotation-planar circuit is rotation planar.** -/
theorem rotationPlanar_restrict {c : ADRCircuit n} (hplanar : RotationPlanar c) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) :
    RotationPlanar (restrict c f out) := by
  rw [rotationPlanar_iff_genus_zero] at hplanar ⊢
  have := genus_restrict_le f out
  omega

/-- Pruning preserves rotation planarity. -/
theorem rotationPlanar_prunedCircuit {c : ADRCircuit n} (hplanar : RotationPlanar c) :
    RotationPlanar (prunedCircuit c) :=
  rotationPlanar_restrict hplanar _ _

/-- The ancestor cone of a gate of a rotation-planar circuit is rotation planar. -/
theorem rotationPlanar_ancestorCone {c : ADRCircuit n} (hplanar : RotationPlanar c)
    (h : Fin c.gateCount) : RotationPlanar (ancestorCone c h) :=
  rotationPlanar_prunedCircuit (rotationPlanar_setOutput hplanar h)

/-! ## The ancestor cone as an input to the width induction -/

/-- The ancestor cone of a gate is well formed. -/
theorem wellFormedADR_ancestorCone {c : ADRCircuit n} (hc : WellFormedADR c)
    (h : Fin c.gateCount) : WellFormedADR (ancestorCone c h) :=
  wellFormed_prunedCircuit (wellFormedADR_setOutput hc h)

/-- The ancestor cone inherits the computation-width bound. -/
theorem width_ancestorCone {c : ADRCircuit n} {w : Nat} (hw : ADRHasWidthAtMost c w)
    (h : Fin c.gateCount) : ADRHasWidthAtMost (ancestorCone c h) w :=
  width_prunedCircuit hw

/-- The ancestor cone has at most as many gates as the circuit. -/
theorem gateCount_ancestorCone_le (c : ADRCircuit n) (h : Fin c.gateCount) :
    (ancestorCone c h).gateCount ≤ c.gateCount :=
  gateCount_prunedCircuit_le (setOutput c h)

/-- **The ancestor cone computes the value of its apex gate.** -/
theorem adrAccepts_ancestorCone {c : ADRCircuit n} (hc : WellFormedADR c)
    (h : Fin c.gateCount) (x : Fin n → Bool) :
    ADRAccepts (ancestorCone c h) x ↔ evalADR c hc x h = true := by
  rw [ancestorCone, adrAccepts_prunedCircuit (wellFormedADR_setOutput hc h) x,
    adrAccepts_iff (wellFormedADR_setOutput hc h) x, evalADR_setOutput hc h x]
  exact Iff.rfl

end AllenderOQ3.Internal
