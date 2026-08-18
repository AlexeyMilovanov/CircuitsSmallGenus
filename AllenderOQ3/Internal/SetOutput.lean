import AllenderOQ3.Internal.Prune
import AllenderOQ3.Internal.Semantics

set_option autoImplicit false

namespace AllenderOQ3.Internal

def setOutput {n : Nat} (c : ADRCircuit n) (h : Fin c.gateCount) : ADRCircuit n :=
  { c with output := h }

@[simp] theorem setOutput_gateCount {n : Nat} (c : ADRCircuit n) (h : Fin c.gateCount) :
    (setOutput c h).gateCount = c.gateCount := rfl

@[simp] theorem setOutput_edge {n : Nat} (c : ADRCircuit n) (h : Fin c.gateCount) (u v) :
    (setOutput c h).edge u v = c.edge u v := rfl

@[simp] theorem setOutput_layer {n : Nat} (c : ADRCircuit n) (h : Fin c.gateCount) (g) :
    (setOutput c h).layer g = c.layer g := rfl

@[simp] theorem setOutput_kind {n : Nat} (c : ADRCircuit n) (h : Fin c.gateCount) (g) :
    (setOutput c h).kind g = c.kind g := rfl

theorem wellFormedADR_setOutput {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (h : Fin c.gateCount) : WellFormedADR (setOutput c h) := by
  constructor
  · intro u v hedge
    exact hc.1 u v hedge
  · intro g hkind v
    exact hc.2 g hkind v

theorem adrValuation_setOutput {n : Nat} {c : ADRCircuit n}
    (x : Fin n → Bool) (value : Fin c.gateCount → Bool) (h : Fin c.gateCount) :
    ADRValuation (setOutput c h) x value ↔ ADRValuation c x value := by
  rfl

theorem evalADR_setOutput {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    (h : Fin c.gateCount) (x : Fin n → Bool) :
    evalADR (setOutput c h) (wellFormedADR_setOutput hc h) x = evalADR c hc x := by
  have H1 := Classical.choose_spec (adrValuation_exists (setOutput c h) (wellFormedADR_setOutput hc h) x)
  have H2 := Classical.choose_spec (adrValuation_exists c hc x)
  have H1' : ADRValuation c x (evalADR (setOutput c h) (wellFormedADR_setOutput hc h) x) := by
    exact (adrValuation_setOutput x _ h).mp H1
  exact adrValuation_unique hc H1' H2

theorem underlyingAdj_setOutput {n : Nat} {c : ADRCircuit n} (h : Fin c.gateCount) (u v : Fin c.gateCount) :
    UnderlyingAdj (setOutput c h) u v ↔ UnderlyingAdj c u v := by rfl

def orientableRotation_setOutput {n : Nat} {c : ADRCircuit n}
    (r : OrientableRotation c) (h : Fin c.gateCount) :
    OrientableRotation (setOutput c h) where
  rotation := r.rotation
  preservesSource := r.preservesSource
  cyclicAtVertex := r.cyclicAtVertex

theorem rotationGenus_setOutput {n : Nat} {c : ADRCircuit n} (r : OrientableRotation c) (h : Fin c.gateCount) :
    rotationGenus (orientableRotation_setOutput r h) = rotationGenus r := by
  rfl

theorem rotationPlanar_setOutput {n : Nat} {c : ADRCircuit n}
    (hplanar : RotationPlanar c) (h : Fin c.gateCount) :
    RotationPlanar (setOutput c h) := by
  rcases hplanar with ⟨r, hr⟩
  use orientableRotation_setOutput r h
  rw [rotationGenus_setOutput]
  exact hr

/-- The ancestor cone of a gate `h` can be extracted by changing the output to `h` and pruning. -/
noncomputable def ancestorCone {n : Nat} (c : ADRCircuit n) (h : Fin c.gateCount) : ADRCircuit n :=
  prunedCircuit (setOutput c h)

end AllenderOQ3.Internal
