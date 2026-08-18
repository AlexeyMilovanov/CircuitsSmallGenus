import AllenderOQ3.Incidence
import AllenderOQ3.Internal.Semantics

/-!
# Predecessor-closed subcircuits

A `SubEmbedding` picks out an injective family of gates that is closed under
taking predecessors.  Restricting a circuit to such a family preserves
well-formedness, does not increase the width, and — crucially — does not change
the value computed at any retained gate.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- An injective, predecessor-closed selection of `m` gates of `c`. -/
structure SubEmbedding {n : Nat} (c : ADRCircuit n) (m : Nat) where
  toFun : Fin m → Fin c.gateCount
  inj : Function.Injective toFun
  predClosed : ∀ (a : Fin m) (u : Fin c.gateCount),
    c.edge u (toFun a) = true → ∃ b, toFun b = u

/-- The subcircuit induced by a predecessor-closed embedding. -/
def restrict {n : Nat} (c : ADRCircuit n) {m : Nat} (f : SubEmbedding c m)
    (out : Fin m) : ADRCircuit n where
  gateCount := m
  output := out
  kind := fun a => c.kind (f.toFun a)
  layer := fun a => c.layer (f.toFun a)
  edge := fun a b => c.edge (f.toFun a) (f.toFun b)

@[simp] theorem restrict_kind {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) (a : Fin m) :
    (restrict c f out).kind a = c.kind (f.toFun a) := rfl

@[simp] theorem restrict_layer {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) (a : Fin m) :
    (restrict c f out).layer a = c.layer (f.toFun a) := rfl

@[simp] theorem restrict_edge {n : Nat} (c : ADRCircuit n) {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) (a b : Fin m) :
    (restrict c f out).edge a b = c.edge (f.toFun a) (f.toFun b) := rfl

theorem wellFormed_restrict {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {m : Nat} (f : SubEmbedding c m) (out : Fin m) :
    WellFormedADR (restrict c f out) := by
  refine ⟨?_, ?_⟩
  · intro u v h
    exact hc.1 _ _ h
  · intro g hg h
    exact hc.2 _ hg _

/-- Restriction to a predecessor-closed subfamily does not change any value. -/
theorem eval_restrict {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {m : Nat} (f : SubEmbedding c m) (out : Fin m) (x : Fin n → Bool)
    (a : Fin m) :
    evalADR (restrict c f out) (wellFormed_restrict hc f out) x a
      = evalADR c hc x (f.toFun a) := by
  have hval : ADRValuation (restrict c f out) x
      (fun b => evalADR c hc x (f.toFun b)) := by
    intro g
    have hg := (adrValuation_iff_eq_evalADR (c := c) hc (v := evalADR c hc x)).mpr rfl
      (f.toFun g)
    change match c.kind (f.toFun g) with
      | .literal i negated => _
      | .andGate => _
      | .orGate => _
    cases hk : c.kind (f.toFun g) with
    | literal i b =>
        rw [hk] at hg
        simpa using hg
    | andGate =>
        rw [hk] at hg
        simp only
        constructor
        · intro h1 b hb
          exact hg.mp h1 _ hb
        · intro h1
          refine hg.mpr ?_
          intro u hu
          obtain ⟨b, rfl⟩ := f.predClosed g u hu
          exact h1 b hu
    | orGate =>
        rw [hk] at hg
        simp only
        constructor
        · intro h1
          obtain ⟨u, hu, hvu⟩ := hg.mp h1
          obtain ⟨b, rfl⟩ := f.predClosed g u hu
          exact ⟨b, hu, hvu⟩
        · intro h1
          obtain ⟨b, hb, hvb⟩ := h1
          exact hg.mpr ⟨f.toFun b, hb, hvb⟩
  have := (adrValuation_iff_eq_evalADR (wellFormed_restrict hc f out)).mp hval
  exact congrFun this.symm a

/-- Restriction does not increase the number of gates in any layer. -/
theorem totalWidth_restrict {n : Nat} {c : ADRCircuit n} {m : Nat}
    (f : SubEmbedding c m) (out : Fin m) {w : Nat}
    (hw : AllenderOQ3.TotalWidthAtMost c w) :
    AllenderOQ3.TotalWidthAtMost (restrict c f out) w := by
  intro ell
  refine le_trans ?_ (hw ell)
  refine Finset.card_le_card_of_injOn f.toFun ?_ (Function.Injective.injOn f.inj)
  intro a ha
  have ha' : c.layer (f.toFun a) = ell := by simpa using ha
  simpa using ha'

/-- Acceptance of a restricted circuit is the value of the original circuit at
the chosen output gate. -/
theorem adrAccepts_restrict {n : Nat} {c : ADRCircuit n} (hc : WellFormedADR c)
    {m : Nat} (f : SubEmbedding c m) (out : Fin m) (x : Fin n → Bool) :
    ADRAccepts (restrict c f out) x ↔ evalADR c hc x (f.toFun out) = true := by
  rw [adrAccepts_iff (wellFormed_restrict hc f out) x]
  have hout : (restrict c f out).output = out := rfl
  rw [hout, eval_restrict hc f out x out]

end AllenderOQ3.Internal
