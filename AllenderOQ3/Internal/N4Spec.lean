import AllenderOQ3.Incidence
import AllenderOQ3.Base
import AllenderOQ3.Internal.AbstractCircuit
import AllenderOQ3.Internal.IncidenceToolkit

set_option autoImplicit false

namespace AllenderOQ3.Internal

open AllenderOQ3

/-!
# The gate type and the circuit data of the N4 refinement

This file carries out the construction of §3 of `docs/INCIDENCE_REFINEMENT.md` on an
abstract finite gate type, in the uniform "shift register" form.

Fix a fan-in bound `F` and put `T = F + 2`.  The refined circuit has

* one *checkpoint* node `old g` for every gate `g` of the source circuit, placed on
  layer `(c.layer g + 1) * T`;
* for every gate `g` and every pair `(j, k)` of indices in `Fin (F + 1)`, one node
  `node g j k` on layer `c.layer g * T + j + 1`.

Inside the strip of a gate `g`, the slot `k = 0` is the *accumulator* and the slot
`k = i + 1` is the *rail* carrying the value of the `(j + i)`-th predecessor of `g`.
The accumulator starts as the fresh port `y_g` (a literal node) and absorbs, one per
micro-layer, the value of the rail sitting immediately next to it, while the remaining
rails shift down by one slot.  After `F` steps the accumulator has absorbed the fresh
port and all predecessors of `g`, and the checkpoint node `old g` is a unary copy of it.

Rails whose predecessor index is out of range are isolated padding nodes; they keep every
micro-layer of a strip at the same width `F + 1`, which is what makes the total width
bound `(F + 1) * W` and the size bound of §5 immediate.
-/


/-- The port-augmented semantics of a circuit: every AND/OR gate `g` receives one extra
input `y g`, combined with its old predecessors by the operation of `g`. -/
def PortAugmentedADRValuation {n : Nat} (c : ADRCircuit n)
    (x : Fin n → Bool) (y : Fin c.gateCount → Bool)
    (value : Fin c.gateCount → Bool) : Prop :=
  ∀ g, match c.kind g with
    | .literal i negated =>
        value g = if negated then !(x i) else x i
    | .andGate =>
        (value g = true ↔
          (∀ h, c.edge h g = true → value h = true) ∧ y g = true)
    | .orGate =>
        (value g = true ↔
          (∃ h, c.edge h g = true ∧ value h = true) ∨ y g = true)

/-- The gate type of the N4 refinement: old checkpoint gates and, for each old gate, a
`(F+1) × (F+1)` grid of micro-layer slots. -/
abbrev N4Gate (m F : Nat) : Type := Fin m ⊕ (Fin m × Fin (F + 1) × Fin (F + 1))

namespace N4

variable {m F : Nat}

/-- The checkpoint node of an old gate. -/
abbrev old (g : Fin m) : N4Gate m F := Sum.inl g

/-- The slot `k` of the micro-layer `j` of the strip of the old gate `g`. -/
abbrev node (g : Fin m) (j k : Fin (F + 1)) : N4Gate m F := Sum.inr (g, j, k)

end N4

variable {n : Nat}

/-- The AND/OR operation of an old gate, as a gate of the refined circuit. -/
def n4Op (c : ADRCircuit n) (g : Fin c.gateCount) : ADRGate (n + c.gateCount) :=
  match c.kind g with
  | .andGate => .andGate
  | _ => .orGate

/-- The labels of the refined circuit. -/
def n4Kind (c : ADRCircuit n) (F : Nat) :
    N4Gate c.gateCount F → ADRGate (n + c.gateCount)
  | Sum.inl g =>
      match c.kind g with
      | .literal i b => .literal (Fin.castAdd c.gateCount i) b
      | _ => .orGate
  | Sum.inr (g, j, k) =>
      if j.val = 0 ∧ k.val = 0 then .literal (Fin.natAdd n g) false
      else if k.val = 0 then n4Op c g else .orGate

/-- The layers of the refined circuit. -/
def n4Layer (c : ADRCircuit n) (F : Nat) : N4Gate c.gateCount F → Nat
  | Sum.inl g => (c.layer g + 1) * (F + 2)
  | Sum.inr (g, j, _) => c.layer g * (F + 2) + j.val + 1

/-- The wires of the refined circuit, relative to a chosen ordering `pred` of the
predecessors of each old gate. -/
def n4Edge (c : ADRCircuit n) (F : Nat) (pred : Fin c.gateCount → List (Fin c.gateCount)) :
    N4Gate c.gateCount F → N4Gate c.gateCount F → Bool
  | Sum.inl _, Sum.inl _ => false
  | Sum.inl u, Sum.inr (g, j, k) =>
      decide (j.val = 0 ∧ 1 ≤ k.val ∧ (pred g)[k.val - 1]? = some u)
  | Sum.inr (g', j', k'), Sum.inl g =>
      decide (g' = g ∧ j'.val = F ∧ k'.val = 0 ∧ (c.kind g).isComputation = true)
  | Sum.inr (g', j', k'), Sum.inr (g, j, k) =>
      decide (g' = g ∧ j.val = j'.val + 1 ∧
        ((k.val = 0 ∧ k'.val = 0) ∨
         (k.val = 0 ∧ k'.val = 1 ∧ j'.val < (pred g).length) ∨
         (1 ≤ k.val ∧ k'.val = k.val + 1 ∧ j.val + k.val - 1 < (pred g).length)))

/-- The circuit data of the N4 refinement on the abstract gate type. -/
def n4Spec (c : ADRCircuit n) (F : Nat) (pred : Fin c.gateCount → List (Fin c.gateCount)) :
    ADRSpec (n + c.gateCount) (N4Gate c.gateCount F) where
  output := Sum.inl c.output
  kind := n4Kind c F
  layer := n4Layer c F
  edge := n4Edge c F pred

/-! ## The predecessor ordering read off an incidence certificate -/

/-- The predecessors of `g`, listed in the order in which the incidence certificate of the
transition into the layer of `g` lists the incoming arcs of `g`. -/
def n4Inc (c : ADRCircuit n) (cyl : IncidenceCylinder c) (g : Fin c.gateCount) :
    List (Fin c.gateCount) :=
  if h : c.layer g = 0 then [] else
    ((cyl.transitionOrder (c.layer g - 1)).incoming ⟨g, by omega⟩).map (fun e => e.1.1)

end AllenderOQ3.Internal
