import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Relation

/-!
# Trusted Comparator challenge: Allender OQ3

This file is the complete human-trusted Lean statement for the
resolution of Allender's Open Question 3. It deliberately imports only
Mathlib modules -- the explicit ones listed above, and nothing from this
project. The definitions below are copied verbatim from the project interface
(AllenderOQ3/Model.lean), whose import header is identical.

The proof is intentionally a `sorry`: Comparator checks that `Solution.lean`
proves this exact statement, with these exact definitions, using only the
permitted axioms in `config.json`.
-/

abbrev BinaryLanguage := ∀ n : Nat, (Fin n → Bool) → Prop

inductive ADRGate (inputCount : Nat) where
  | literal (index : Fin inputCount) (negated : Bool)
  | andGate
  | orGate
  deriving DecidableEq

def ADRGate.isComputation {inputCount : Nat} : ADRGate inputCount → Bool
  | .literal _ _ => false
  | .andGate => true
  | .orGate => true

structure ADRCircuit (inputCount : Nat) where
  gateCount : Nat
  output : Fin gateCount
  kind : Fin gateCount → ADRGate inputCount
  layer : Fin gateCount → Nat
  edge : Fin gateCount → Fin gateCount → Bool

def WellFormedADR {n : Nat} (c : ADRCircuit n) : Prop :=
  (∀ u v, c.edge u v = true → c.layer u + 1 = c.layer v) ∧
  (∀ g, (∃ (i : Fin n) (b : Bool), c.kind g = .literal i b) →
    ∀ h, c.edge h g = false)

def ADRHasWidthAtMost {n : Nat} (c : ADRCircuit n) (w : Nat) : Prop :=
  ∀ ell : Nat,
    (Finset.univ.filter (fun g : Fin c.gateCount =>
      c.layer g = ell ∧ (c.kind g).isComputation = true)).card ≤ w

def ADRValuation {n : Nat} (c : ADRCircuit n) (x : Fin n → Bool)
    (value : Fin c.gateCount → Bool) : Prop :=
  ∀ g, match c.kind g with
    | .literal i negated =>
        value g = if negated then !(x i) else x i
    | .andGate =>
        (value g = true ↔
          ∀ h, c.edge h g = true → value h = true)
    | .orGate =>
        (value g = true ↔
          ∃ h, c.edge h g = true ∧ value h = true)

def ADRAccepts {n : Nat} (c : ADRCircuit n)
    (x : Fin n → Bool) : Prop :=
  ∃ value : Fin c.gateCount → Bool,
    ADRValuation c x value ∧ value c.output = true

def ADRFamilyDecides (family : ∀ n : Nat, ADRCircuit n)
    (L : BinaryLanguage) : Prop :=
  ∀ (n : Nat) (x : Fin n → Bool),
    ADRAccepts (family n) x ↔ L n x

def UnderlyingAdj {n : Nat} (c : ADRCircuit n)
    (u v : Fin c.gateCount) : Prop :=
  (c.edge u v = true ∨ c.edge v u = true) ∧ u ≠ v

instance instDecidableUnderlyingAdj {n : Nat} (c : ADRCircuit n)
    (u v : Fin c.gateCount) : Decidable (UnderlyingAdj c u v) := by
  unfold UnderlyingAdj
  infer_instance

abbrev CircuitDart {n : Nat} (c : ADRCircuit n) :=
  {p : Fin c.gateCount × Fin c.gateCount //
    UnderlyingAdj c p.1 p.2}

def CircuitDart.source {n : Nat} {c : ADRCircuit n}
    (d : CircuitDart c) : Fin c.gateCount :=
  d.1.1

def CircuitDart.target {n : Nat} {c : ADRCircuit n}
    (d : CircuitDart c) : Fin c.gateCount :=
  d.1.2

def dartReverse {n : Nat} (c : ADRCircuit n) :
    CircuitDart c ≃ CircuitDart c where
  toFun d :=
    ⟨(d.target, d.source),
      ⟨d.property.1.elim Or.inr Or.inl,
        Ne.symm d.property.2⟩⟩
  invFun d :=
    ⟨(d.target, d.source),
      ⟨d.property.1.elim Or.inr Or.inl,
        Ne.symm d.property.2⟩⟩
  left_inv d := by
    apply Subtype.ext
    simp [CircuitDart.source, CircuitDart.target]
  right_inv d := by
    apply Subtype.ext
    simp [CircuitDart.source, CircuitDart.target]

structure OrientableRotation {n : Nat} (c : ADRCircuit n) where
  rotation : Equiv.Perm (CircuitDart c)
  preservesSource : ∀ d, (rotation d).source = d.source
  cyclicAtVertex : ∀ d e, d.source = e.source →
    ∃ k : Nat, (rotation ^ k) d = e

noncomputable def permCycleCount {α : Type}
    [Fintype α] [DecidableEq α] (p : Equiv.Perm α) : Nat := by
  classical
  exact (Finset.univ.filter (fun x =>
    ∀ y, (∃ k : Nat, (p ^ k) x = y) →
      (Fintype.equivFin α x).val ≤
        (Fintype.equivFin α y).val)).card

def VertexReachable {n : Nat} (c : ADRCircuit n)
    (u v : Fin c.gateCount) : Prop :=
  Relation.ReflTransGen (UnderlyingAdj c) u v

noncomputable def componentCount {n : Nat}
    (c : ADRCircuit n) : Nat := by
  classical
  exact (Finset.univ.filter (fun u =>
    ∀ v, VertexReachable c u v → u.val ≤ v.val)).card

noncomputable def isolatedVertexCount {n : Nat}
    (c : ADRCircuit n) : Nat := by
  classical
  exact (Finset.univ.filter (fun u =>
    ∀ v, ¬ UnderlyingAdj c u v)).card

noncomputable def underlyingEdgeCount {n : Nat}
    (c : ADRCircuit n) : Nat := by
  classical
  exact Finset.univ.sum (fun u =>
    (Finset.univ.filter (fun v =>
      u.val < v.val ∧ UnderlyingAdj c u v)).card)

def facePermutation {n : Nat} {c : ADRCircuit n}
    (r : OrientableRotation c) : Equiv.Perm (CircuitDart c) :=
  (dartReverse c).trans r.rotation

noncomputable def rotationGenus {n : Nat} {c : ADRCircuit n}
    (r : OrientableRotation c) : Nat :=
  let faces :=
    permCycleCount (facePermutation r) + isolatedVertexCount c
  (2 * componentCount c + underlyingEdgeCount c -
    c.gateCount - faces) / 2

noncomputable def orientableCircuitGenus {n : Nat}
    (c : ADRCircuit n) : Nat :=
  sInf {g : Nat |
    ∃ r : OrientableRotation c, rotationGenus r = g}

inductive ACCGate (inputCount modulus : Nat) where
  | literal (index : Fin inputCount) (negated : Bool)
  | andGate
  | orGate
  | notGate
  | modGate
  deriving DecidableEq

structure ACCCircuit (inputCount modulus : Nat) where
  gateCount : Nat
  output : Fin gateCount
  kind : Fin gateCount → ACCGate inputCount modulus
  layer : Fin gateCount → Nat
  edge : Fin gateCount → Fin gateCount → Bool

def WellFormedACC {n m : Nat} (c : ACCCircuit n m) : Prop :=
  (∀ u v, c.edge u v = true → c.layer u < c.layer v) ∧
  (∀ g, c.layer g = 0 ↔
    ∃ (i : Fin n) (b : Bool), c.kind g = .literal i b) ∧
  (∀ g, c.kind g = .notGate →
    ∃! h, c.edge h g = true)

def ACCValuation {n m : Nat} (c : ACCCircuit n m)
    (x : Fin n → Bool) (value : Fin c.gateCount → Bool) : Prop :=
  ∀ g, match c.kind g with
    | .literal i negated =>
        value g = if negated then !(x i) else x i
    | .andGate =>
        (value g = true ↔
          ∀ h, c.edge h g = true → value h = true)
    | .orGate =>
        (value g = true ↔
          ∃ h, c.edge h g = true ∧ value h = true)
    | .notGate =>
        (value g = true ↔
          ∃ h, c.edge h g = true ∧ value h = false)
    | .modGate =>
        (value g = true ↔
          (Finset.univ.filter (fun h =>
            c.edge h g = true ∧ value h = true)).card % m = 0)

def ACCAccepts {n m : Nat} (c : ACCCircuit n m)
    (x : Fin n → Bool) : Prop :=
  ∃ value : Fin c.gateCount → Bool,
    ACCValuation c x value ∧ value c.output = true

def ACCFamilyDecides {m : Nat}
    (family : ∀ n : Nat, ACCCircuit n m)
    (L : BinaryLanguage) : Prop :=
  ∀ (n : Nat) (x : Fin n → Bool),
    ACCAccepts (family n) x ↔ L n x

def InNonuniformACC0 (L : BinaryLanguage) : Prop :=
  ∃ (m depth exponent : Nat)
      (family : ∀ n : Nat, ACCCircuit n m),
    2 ≤ m ∧
    (∀ n, WellFormedACC (family n)) ∧
    (∀ n g, (family n).layer g ≤ depth) ∧
    (∀ n, (family n).gateCount ≤ (n + 1) ^ exponent) ∧
    ACCFamilyDecides family L

def AllenderOQ3Hypothesis (L : BinaryLanguage) : Prop :=
  ∃ (width sizeExponent logExponent factor threshold : Nat)
      (family : ∀ n : Nat, ADRCircuit n),
    0 < width ∧ 0 < factor ∧
    (∀ n, WellFormedADR (family n)) ∧
    (∀ n, ADRHasWidthAtMost (family n) width) ∧
    (∀ n, (family n).gateCount ≤ (n + 1) ^ sizeExponent) ∧
    (∀ n, threshold ≤ n →
      orientableCircuitGenus (family n) ≤
        factor * (Nat.log2 (n + 1)) ^ logExponent) ∧
    ADRFamilyDecides family L

def AllenderOQ3Statement : Prop :=
    ∀ L : BinaryLanguage,
      AllenderOQ3Hypothesis L → InNonuniformACC0 L

/-- The trusted Allender OQ3 challenge. -/
theorem allender_oq3_challenge : AllenderOQ3Statement := by
  sorry
