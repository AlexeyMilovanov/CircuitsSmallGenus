import AllenderOQ3.Internal.ACCTruthTable
import AllenderOQ3.Internal.ACCBuild

/-!
# Predicates depending on few input variables are small constant-depth `ACC`

The `ACC` simulation of a bounded-width circuit needs, for each layer and each
pair of fixed configurations, a *small* `ACC` circuit deciding whether the layer
transition maps one configuration to the other.  Such a predicate depends on the
input `x` only through at most `W` of its coordinates (one per layer slot), so it
is decided by a depth-`2` truth-table circuit of size depending only on `W`.

* `exists_acc_of_factors` — a predicate that factors through `k` coordinates is
  computed by a depth-`2` `ACC[m]` circuit of size `2 * k + 2 ^ k + 1`.
* `exists_acc_of_slotwise` — the form used for layer transitions: a `Fin W`-tuple
  of Booleans, each of which is either a (possibly negated) input literal or a
  constant, is compared to a fixed target tuple.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- The truth-table circuit has depth at most `2`. -/
theorem accTruthTable_layer_le_fewVars (k m : Nat) (P : (Fin k → Bool) → Prop)
    (dec : ∀ y, Decidable (P y)) (g : Fin (accTruthTable k m P dec).gateCount) :
    (accTruthTable k m P dec).layer g ≤ 2 := by
  cases k with
  | zero =>
      simp only [accTruthTable]
      omega
  | succ k' =>
      simp only [accTruthTable]
      split_ifs <;> omega

/-- The truth-table circuit has size at most `2 * k + 2 ^ k + 1`. -/
theorem accTruthTable_gateCount_le_fewVars (k m : Nat) (P : (Fin k → Bool) → Prop)
    (dec : ∀ y, Decidable (P y)) :
    (accTruthTable k m P dec).gateCount ≤ 2 * k + 2 ^ k + 1 := by
  cases k with
  | zero => simp [accTruthTable_gateCount_zero]
  | succ k' => rw [accTruthTable_gateCount_succ]

/-- **A predicate factoring through `k` coordinates is small constant-depth `ACC`.**
If `Q x` depends on `x` only through the `k` coordinates selected by `f`, then
`Q` is decided by an `ACC[m]` circuit of depth at most `2` and size at most
`2 * k + 2 ^ k + 1`. -/
theorem exists_acc_of_factors {n k m : Nat} (f : Fin k → Fin n)
    (P : (Fin k → Bool) → Prop) (dec : ∀ y, Decidable (P y))
    (Q : (Fin n → Bool) → Prop)
    (hQ : ∀ x : Fin n → Bool, Q x ↔ P (fun j => x (f j))) :
    ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ g, a.layer g ≤ 2) ∧
      a.gateCount ≤ 2 * k + 2 ^ k + 1 ∧ ∀ x, ACCAccepts a x ↔ Q x := by
  refine ⟨accRelabel (accTruthTable k m P dec) f,
    wellFormedACC_accRelabel (wellFormedACC_accTruthTable k m P dec) f,
    accRelabel_layer_le (accTruthTable_layer_le_fewVars k m P dec) f,
    accTruthTable_gateCount_le_fewVars k m P dec, fun x => ?_⟩
  rw [accAccepts_accRelabel (wellFormedACC_accTruthTable k m P dec) f x,
    accAccepts_accTruthTable]
  exact (hQ x).symm

/-- **Slotwise comparison of a tuple against a fixed target.**  Suppose each
coordinate `F x j` of a `Fin W`-tuple is either a (possibly negated) input
literal or a constant, uniformly in `x`.  Then the predicate `F x = t` is decided
by an `ACC[m]` circuit of depth at most `2` and size at most `2 * W + 2 ^ W + 1`,
independently of the number `n` of input variables. -/
theorem exists_acc_of_slotwise {n W m : Nat}
    (F : (Fin n → Bool) → Fin W → Bool) (t : Fin W → Bool)
    (hF : ∀ j : Fin W,
      (∃ (idx : Fin n) (neg : Bool), ∀ x, F x j = if neg then !(x idx) else x idx) ∨
      (∃ b : Bool, ∀ x, F x j = b)) :
    ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ g, a.layer g ≤ 2) ∧
      a.gateCount ≤ 2 * W + 2 ^ W + 1 ∧ ∀ x, ACCAccepts a x ↔ F x = t := by
  classical
  cases n with
  | zero =>
      -- No input variables: the predicate is constant.
      have hx : ∀ x : Fin 0 → Bool, x = fun i : Fin 0 => i.elim0 :=
        fun x => funext fun i => i.elim0
      refine ⟨accTruthTable 0 m (fun _ => F (fun i : Fin 0 => i.elim0) = t)
          (fun _ => inferInstance),
        wellFormedACC_accTruthTable _ _ _ _,
        accTruthTable_layer_le_fewVars _ _ _ _, ?_, fun x => ?_⟩
      · exact le_trans (accTruthTable_gateCount_le_fewVars 0 m _ _) (by
          have : (1 : Nat) ≤ 2 ^ W := Nat.one_le_two_pow
          omega)
      · rw [accAccepts_accTruthTable]
        rw [hx x]
  | succ n' =>
      -- Choose, for every slot, either its literal description or its constant value.
      let f : Fin W → Fin (n' + 1) := fun j =>
        if h : ∃ (idx : Fin (n' + 1)) (neg : Bool),
            ∀ x, F x j = if neg then !(x idx) else x idx then
          h.choose
        else ⟨0, Nat.succ_pos n'⟩
      let P : (Fin W → Bool) → Prop := fun y => ∀ j : Fin W,
        (if h : ∃ (idx : Fin (n' + 1)) (neg : Bool),
            ∀ x, F x j = if neg then !(x idx) else x idx then
          (if h.choose_spec.choose then !(y j) else y j)
         else F (fun _ => false) j) = t j
      refine exists_acc_of_factors f P (fun _ => inferInstance) (fun x => F x = t) ?_
      intro x
      change F x = t ↔ P (fun j => x (f j))
      rw [funext_iff]
      refine forall_congr' fun j => ?_
      by_cases h : ∃ (idx : Fin (n' + 1)) (neg : Bool),
          ∀ x, F x j = if neg then !(x idx) else x idx
      · have hspec := h.choose_spec.choose_spec
        simp only [f, dif_pos h]
        rw [hspec x]
      · have hconst : ∃ b : Bool, ∀ x, F x j = b := (hF j).resolve_left h
        obtain ⟨b, hb⟩ := hconst
        simp only [dif_neg h]
        rw [hb x, hb (fun _ => false)]

end AllenderOQ3.Internal
