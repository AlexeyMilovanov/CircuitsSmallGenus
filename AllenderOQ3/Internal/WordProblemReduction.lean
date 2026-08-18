import AllenderOQ3.Internal.ACCAssembleWord
import AllenderOQ3.Internal.NonCrossingEval
import AllenderOQ3.Principles

/-!
# Reducing the quantitative cylindrical `ACC` principle to a word problem

`AllenderOQ3.QuantitativeCylindricalACCPrinciple` is the last external fact of
the audited development.  This file isolates exactly what is still missing:

* `WordProblemACC w` — for circuits of total width `w` carrying an incidence
  certificate, the predicate "the product of the layer letters equals `g`" is
  decided, for every fixed `g` of the width-`w` transition monoid, by an
  `ACC[m]` circuit of constant depth and polynomial size;
* `quantitativeCylindricalACC_of_wordProblem` — `WordProblemACC` for every width
  implies the frozen principle.

The proof is the assembly theorem `exists_acc_adrAccepts_of_word` together with
the arithmetic needed to absorb the width-dependent constants into the size
exponent.  Nothing about the frozen statement is changed or weakened: the
implication is proved outright, so the remaining mathematical content of the
external fact is precisely `WordProblemACC`.

The degenerate width `w = 0` is discharged unconditionally
(`wordProblemACC_zero`): a circuit always has an output gate, so its layer is
occupied and `TotalWidthAtMost c 0` is contradictory.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- **The remaining obligation.**  For every incidence-certified circuit of total
width `w` and every element `g` of the width-`w` transition monoid, the predicate
"the product of the layer letters of the circuit equals `g`" is decided by an
`ACC[modulus]` circuit of depth at most `depth` and size at most
`(gateCount + 1) ^ exponent`, with `modulus`, `depth` and `exponent` depending
only on `w`. -/
def WordProblemACC (w : Nat) : Prop :=
  ∃ modulus depth exponent : Nat,
    2 ≤ modulus ∧
      ∀ {n : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c),
        HMVNormal c →
        TotalWidthAtMost c w →
        ∀ g : TransMonoid w,
          ∃ a : ACCCircuit n modulus,
            WellFormedACC a ∧
            (∀ q, a.layer q ≤ depth) ∧
            a.gateCount ≤ (c.gateCount + 1) ^ exponent ∧
            (∀ x, ACCAccepts a x ↔ outputWord c cert x w = g)

/-- Width zero is degenerate: the output gate occupies its own layer, so
`TotalWidthAtMost c 0` is contradictory and the obligation holds vacuously. -/
theorem wordProblemACC_zero : WordProblemACC 0 := by
  refine ⟨2, 0, 0, le_refl 2, ?_⟩
  intro n c _ _ hW _
  exact (totalWidthAtMost_zero_elim c hW).elim

/-- A constant is absorbed into the exponent of a base at least two. -/
theorem const_mul_pow_le_pow {P C e : Nat} (hP : 2 ≤ P) :
    C * P ^ e ≤ P ^ (e + C) := by
  have h1 : C ≤ 2 ^ C := le_of_lt Nat.lt_two_pow_self
  have h2 : (2 : Nat) ^ C ≤ P ^ C := Nat.pow_le_pow_left hP C
  calc C * P ^ e ≤ P ^ C * P ^ e := Nat.mul_le_mul_right _ (le_trans h1 h2)
    _ = P ^ (e + C) := by rw [← pow_add, Nat.add_comm]

/-- The size bound produced by the assembly step is a constant multiple of the
size of the word recogniser. -/
theorem assemble_size_bound {K A S : Nat} (hS : 1 ≤ S) :
    K * (S + A + 2) + 1 ≤ (K * (A + 3) + 1) * S := by
  have h1 : K * (S + A + 2) + 1 = K * S + (K * (A + 2) + 1) := by ring
  have h2 : (K * (A + 3) + 1) * S = K * S + (K * (A + 2) + 1) * S := by ring
  have h3 : K * (A + 2) + 1 ≤ (K * (A + 2) + 1) * S := Nat.le_mul_of_pos_right _ hS
  omega

/-- **The quantitative cylindrical `ACC` principle follows from the word problem
of the transition monoid.** -/
theorem quantitativeCylindricalACC_of_wordProblem
    (H : ∀ w : Nat, WordProblemACC w) : QuantitativeCylindricalACCPrinciple := by
  intro width
  obtain ⟨M, D, e, hM, hword⟩ := H width
  classical
  refine ⟨M, max D 2 + 2,
    e + (Fintype.card (Config width × TransMonoid width) *
      (2 * width + 2 ^ width + 1 + 3) + 1), hM, ?_⟩
  intro n c hN hW hcyl
  obtain ⟨cert⟩ := hcyl
  obtain ⟨a, hwf, hlay, hsize, hacc⟩ :=
    exists_acc_adrAccepts_of_word (m := M) (D := D) (S := (c.gateCount + 1) ^ e)
      c cert hN.1 hW (fun g => hword c cert hN hW g)
  refine ⟨a, hwf, hlay, ?_, hacc⟩
  -- absorb the width-dependent constants into the size exponent
  have hP : 2 ≤ c.gateCount + 1 := by
    have := c.output.isLt
    omega
  have hpow : 1 ≤ (c.gateCount + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  exact le_trans (le_trans hsize (assemble_size_bound hpow)) (const_mul_pow_le_pow hP)

end AllenderOQ3.Internal
