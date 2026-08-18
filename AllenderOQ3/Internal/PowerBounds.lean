import Mathlib.Tactic

/-!
# Crude polynomial bounds by powers of a base at least two

The size bookkeeping of the constant-depth circuit constructions is always of
the same shape: an expression built out of the size parameter, the length of the
window and a handful of constants depending only on the fixed finite monoid has
to be bounded by `(size + len + 2) ^ exponent` for a *fixed* exponent.

Because the base `S` is at least two, every constant `C` is itself bounded by
`S ^ C`, so such an expression can be bounded structurally: sums, products and
powers of bounded quantities are bounded with the exponents added.  The four
lemmas below are exactly those structural steps, and they let a size bound be
assembled without ever tracking a multiplicative constant.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/-- Monotonicity of `S ^ ·` for `2 ≤ S`. -/
theorem pow_bnd_mono {S a b : Nat} (hS : 2 ≤ S) (hab : a ≤ b) : S ^ a ≤ S ^ b :=
  Nat.pow_le_pow_right (by omega) hab

/-- **A constant is bounded by the base to that constant.** -/
theorem pow_bnd_const {S : Nat} (hS : 2 ≤ S) (C : Nat) : C ≤ S ^ C :=
  le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hS C)

/-- **A sum of bounded quantities is bounded**, with one extra unit of exponent. -/
theorem pow_bnd_add {S X Y a b : Nat} (hS : 2 ≤ S) (hX : X ≤ S ^ a) (hY : Y ≤ S ^ b) :
    X + Y ≤ S ^ (a + b + 1) := by
  have h1 : X + Y ≤ S ^ a + S ^ b := Nat.add_le_add hX hY
  have h2 : S ^ a + S ^ b ≤ S ^ (a + b) + S ^ (a + b) :=
    Nat.add_le_add (pow_bnd_mono hS (by omega)) (pow_bnd_mono hS (by omega))
  have h3 : S ^ (a + b) + S ^ (a + b) ≤ S * S ^ (a + b) := by
    have := Nat.mul_le_mul_right (S ^ (a + b)) hS
    omega
  have h4 : S * S ^ (a + b) = S ^ (a + b + 1) := by ring
  omega

/-- **A product of bounded quantities is bounded**, with the exponents added. -/
theorem pow_bnd_mul {S X Y a b : Nat} (hX : X ≤ S ^ a) (hY : Y ≤ S ^ b) :
    X * Y ≤ S ^ (a + b) := by
  calc X * Y ≤ S ^ a * S ^ b := Nat.mul_le_mul hX hY
    _ = S ^ (a + b) := (pow_add S a b).symm

/-- **A power of a bounded quantity is bounded**, with the exponents multiplied. -/
theorem pow_bnd_pow {S X a e : Nat} (hX : X ≤ S ^ a) : X ^ e ≤ S ^ (a * e) := by
  calc X ^ e ≤ (S ^ a) ^ e := Nat.pow_le_pow_left hX e
    _ = S ^ (a * e) := (pow_mul S a e).symm

end Internal
end AllenderOQ3
