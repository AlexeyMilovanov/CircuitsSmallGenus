import AllenderOQ3.Internal.Glue

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# §7.6 quantitative bookkeeping for the planar bridge

The width induction of §7 produces, at width `w`, a size bound of the shape

```text
S_w(N) ≤ w * N * A * (N+1)^p + C * (N+1)^k + C' * (N+1)
```

with `A, C, C', p, k` depending only on `w`.  The downstream interface
(`PlanarBridgeAt`) requires the pure form `≤ (N+1)^e`.  The lemmas below perform
exactly that collapse: three powers are absorbed into one exponent
(`three_pow_le`), and the leading constants are absorbed by raising the exponent
(`size_recurrence_absorb`), using `1 ≤ N` — every `ADRCircuit` has at least one
gate, because it carries `output : Fin gateCount`.

Everything here is `sorry`-free.
-/

/-- Three powers of a base `≥ 2` are absorbed by two extra units in the exponent. -/
theorem three_pow_le {T : Nat} (hT : 2 ≤ T) (a b k : Nat) :
    T ^ a + T ^ b + T ^ k ≤ T ^ (max (max a b) k + 2) := by
  have h1 : T ^ a + T ^ b ≤ T ^ (max a b + 1) := pow_add_pow_le hT a b
  have h2 : T ^ (max a b + 1) + T ^ k ≤ T ^ (max (max a b + 1) k + 1) :=
    pow_add_pow_le hT _ _
  have h3 : max (max a b + 1) k + 1 ≤ max (max a b) k + 2 := by omega
  have h4 : T ^ (max (max a b + 1) k + 1) ≤ T ^ (max (max a b) k + 2) :=
    Nat.pow_le_pow_right (by omega) h3
  omega

/-- A linear-in-`N` multiple of a power is absorbed by one extra unit in the exponent. -/
theorem mul_self_pow_le {N : Nat} (p : Nat) : N * (N + 1) ^ p ≤ (N + 1) ^ (p + 1) := by
  rw [pow_succ]
  exact Nat.mul_le_mul (Nat.le_succ N) (le_refl _) |>.trans_eq (Nat.mul_comm _ _)

/-- **§7.6 size collapse.**  The recurrence bound produced by the width induction has the
pure polynomial form `(N+1)^e` required by `PlanarBridgeAt`, for an exponent depending
only on the level constants. -/
theorem size_recurrence_absorb {N w A p C k C' S : Nat} (hN : 1 ≤ N)
    (h : S ≤ w * N * A * (N + 1) ^ p + C * (N + 1) ^ k + C' * (N + 1)) :
    S ≤ (N + 1) ^ (max (max (w * A + (p + 1)) (C + k)) (C' + 1) + 2) := by
  have hT : 2 ≤ N + 1 := by omega
  have e1 : w * N * A * (N + 1) ^ p ≤ (N + 1) ^ (w * A + (p + 1)) := by
    have hrw : w * N * A * (N + 1) ^ p = w * A * (N * (N + 1) ^ p) := by ring
    calc w * N * A * (N + 1) ^ p = w * A * (N * (N + 1) ^ p) := hrw
      _ ≤ w * A * (N + 1) ^ (p + 1) := Nat.mul_le_mul_left _ (mul_self_pow_le p)
      _ ≤ (N + 1) ^ (w * A + (p + 1)) := const_mul_pow_le hT _ _
  have e2 : C * (N + 1) ^ k ≤ (N + 1) ^ (C + k) := const_mul_pow_le hT _ _
  have e3 : C' * (N + 1) ≤ (N + 1) ^ (C' + 1) := by
    have : C' * (N + 1) ^ 1 ≤ (N + 1) ^ (C' + 1) := const_mul_pow_le hT _ _
    simpa using this
  have hsum := three_pow_le hT (w * A + (p + 1)) (C + k) (C' + 1)
  omega

end AllenderOQ3.Internal
