import Mathlib

/-!
# Collapse of a ceiling-division chain

`docs/MATHEMATICAL_PROOF.md` §9 iterates a merging round which replaces a count `m`
by `⌈m / B⌉ = (m + B - 1) / B`.  After `k` rounds the count is at most `C` as soon as
it started at most `C * B ^ k`; in particular a chain of `m₀` items collapses to a
single one after `k` rounds whenever `m₀ ≤ B ^ k`.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-- One merging round: `m ↦ ⌈m / B⌉`. -/
def ceilDivStep (B : Nat) (m : Nat) : Nat := (m + B - 1) / B

/-- A single round divides the bound by `B`. -/
theorem ceilDivStep_le {B : Nat} (hB : 1 ≤ B) {m D : Nat} (hm : m ≤ D * B) :
    ceilDivStep B m ≤ D := by
  have hBpos : 0 < B := hB
  have hlt : m + B - 1 < (D + 1) * B := by
    have : (D + 1) * B = D * B + B := by ring
    omega
  have := (Nat.div_lt_iff_lt_mul hBpos).mpr hlt
  simpa [ceilDivStep] using Nat.lt_succ_iff.mp this

/-- After `k` rounds of `m ↦ ⌈m / B⌉` a count bounded by `C * B ^ k` is bounded by `C`. -/
theorem iterate_ceilDiv_le (B : Nat) (hB : 1 ≤ B) (C : Nat) :
    ∀ (k m : Nat), m ≤ C * B ^ k → (fun x => (x + B - 1) / B)^[k] m ≤ C := by
  intro k
  induction k with
  | zero => intro m hm; simpa using hm
  | succ k ih =>
      intro m hm
      rw [Function.iterate_succ_apply]
      refine ih _ ?_
      have hm' : m ≤ (C * B ^ k) * B := by
        calc m ≤ C * B ^ (k + 1) := hm
          _ = (C * B ^ k) * B := by ring
      simpa [ceilDivStep] using ceilDivStep_le hB hm'

end AllenderOQ3.Internal
