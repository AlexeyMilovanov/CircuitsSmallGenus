import AllenderOQ3.Internal.CeilDivChain

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# Polylog relation composition (§9)

`docs/MATHEMATICAL_PROOF.md` §9 composes a chain of `≤ C * B ^ k` constant-state block
relations into a single relation by `k + 1` rounds of the depth-two OR-of-AND operator
`accOrAnd`, where `B = ⌊log₂(n+1)⌋` and the large-`n` cutoff guarantees `2 * C ≤ B`.

The round-count arithmetic (B3b) is already proved, independently of any circuit, in
`AllenderOQ3.Internal.CeilDivChain`:

* `ceilDivStep`, `ceilDivStep_le` — one round `m ↦ ⌈m / B⌉` divides the bound by `B`;
* `iterate_ceilDiv_le`           — after `k` rounds a bound `C * B ^ k` becomes `C`.

`polylogCompose_collapse` below is the §9 payoff of that arithmetic: above the cutoff a
chain of length `≤ C * B ^ k` collapses to a single relation after `k + 1` rounds.  It is
proved from `iterate_ceilDiv_le`, not re-derived.

The two remaining §9 leaves are purely about the ACC realization of one round and of the
whole chain.  They consume the depth-two round operator
`AllenderOQ3.Internal.ACCJoin.accOrAnd` (with `accAccepts_accOrAnd`, `accOrAnd_layer_le`)
together with the constant-state block relations of `AllenderOQ3.Internal.PlanarBlock`
(`planarBlockRelation`) and the composition law
`AllenderOQ3.Internal.StateChain.reach_add`:

* **B3a** (one round): an `ACC[M]` circuit for the composite of `≤ B` block relations, of
  depth `+ 2` and size `× (n + 1) ^ q`, with the modulus unchanged;
* **B3c** (full chain): iterate B3a `k + 1` times — the count of which is fixed by
  `polylogCompose_collapse` — giving one `ACC[M]` relation of constant added depth and
  polynomial size.

These are carried as Aristotle leaves in the iteration packet; they are intentionally not
present here as `sorry` stubs, so that every remaining `sorry` in the section is a faithful,
non-vacuous statement rather than a tautological `: True` interface.
-/

/-- **B3b payoff (§9).**  Above the large-`n` cutoff `2 * C ≤ B`, a chain of at most
`C * B ^ k` constant-state relations collapses, under the round map `m ↦ ⌈m / B⌉`, to a
single relation after `k + 1` rounds.  This fixes the number of `accOrAnd` rounds to the
constant `k + 1`, which is what makes the total added depth constant in §9.

It is a direct consequence of the already-proved `iterate_ceilDiv_le`: from `m ≤ C * B ^ k`
and `C ≤ B` (a consequence of the cutoff) we get `m ≤ 1 * B ^ (k + 1)`, so after `k + 1`
rounds the count is at most `1`. -/
theorem polylogCompose_collapse (B C k m : Nat) (hB : 1 ≤ B) (hcut : 2 * C ≤ B)
    (hm : m ≤ C * B ^ k) :
    (fun x => (x + B - 1) / B)^[k + 1] m ≤ 1 := by
  have hC : C ≤ B := by omega
  apply iterate_ceilDiv_le B hB 1 (k + 1) m
  calc m ≤ C * B ^ k := hm
    _ ≤ B * B ^ k := Nat.mul_le_mul hC (le_refl (B ^ k))
    _ = B ^ (k + 1) := by rw [pow_succ]; ring
    _ = 1 * B ^ (k + 1) := (one_mul _).symm

/-- **The large-`n` cutoff.**  The §9 blocking parameter `B = ⌊log₂ (n+1)⌋` exceeds any
fixed constant `c` once `n ≥ 2 ^ c`; this is what discharges the hypothesis `2 * C ≤ B`
of `polylogCompose_collapse` above a threshold. -/
theorem le_log2_succ_of_pow_le (c n : Nat) (h : 2 ^ c ≤ n) : c ≤ Nat.log2 (n + 1) := by
  rw [Nat.log2_eq_log_two]
  exact Nat.le_log_of_pow_le (by omega) (by omega)

end AllenderOQ3.Internal
