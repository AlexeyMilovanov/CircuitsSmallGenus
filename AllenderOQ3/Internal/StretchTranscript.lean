import AllenderOQ3.Internal.StretchPrefixReduction

/-!
# Transcripts of a stretch, and the algebraic leaf behind `StretchPrefixACC`

`StretchPrefixReduction` reduces the letter word problem to `StretchPrefixACC`:
circuits that certify `gin * (block product) = gout`, sound on every block and
complete on the order-isomorphism stretches.

This file isolates the *algebraic* content of the remaining obligation and
separates it from the circuit engineering.

* A **transcript** of a block is a sequence `rho : Nat → Config w → Config w`
  of candidate restrictions of the prefix products to the range of `gin`,
  starting at the identity and updated by one letter at a time.
  `runTrans_blockProd_eq_of_transcript` shows a transcript really does compute
  the action of the block on the range of `gin`, and
  `mul_blockProd_eq_of_transcript` turns that into the equation
  `gin * (block product) = gout` that `StretchPrefixACC` asks for.  Both are
  unconditional: no promise on the block is needed, which is what makes a
  *verified* transcript a sound certificate.

* `StretchHolonomy w` is the purely algebraic statement that along an
  order-isomorphism stretch the transcript is *compressible*: the restriction of
  the prefix product to the range of `gin` only depends on the sum, modulo a
  fixed `N`, of a per-letter exponent.  This is the holonomy/cyclicity input of
  the Barrington–Thérien cascade for `NonCrossing w`, stated with no reference
  to circuits.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-! ## Transcripts -/

/-- **A transcript computes the action of the block on the range of `gin`.**

If `rho a` is the identity on the range of `gin` and `rho (i + 1)` is obtained
from `rho i` by applying the letter at position `start + i`, then `rho c`
describes the action of the whole block `[start + a, start + c)` on that range.
No hypothesis on the letters is needed. -/
theorem runTrans_blockProd_eq_of_transcript {n : Nat}
    (letter : Nat → (Fin n → Bool) → TransMonoid w)
    (start : Nat) (x : Fin n → Bool) (gin : TransMonoid w)
    (rho : Nat → Config w → Config w) {a c : Nat} (hac : a ≤ c)
    (h0 : ∀ p ∈ rangeTrans gin, rho a p = p)
    (hstep : ∀ i, a ≤ i → i < c → ∀ p ∈ rangeTrans gin,
      rho (i + 1) p = runTrans (letter (start + i) x) (rho i p)) :
    ∀ p ∈ rangeTrans gin, runTrans (blockProd letter start a c x) p = rho c p := by
  induction c, hac using Nat.le_induction with
  | base => intro p hp; simp [h0 p hp]
  | succ c hac ih =>
      intro p hp
      have hprev : ∀ i, a ≤ i → i < c → ∀ p ∈ rangeTrans gin,
          rho (i + 1) p = runTrans (letter (start + i) x) (rho i p) := by
        intro i hi1 hi2 q hq
        exact hstep i hi1 (by omega) q hq
      have hsplit : blockProd letter start a (c + 1) x
          = blockProd letter start a c x * letter (start + c) x := by
        rw [← blockProd_succ letter start c x]
        exact (blockProd_concat letter start x hac (Nat.le_succ c)).symm
      rw [hsplit, runTrans_mul, ih hprev p hp]
      exact (hstep c hac (Nat.lt_succ_self c) p hp).symm

/-- **A verified transcript certifies the prefix equation.**  If, in addition to
being a transcript of the block, `rho c` sends the range of `gin` the way `gout`
sends the whole configuration space, then `gin * (block product) = gout`. -/
theorem mul_blockProd_eq_of_transcript {n : Nat}
    (letter : Nat → (Fin n → Bool) → TransMonoid w)
    (start : Nat) (x : Fin n → Bool) (gin gout : TransMonoid w)
    (rho : Nat → Config w → Config w) {a c : Nat} (hac : a ≤ c)
    (h0 : ∀ p ∈ rangeTrans gin, rho a p = p)
    (hstep : ∀ i, a ≤ i → i < c → ∀ p ∈ rangeTrans gin,
      rho (i + 1) p = runTrans (letter (start + i) x) (rho i p))
    (hfin : ∀ y : Config w, rho c (runTrans gin y) = runTrans gout y) :
    gin * blockProd letter start a c x = gout := by
  refine MulOpposite.unop_injective (funext fun y => ?_)
  have hmem : runTrans gin y ∈ rangeTrans gin := mem_rangeTrans.mpr ⟨y, rfl⟩
  have hact := runTrans_blockProd_eq_of_transcript letter start x gin rho hac h0 hstep
    (runTrans gin y) hmem
  have : runTrans (gin * blockProd letter start a c x) y = runTrans gout y := by
    rw [runTrans_mul, hact, hfin y]
  exact this

end Internal
end AllenderOQ3
