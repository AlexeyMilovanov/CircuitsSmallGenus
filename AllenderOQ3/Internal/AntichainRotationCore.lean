import AllenderOQ3.Internal.StartRank
import AllenderOQ3.Internal.StartRotationComb
import AllenderOQ3.Internal.StartSuccBridge
import AllenderOQ3.Internal.ConstantFreeLayers
import AllenderOQ3.Internal.ArcWordBlocks
import AllenderOQ3.Internal.IntervalStart
import AllenderOQ3.Internal.StartRotationGeo

/-!
# B2-core: a single constant-free layer rotates the starts (the geometric crux)

This file isolates the *single* open geometric obligation of Part B:

* `startRotationBetween_of_cyclic_order_preservation` — a constant-free map `g`
  bijecting a top-free antichain of interval configurations `A` onto another
  such antichain `B` induces a **relative start rotation** `A → B`: the start
  rank shifts by a constant additive offset in `ZMod A.card`
  (`IsStartRotationBetween`).

Everything above this in the section consumes it as a black box:
`AntichainRotation.lean` lifts it along the constant-free word (B2-word,
`sorry`-free), and `StartRank.lean` turns two such rotations into element-wise
commutation (B3 + B4, `sorry`-free).  So this lemma is the last mile to the
byte-exact leaf `intervalAntichainsCommuteCF_holds`.

## Intended route (paper §4 / plan 6c)

The arcs emitted from one interval form a *contiguous block* of the common arc
word (`ArcWordBlocks.lean`).  Reading the block gives, for each input interval,
a *leading cut* `κ(x)`; the constant-free layer's *first-true-target* map `λ`
sends a cut to the start of the output interval, and the output start is
`λ(κ(x)) mod w` (`IntervalStart.startOf`).

## Pitfall found this iteration (why the earlier skeleton was pruned)

An earlier draft decomposed this via two maps `startToLeadingCut` (`x ↦ κ(x)`)
and `lambdaFirstTrueTarget` (`λ`) asserted only to be **weakly monotone**
(`rank x ≤ rank y → κ x ≤ κ y`, and `c₁ ≤ c₂ → λ c₁ ≤ λ c₂`) together with the
composition identity `startOf (g x) = λ (κ x) % w`.  Those three facts are
**insufficient**: weak monotonicity followed by reduction `mod w` does not force
a rotation.  Counterexample (`w = 4`, `A.card = 4`): source ranks `0,1,2,3` with
`λ(κ ·)` values `0,2,5,7` are weakly monotone and give distinct output starts
`0,2,1,3`, yet `0,2,1,3` is **not** a cyclic shift of `0,1,2,3`.  The missing
ingredient is the **degree-one / bounded-span (single-winding)** property: as `x`
runs once through the source cycle, `λ(κ(x))` must wind around the width-`w`
cycle exactly once.  The three weak-monotone statements omit it, so they were
removed rather than left as a misleading (unprovable-as-stated) skeleton.

## Recommended valid decomposition (for the next iteration / Aristotle)

Split the crux into a *geometric* leaf and a *pure-combinatorial* lemma:

* **GEO (the real crux, local form).**  `runTrans g` sends cyclically
  consecutive source starts to cyclically consecutive target starts, i.e. it
  commutes with the cyclic *start-successor* on the antichain.  Equivalently, it
  preserves the cyclic order of starts.  This is exactly the degree-one content
  and is what the arc-word block reading supplies.
* **COMB (closeable, no geometry).**  A bijection `A → B` between two top-free
  interval antichains that commutes with the cyclic start-successor induces
  `IsStartRotationBetween hw A.card A B f`.  Proof sketch: the start rank is an
  order iso `A ≃ Fin A.card` (`StartRank.startRank_injOn`, `startRank_lt_card`),
  the successor increments the rank by `1` in `ZMod A.card`, so the induced
  permutation `σ` of ranks satisfies `σ (i+1) = σ i + 1`, whence
  `σ i = σ 0 + i` — a constant offset.

`startRotationBetween_of_cyclic_order_preservation` then follows by
`COMB (GEO g)`.  Only GEO carries genuine geometric debt.

## Status: COMB is now proved

`StartRotationComb.lean` discharges the whole combinatorial half, `sorry`-free:
`isStartRotationBetween_of_rank_succ_step` takes the hypothesis

```
∀ x ∈ A, ∀ y ∈ A,
  (startRank hw A y : ZMod A.card) = (startRank hw A x : ZMod A.card) + 1 →
  (startRank hw B (f y) : ZMod A.card) = (startRank hw B (f x) : ZMod A.card) + 1
```

(the rank form of GEO: cyclically consecutive source ranks go to cyclically
consecutive target ranks) and returns `IsStartRotationBetween hw A.card A B f`.
It rests on `image_startRank_eq_range` (the start rank is a bijection of the
antichain onto `Finset.range A.card`) and the `ZMod` atom
`eq_add_of_succ_commute` (`σ (i+1) = σ i + 1` forces `σ i = σ 0 + i`).

`StartSuccBridge.lean` additionally translates that rank hypothesis into the
language the geometry speaks, `sorry`-free: `IsCyclicStartSucc hw L x y` says
`startOf y` is the next member start above `startOf x` (or the wrap-around
max → min), `rank_succ_of_isCyclicStartSucc` and `isCyclicStartSucc_of_rank_succ`
identify it with the `+1` step of the rank in `ZMod L.card`, and

```
isStartRotationBetween_of_startSucc_preserving :
  … → Set.MapsTo f ↑A ↑B → A.card = B.card →
  (∀ x ∈ A, ∀ y ∈ A, IsCyclicStartSucc hw A x y → IsCyclicStartSucc hw B (f x) (f y)) →
  IsStartRotationBetween hw A.card A B f
```

So the only remaining debt below is *GEO*: that `runTrans g`, for a
constant-free `g`, preserves the cyclic start successor between the two
antichains.  Nothing combinatorial is left.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- **B2-core (the section crux): a single constant-free layer rotates the
starts.**  A constant-free map `g` bijecting a top-free antichain of interval
configurations `A` onto another such antichain `B` induces a relative start
rotation `A → B` (a constant additive offset on the start rank in `ZMod A.card`).

The geometric input (paper §4 / plan 6c): the arcs from an interval form a
contiguous block of the common arc word; reading it, the output start is a
degree-one (single-winding) reindexing of the input start, so the induced map on
the cyclic order of starts is a rotation.  Numerical anchor: zero exceptions over
14,238,180 instances on the exact `w = 4` monoid.

See the module docstring for the recommended `GEO`/`COMB` split; `COMB` is pure
finite combinatorics, `GEO` (cyclic-order preservation of starts) is the only
remaining geometric obligation. -/
theorem startRotationBetween_of_cyclic_order_preservation (hw : 0 < w) {g : TransMonoid w}
    (hg : isConstantFreeMap w g) {A B : Finset (Config w)}
    (hA : ∀ y ∈ A, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hB : ∀ y ∈ B, IsIntervalConfig y ∧ y ≠ topConfig w)
    (hAanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
    (hBanti : ∀ x ∈ B, ∀ y ∈ B, x ≤ y → x = y)
    (hbij : Set.BijOn (runTrans g) ↑A ↑B) :
    IsStartRotationBetween hw A.card A B (runTrans g) := by
  have hAInt : ∀ y ∈ A, IsIntervalConfig y := fun y hy => (hA y hy).1
  have hBInt : ∀ y ∈ B, IsIntervalConfig y := fun y hy => (hB y hy).1
  have hmaps : Set.MapsTo (runTrans g) ↑A ↑B := hbij.mapsTo
  have hcard : A.card = B.card := by
    have himg : A.image (runTrans g) = B :=
      Finset.coe_injective (by rw [Finset.coe_image]; exact hbij.image_eq)
    rw [← himg, Finset.card_image_of_injOn hbij.injOn]
  have hpres : ∀ x ∈ A, ∀ y ∈ A, IsCyclicStartSucc hw A x y →
      IsCyclicStartSucc hw B (runTrans g x) (runTrans g y) :=
    fun x hx y hy hsucc =>
      isCyclicStartSucc_preserved_of_constantFreeLayer
        hw hg hA hB hAanti hBanti hbij x y hx hy hsucc
  exact isStartRotationBetween_of_startSucc_preserving
    hw hAInt hAanti hBInt hBanti hmaps hcard hpres

end Internal
end AllenderOQ3
