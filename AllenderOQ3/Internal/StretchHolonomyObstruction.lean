import AllenderOQ3.Internal.StretchHolonomy
import AllenderOQ3.Internal.ConstantMaps

/-!
# An obstruction to the cyclic-holonomy hypothesis

`StretchHolonomyAt w N gin` (see `StretchHolonomy`) asks that the action, on the
range of `gin`, of a shape-constant stretch of `NonCrossing w` letters be
determined by the *sum* of a per-letter exponent.  A sum does not see the order
of the letters, so the hypothesis forces every shape-constant pair of letters to
commute on the range of `gin`.

That is a real restriction.  If `gin` has a **singleton** range — a rank-one
prefix — then *every* word is shape-constant out of `gin` (rank and shape count
of a singleton range are constant), so the hypothesis at such a `gin` forces all
of `NonCrossing w` to commute at that point.  Concretely, if `NonCrossing w`
contains two elements whose composites act differently on the point of the range
of a rank-one prefix (for instance two distinct constant maps), then
`StretchHolonomy w` is false, and the exponent must be allowed to depend on more
than the single letter it is attached to.

The witnesses exist as soon as `0 < w`: every constant map belongs to
`NonCrossing w` (`constTrans_mem_nonCrossing`), a constant map has a singleton
range, and two distinct constant maps do not commute at any configuration.  So
`StretchHolonomy w` is **false** for every positive width
(`not_stretchHolonomy_of_pos`).

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

attribute [local instance] Classical.propDecidable

/-- **Shape-constant pairs of letters must commute on the range.**  A sum of
per-letter exponents cannot distinguish `g * h` from `h * g`. -/
theorem not_stretchHolonomyAt_of_not_commute {N : Nat} {gin g h : TransMonoid w} {p : Config w}
    (hginmem : gin ∈ NonCrossing w) (hg : g ∈ NonCrossing w) (hh : h ∈ NonCrossing w)
    (hp : p ∈ rangeTrans gin)
    (hshape1 : ∀ k, k ≤ 2 → shapeCoord (gin * prefixEnd [g, h] k) = shapeCoord gin)
    (hshape2 : ∀ k, k ≤ 2 → shapeCoord (gin * prefixEnd [h, g] k) = shapeCoord gin)
    (hne : runTrans (g * h) p ≠ runTrans (h * g) p) :
    ¬ StretchHolonomyAt w N gin := by
  rintro ⟨state, expo, -, -, -, hword⟩
  have hmem1 : ∀ m ∈ [g, h], m ∈ NonCrossing w := by
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hg
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact hh
      · exact absurd hm (by simp)
  have hmem2 : ∀ m ∈ [h, g], m ∈ NonCrossing w := by
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hh
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact hg
      · exact absurd hm (by simp)
  have h1 := hword [g, h] hginmem hmem1 (by simpa using hshape1) p hp
  have h2 := hword [h, g] hginmem hmem2 (by simpa using hshape2) p hp
  rw [show ([g, h] : List (TransMonoid w)).prod = g * h by simp,
    show (([g, h] : List (TransMonoid w)).map expo).sum = expo g + expo h by simp] at h1
  rw [show ([h, g] : List (TransMonoid w)).prod = h * g by simp,
    show (([h, g] : List (TransMonoid w)).map expo).sum = expo h + expo g by simp] at h2
  rw [Nat.add_comm (expo h) (expo g)] at h2
  exact hne (h1.trans h2.symm)

/-! ## Rank-one prefixes -/

theorem compPairs_singleton (q : Config w) :
    compPairs ({q} : Finset (Config w)) = {(q, q)} := by
  classical
  ext y
  simp only [mem_compPairs, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact Prod.ext h1 h2
  · rintro rfl
    exact ⟨⟨rfl, rfl⟩, le_refl q⟩

/-- Out of a prefix with a singleton range, *every* stretch is shape-constant:
the range stays a singleton, so both the rank and the shape count are
constant. -/
theorem shapeCoord_mul_eq_of_rangeTrans_singleton {gin : TransMonoid w} {q : Config w}
    (hrange : rangeTrans gin = {q}) (m : TransMonoid w) :
    shapeCoord (gin * m) = shapeCoord gin := by
  classical
  have hr : rangeTrans (gin * m) = {runTrans m q} := by
    rw [rangeTrans_mul, hrange]
    simp
  refine shapeCoord_eq_iff.mpr ⟨?_, ?_⟩
  · rw [rankTrans_eq_card_rangeTrans, rankTrans_eq_card_rangeTrans, hr, hrange]
    simp
  · rw [shapeCount, shapeCount, hr, hrange, compPairs_singleton, compPairs_singleton]
    simp

/-- **The cyclic-holonomy hypothesis fails at a rank-one prefix carrying two
letters that do not commute at its point.** -/
theorem not_stretchHolonomyAt_of_rangeTrans_singleton {N : Nat} {gin g h : TransMonoid w}
    {q : Config w} (hginmem : gin ∈ NonCrossing w) (hg : g ∈ NonCrossing w)
    (hh : h ∈ NonCrossing w) (hrange : rangeTrans gin = {q})
    (hne : runTrans (g * h) q ≠ runTrans (h * g) q) :
    ¬ StretchHolonomyAt w N gin := by
  refine not_stretchHolonomyAt_of_not_commute hginmem hg hh
    (by rw [hrange]; exact Finset.mem_singleton_self q) ?_ ?_ hne
  · intro k _
    exact shapeCoord_mul_eq_of_rangeTrans_singleton hrange _
  · intro k _
    exact shapeCoord_mul_eq_of_rangeTrans_singleton hrange _

/-- **The global cyclic-holonomy hypothesis is refuted by a rank-one prefix with
two non-commuting letters.** -/
theorem not_stretchHolonomy_of_rangeTrans_singleton {gin g h : TransMonoid w}
    {q : Config w} (hginmem : gin ∈ NonCrossing w) (hg : g ∈ NonCrossing w)
    (hh : h ∈ NonCrossing w) (hrange : rangeTrans gin = {q})
    (hne : runTrans (g * h) q ≠ runTrans (h * g) q) :
    ¬ StretchHolonomy w := by
  rintro ⟨N, -, hol⟩
  exact not_stretchHolonomyAt_of_rangeTrans_singleton (N := N) hginmem hg hh hrange hne (hol gin)

/-! ## The hypothesis is false at every positive width -/

theorem rangeTrans_constTrans (q : Config w) : rangeTrans (Holonomy.constTrans q) = {q} := by
  classical
  ext y
  simp [mem_rangeTrans, eq_comm]

/-- **The cyclic-holonomy hypothesis is false for every positive width.**  The
constant maps all lie in `NonCrossing w`, a constant map has a singleton range,
and two distinct constant maps compose in either order to the two different
constants — which a sum of per-letter exponents cannot tell apart. -/
theorem not_stretchHolonomy_of_pos {w : Nat} (hw : 0 < w) : ¬ StretchHolonomy w := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b : Config w, a ≠ b := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    intro h
    have := congrFun h ⟨0, hw⟩
    simp at this
  refine not_stretchHolonomy_of_rangeTrans_singleton (gin := Holonomy.constTrans a)
    (g := Holonomy.constTrans a) (h := Holonomy.constTrans b) (q := a)
    (Holonomy.constTrans_mem_nonCrossing a) (Holonomy.constTrans_mem_nonCrossing a)
    (Holonomy.constTrans_mem_nonCrossing b) (rangeTrans_constTrans a) ?_
  simp only [runTrans_mul, Holonomy.runTrans_constTrans]
  exact fun h => hab h.symm

end Internal
end AllenderOQ3
