import AllenderOQ3.Internal.TransRank

/-!
# Inside an `R`-constant block a letter acts bijectively on the range

The descent decomposition splits a word of layer letters into at most `2 ^ W`
maximal blocks on which the `R`-class of the prefix transition is constant
(`card_prefix_RDescents_le_two_pow`, `REquiv_prefixEnd_of_no_descent`).  This
file describes what happens *inside* such a block.

If `a * u` is `R`-equivalent to `a`, then reading the letter `u` after the
prefix `a` loses no information: `runTrans u` restricted to the range of
`runTrans a` is a **bijection** onto the range of `runTrans (a * u)`.  So along
an `R`-constant block the transition is carried by a sequence of bijections
between sets of the same, fixed cardinality — the permutation picture that the
Barrington–Thérien analysis of the non-crossing monoid acts on.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {W : Nat}

open Classical in
/-- The range of a transition, as a finite set of configurations. -/
noncomputable def rangeTrans (g : TransMonoid W) : Finset (Config W) :=
  Finset.univ.image (runTrans g)

theorem rankTrans_eq_card_rangeTrans (g : TransMonoid W) :
    rankTrans g = (rangeTrans g).card := rfl

theorem mem_rangeTrans {g : TransMonoid W} {y : Config W} :
    y ∈ rangeTrans g ↔ ∃ x, runTrans g x = y := by
  classical
  simp [rangeTrans]

theorem rangeTrans_mul (a u : TransMonoid W) :
    rangeTrans (a * u) = (rangeTrans a).image (runTrans u) :=
  image_runTrans_mul a u

/-- **Reading a letter inside an `R`-constant block is injective on the range.** -/
theorem injOn_rangeTrans_of_REquiv {a u : TransMonoid W}
    (h : REquiv (TransMonoid W) (a * u) a) :
    Set.InjOn (runTrans u) ↑(rangeTrans a) := by
  intro p hp q hq hpq
  obtain ⟨x, hx⟩ := mem_rangeTrans.mp (Finset.mem_coe.mp hp)
  obtain ⟨y, hy⟩ := mem_rangeTrans.mp (Finset.mem_coe.mp hq)
  have hker := (RPreorder_iff_ker_subset a (a * u)).mp h.2
  have : runTrans (a * u) x = runTrans (a * u) y := by
    simp only [runTrans_mul, hx, hy, hpq]
  rw [← hx, ← hy]
  exact hker x y this

/-- Conversely, a letter acting injectively on the range keeps the `R`-class. -/
theorem REquiv_of_injOn_rangeTrans {a u : TransMonoid W}
    (h : Set.InjOn (runTrans u) ↑(rangeTrans a)) :
    REquiv (TransMonoid W) (a * u) a := by
  refine ⟨⟨u, rfl⟩, (RPreorder_iff_ker_subset a (a * u)).mpr ?_⟩
  intro x y hxy
  refine h ?_ ?_ (by simpa using hxy)
  · exact Finset.mem_coe.mpr (mem_rangeTrans.mpr ⟨x, rfl⟩)
  · exact Finset.mem_coe.mpr (mem_rangeTrans.mpr ⟨y, rfl⟩)

/-- **The block picture.**  Inside an `R`-constant block, a letter is a bijection
from the range of the current prefix onto the range of the next one. -/
theorem bijOn_rangeTrans_of_REquiv {a u : TransMonoid W}
    (h : REquiv (TransMonoid W) (a * u) a) :
    Set.BijOn (runTrans u) ↑(rangeTrans a) ↑(rangeTrans (a * u)) := by
  classical
  refine ⟨?_, injOn_rangeTrans_of_REquiv h, ?_⟩
  · intro p hp
    obtain ⟨x, hx⟩ := mem_rangeTrans.mp (Finset.mem_coe.mp hp)
    exact Finset.mem_coe.mpr (mem_rangeTrans.mpr ⟨x, by simp [← hx]⟩)
  · intro q hq
    obtain ⟨x, hx⟩ := mem_rangeTrans.mp (Finset.mem_coe.mp hq)
    exact ⟨runTrans a x, Finset.mem_coe.mpr (mem_rangeTrans.mpr ⟨x, rfl⟩), by
      simpa using hx⟩

/-- The rank is constant along an `R`-constant block. -/
theorem rankTrans_eq_of_REquiv {a b : TransMonoid W} (h : REquiv (TransMonoid W) a b) :
    rankTrans a = rankTrans b :=
  le_antisymm (rankTrans_le_of_RPreorder h.1) (rankTrans_le_of_RPreorder h.2)

/-- The product of the letters strictly between two prefix positions. -/
def blockEnd (w : List (TransMonoid W)) (a b : Nat) : TransMonoid W :=
  wordEnd ((w.take b).drop a)

/-- A later prefix is the earlier prefix times the intervening block. -/
theorem prefixEnd_eq_mul_blockEnd (w : List (TransMonoid W)) {a b : Nat} (hab : a ≤ b) :
    prefixEnd w b = prefixEnd w a * blockEnd w a b := by
  have htake : (w.take b).take a = w.take a := by
    rw [List.take_take, Nat.min_eq_left hab]
  rw [prefixEnd, prefixEnd, blockEnd, ← htake, ← wordEnd_append,
    List.take_append_drop]

/-- **The block picture along a descent-free stretch.**  If no `R`-descent occurs
between positions `a` and `b`, the product of the letters in between is a
bijection from the range of the prefix at `a` onto the range of the prefix at
`b`. -/
theorem bijOn_rangeTrans_blockEnd (w : List (TransMonoid W)) {a b : Nat} (hab : a ≤ b)
    (hno : ∀ i : Nat, a ≤ i → i < b →
      REquiv (TransMonoid W) (prefixEnd w i) (prefixEnd w (i + 1))) :
    Set.BijOn (runTrans (blockEnd w a b))
      ↑(rangeTrans (prefixEnd w a)) ↑(rangeTrans (prefixEnd w b)) := by
  have hsplit := prefixEnd_eq_mul_blockEnd w hab
  have hR : REquiv (TransMonoid W) (prefixEnd w a * blockEnd w a b) (prefixEnd w a) := by
    rw [← hsplit]
    exact REquiv_symm (TransMonoid W) _ _ (REquiv_prefixEnd_of_no_descent w hab hno)
  have h := bijOn_rangeTrans_of_REquiv hR
  rwa [← hsplit] at h

end Internal
end AllenderOQ3
