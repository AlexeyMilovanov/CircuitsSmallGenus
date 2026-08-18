import AllenderOQ3.Internal.CascadeCoordinate

/-!
# Block boundaries of a bounded-change coordinate

`CascadeCoordinate` bounds the number of positions at which the rank/shape
coordinate of the prefix transitions of a word of monotone letters changes.  The
Barrington--Thérien cascade consumes that bound in the form of an *explicit
block decomposition*: a constant-length, non-decreasing tuple of boundary
positions

  `0 = bs 0 ≤ bs 1 ≤ … ≤ bs (K + 1) = len`

on each of whose half-open blocks `[bs j, bs (j + 1))` the coordinate is
constant.  That is what a guess-and-verify layer has to guess, and the existence
statement proved here is what makes the guess complete.

The main results are

* `exists_block_boundaries` — a sequence with at most `K` changes below `len`
  admits `K + 2` boundaries as above (pure combinatorics, any coordinate type);
* `card_shapeCoord_changes_range_le` — the change bound of
  `CascadeCoordinate.card_shapeCoord_changes_le` in the `Finset.range` form the
  block extraction consumes;
* `exists_shapeCoord_block_boundaries` — the resulting block decomposition of a
  word of `NonCrossing w` letters;
* `orderIso_blockEnd_of_mem_block` — on every one of those blocks the product of
  the intervening letters is an order isomorphism from the range at the start of
  the block onto the range at the current position.

A second, algebraic ingredient of the same step is recorded here:

* `REquiv_mul_iff_injOn_range` — reading one more letter keeps the prefix in its
  `R`-class exactly when that letter is injective on the current range, so along
  a block no two reachable configurations are ever merged;
* `injOn_range_of_shapeCoord_const` — the instance of that fact along a block.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/-! ## Counting changes of a sequence -/

/-- The number of positions below `t` at which the sequence `z` changes. -/
noncomputable def changeCount {Z : Type} [DecidableEq Z] (z : Nat → Z) (t : Nat) : Nat :=
  ((Finset.range t).filter fun i => z i ≠ z (i + 1)).card

theorem changeCount_zero {Z : Type} [DecidableEq Z] (z : Nat → Z) : changeCount z 0 = 0 := by
  simp [changeCount]

theorem changeCount_succ {Z : Type} [DecidableEq Z] (z : Nat → Z) (t : Nat) :
    changeCount z (t + 1) = changeCount z t + (if z t ≠ z (t + 1) then 1 else 0) := by
  classical
  rw [changeCount, changeCount, Finset.range_add_one, Finset.filter_insert]
  by_cases h : z t = z (t + 1)
  · rw [if_neg (not_not_intro h), if_neg (not_not_intro h), Nat.add_zero]
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]

theorem changeCount_mono {Z : Type} [DecidableEq Z] (z : Nat → Z) {a b : Nat} (hab : a ≤ b) :
    changeCount z a ≤ changeCount z b := by
  classical
  refine Finset.card_le_card ?_
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 hab, hi.2⟩

theorem changeCount_lt_of_ne {Z : Type} [DecidableEq Z] (z : Nat → Z) {t : Nat}
    (h : z t ≠ z (t + 1)) : changeCount z t < changeCount z (t + 1) := by
  rw [changeCount_succ, if_pos h]
  omega

/-! ## Extracting block boundaries -/

open Classical in
/-- **A bounded-change sequence has a constant-length block decomposition.**  If
`z` changes at most `K` times below `len`, then there are boundary positions
`0 = bs 0 ≤ bs 1 ≤ … ≤ bs (K + 1) = len`, all at most `len`, such that `z` is
constant on each half-open block `[bs j, bs (j + 1))`. -/
theorem exists_block_boundaries {Z : Type} [DecidableEq Z] (z : Nat → Z) (len K : Nat)
    (hK : changeCount z len ≤ K) :
    ∃ bs : Nat → Nat,
      bs 0 = 0 ∧
      (∀ j, bs j ≤ bs (j + 1)) ∧
      (∀ j, bs j ≤ len) ∧
      bs (K + 1) = len ∧
      (∀ j t, bs j ≤ t → t < bs (j + 1) → z t = z (bs j)) := by
  classical
  have hex : ∀ j : Nat, ∃ t : Nat, j ≤ changeCount z t ∨ t = len := fun _ => ⟨len, Or.inr rfl⟩
  set bs : Nat → Nat := fun j => Nat.find (hex j) with hbs
  have hspec : ∀ j, j ≤ changeCount z (bs j) ∨ bs j = len := fun j => Nat.find_spec (hex j)
  have hle : ∀ j, bs j ≤ len := fun j => Nat.find_le (Or.inr rfl)
  have hmin : ∀ j t, t < bs j → ¬ (j ≤ changeCount z t ∨ t = len) := by
    intro j t ht
    exact Nat.find_min (hex j) ht
  have hzero : bs 0 = 0 := Nat.le_zero.mp (Nat.find_le (Or.inl (Nat.zero_le _)))
  have hmono : ∀ j, bs j ≤ bs (j + 1) := by
    intro j
    refine Nat.find_le ?_
    rcases hspec (j + 1) with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  have hlast : bs (K + 1) = len := by
    rcases hspec (K + 1) with h | h
    · exfalso
      have hm := changeCount_mono z (hle (K + 1))
      omega
    · exact h
  refine ⟨bs, hzero, hmono, hle, hlast, ?_⟩
  -- constancy on a block, by induction from the left endpoint
  have hstep : ∀ j u, bs j ≤ u → u + 1 < bs (j + 1) → z u = z (u + 1) := by
    intro j u hu hu'
    by_contra hne
    have hlen : u < len := lt_of_lt_of_le (by omega) (hle (j + 1))
    -- `u` is below `bs (j+1)`, so the change count there is at most `j`
    have h1 : ¬ (j + 1 ≤ changeCount z u ∨ u = len) := hmin (j + 1) u (by omega)
    push_neg at h1
    have h2 : ¬ (j + 1 ≤ changeCount z (u + 1) ∨ u + 1 = len) := hmin (j + 1) (u + 1) hu'
    push_neg at h2
    have h3 : changeCount z u < changeCount z (u + 1) := changeCount_lt_of_ne z hne
    -- but `bs j ≤ u` forces the count at `u` to be at least `j`
    have h4 : j ≤ changeCount z u := by
      rcases hspec j with h | h
      · exact le_trans h (changeCount_mono z hu)
      · omega
    omega
  intro j t ht ht'
  induction t with
  | zero =>
      have : bs j = 0 := Nat.le_zero.mp ht
      rw [this]
  | succ u ih =>
      rcases Nat.lt_or_ge (bs j) (u + 1) with hlt | hge
      · have hu : bs j ≤ u := by omega
        have := ih hu (by omega)
        rw [← this]
        exact (hstep j u hu ht').symm
      · have : bs j = u + 1 := by omega
        rw [this]

/-! ## The rank/shape coordinate of a word of monotone letters -/

section Shape

variable {W : Nat}

/-- The change bound of `card_shapeCoord_changes_le`, in the `Finset.range` form
consumed by `exists_block_boundaries`. -/
theorem card_shapeCoord_changes_range_le {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) (len : Nat) :
    changeCount (fun t => shapeCoord (prefixEnd word t)) len
      ≤ 2 ^ W * (2 ^ W * 2 ^ W + 1) + 2 ^ W * 2 ^ W := by
  classical
  have h := card_changes_range_add_le
    (zz := fun t => shapeCoord (prefixEnd word t)) (mu := shapeMeasure) len
    (fun i _ => shapeMeasure_prefixEnd_le hmono i)
    (fun i _ hne => shapeMeasure_prefixEnd_lt hmono hne)
  have h' : ((Finset.range len).filter fun i =>
        shapeCoord (prefixEnd word i) ≠ shapeCoord (prefixEnd word (i + 1))).card
      + shapeMeasure (shapeCoord (prefixEnd word 0))
      ≤ shapeMeasure (shapeCoord (prefixEnd word len)) := h
  have hb := shapeMeasure_le (shapeCoord (prefixEnd word len))
  simp only [changeCount]
  omega

/-- **Block decomposition of a word of monotone letters.**  The rank/shape
coordinate of the prefix transitions is constant on each of a constant number of
blocks covering `[0, len)`. -/
theorem exists_shapeCoord_block_boundaries {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) (len : Nat) :
    ∃ bs : Nat → Nat,
      bs 0 = 0 ∧
      (∀ j, bs j ≤ bs (j + 1)) ∧
      (∀ j, bs j ≤ len) ∧
      bs (2 ^ W * (2 ^ W * 2 ^ W + 1) + 2 ^ W * 2 ^ W + 1) = len ∧
      (∀ j t, bs j ≤ t → t < bs (j + 1) →
        shapeCoord (prefixEnd word t) = shapeCoord (prefixEnd word (bs j))) :=
  exists_block_boundaries _ len _ (card_shapeCoord_changes_range_le hmono len)

/-- The non-crossing instance of the block decomposition. -/
theorem exists_shapeCoord_block_boundaries_nonCrossing {w : Nat} {word : List (TransMonoid w)}
    (hword : ∀ g ∈ word, g ∈ NonCrossing w) (len : Nat) :
    ∃ bs : Nat → Nat,
      bs 0 = 0 ∧
      (∀ j, bs j ≤ bs (j + 1)) ∧
      (∀ j, bs j ≤ len) ∧
      bs (2 ^ w * (2 ^ w * 2 ^ w + 1) + 2 ^ w * 2 ^ w + 1) = len ∧
      (∀ j t, bs j ≤ t → t < bs (j + 1) →
        shapeCoord (prefixEnd word t) = shapeCoord (prefixEnd word (bs j))) :=
  exists_shapeCoord_block_boundaries (monotone_of_forall_mem_nonCrossing hword) len

/-- **Inside a block the prefix transition keeps its `R`-class.**  A stretch on
which the rank/shape coordinate is constant contains no `R`-descent, so all the
prefix transitions along it have one and the same kernel. -/
theorem REquiv_prefixEnd_of_shapeCoord_const {word : List (TransMonoid W)} {a b : Nat}
    (hab : a ≤ b)
    (hconst : ∀ t, a ≤ t → t ≤ b → shapeCoord (prefixEnd word t) = shapeCoord (prefixEnd word a)) :
    REquiv (TransMonoid W) (prefixEnd word a) (prefixEnd word b) := by
  refine REquiv_prefixEnd_of_no_descent word hab (fun i hi1 hi2 => ?_)
  have h1 := (shapeCoord_eq_iff.mp (hconst i hi1 (by omega))).1
  have h2 := (shapeCoord_eq_iff.mp (hconst (i + 1) (by omega) (by omega))).1
  exact REquiv_prefixEnd_succ_of_rank_eq (by omega)

/-- **Inside a block the letters read so far act as an order isomorphism.**
Combining the block decomposition with `orderIso_blockEnd_of_shapeCoord_const`:
if the coordinate is constant on `[a, b']` for every `b' < b`, then for each such
position the product of the intervening letters is an order-isomorphism of the
reachable configurations. -/
theorem orderIso_blockEnd_of_mem_block {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) {a b t : Nat}
    (hconst : ∀ u, a ≤ u → u < b → shapeCoord (prefixEnd word u) = shapeCoord (prefixEnd word a))
    (hat : a ≤ t) (htb : t < b) :
    Set.BijOn (runTrans (blockEnd word a t))
        ↑(rangeTrans (prefixEnd word a)) ↑(rangeTrans (prefixEnd word t)) ∧
      ∀ p ∈ rangeTrans (prefixEnd word a), ∀ q ∈ rangeTrans (prefixEnd word a),
        (p ≤ q ↔ runTrans (blockEnd word a t) p ≤ runTrans (blockEnd word a t) q) :=
  orderIso_blockEnd_of_shapeCoord_const hmono hat
    (fun u hu hu' => hconst u hu (lt_of_le_of_lt hu' htb))

end Shape

/-! ## Staying in an `R`-class means never merging the reachable configurations -/

section Injectivity

variable {W : Nat}

open Classical in
/-- **Reading a letter keeps the prefix in its `R`-class exactly when the letter
is injective on the reachable configurations.**  Since Green's right preorder of
`TransMonoid W` is kernel inclusion, `p` and `p * a` have the same kernel iff `a`
separates the configurations that `p` can still produce.  This is the algebraic
form of "no rank is lost at this step". -/
theorem REquiv_mul_iff_injOn_range (p a : TransMonoid W) :
    REquiv (TransMonoid W) p (p * a) ↔
      Set.InjOn (runTrans a) ↑(Finset.univ.image (runTrans p)) := by
  classical
  constructor
  · rintro ⟨h1, -⟩ u hu v hv huv
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    exact (RPreorder_iff_ker_subset p (p * a)).mp h1 x y (by simpa using huv)
  · intro hinj
    refine ⟨(RPreorder_iff_ker_subset p (p * a)).mpr ?_, ⟨a, rfl⟩⟩
    intro x y hxy
    refine hinj ?_ ?_ (by simpa using hxy)
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)

open Classical in
/-- **Along a block no letter merges reachable configurations.**  If the
rank/shape coordinate does not change between the prefix positions `t` and
`t + 1`, then the letter read at `t` is injective on the range of the prefix at
`t`. -/
theorem injOn_range_of_shapeCoord_const {word : List (TransMonoid W)} {t : Nat}
    (h : shapeCoord (prefixEnd word t) = shapeCoord (prefixEnd word (t + 1))) :
    Set.InjOn (runTrans (wordEnd ((word[t]?).toList)))
      ↑(Finset.univ.image (runTrans (prefixEnd word t))) := by
  classical
  have hR : REquiv (TransMonoid W) (prefixEnd word t) (prefixEnd word (t + 1)) :=
    REquiv_prefixEnd_succ_of_rank_eq (shapeCoord_eq_iff.mp h).1.symm
  rw [prefixEnd_succ] at hR
  exact (REquiv_mul_iff_injOn_range _ _).mp hR

end Injectivity

end Internal
end AllenderOQ3
