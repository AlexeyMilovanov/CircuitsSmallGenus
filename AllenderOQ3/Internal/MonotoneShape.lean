import AllenderOQ3.Internal.TransBlock
import AllenderOQ3.Internal.NonCrossingUnits

set_option autoImplicit false

/-!
# The shape of the range of a monotone transition

Inside an `R`-constant block of a word the letters act *bijectively* between the
ranges of consecutive prefixes (`bijOn_rangeTrans_of_REquiv`), and for a word of
`NonCrossing w` letters those bijections are moreover **monotone**
(`monotone_of_mem_nonCrossing`).  A monotone bijection between two finite posets
need not be an order isomorphism: it can only *add* comparabilities.  This file
makes that observation quantitative.

* `compPairs S` — the comparable pairs inside a finite set `S`, i.e. the *shape*
  of the order induced on `S`;
* `card_compPairs_le_of_monotoneOn` — a monotone injection pushes the shape
  forward, so the number of comparable pairs never decreases;
* `le_of_le_image_of_card_compPairs_le` — as soon as the count does not increase, the
  map reflects the order: it is an order isomorphism onto its image;
* `shapeCount g = (compPairs (rangeTrans g)).card`, with
  `shapeCount_le_of_REquiv` (monotonicity along a block),
  `shapeCount_le_sq` (a bound independent of the length of the word), and
  `le_iff_of_shapeCount_le` / `le_iff_runTrans_blockEnd_of_shapeCount_le`
  (the order-isomorphism conclusion, per letter and per block).

Because `shapeCount` is a non-decreasing natural number bounded by
`2 ^ W * 2 ^ W` along an `R`-constant block, it can strictly increase only
boundedly often, however long the word is: after boundedly many *shape
transitions* the letters of the block act as order isomorphisms between the
successive ranges.  That is the aperiodic/group splitting of a block which the
Barrington--Thérien analysis of `NonCrossing w` runs on.

Everything here is `sorry`-free.
-/

namespace AllenderOQ3
namespace Internal

/-! ## Shapes of finite subsets of a preorder -/

section Shape

variable {alpha : Type} [Preorder alpha]

open Classical in
/-- The comparable ordered pairs inside a finite set: the *shape* of the order
induced on `S`. -/
noncomputable def compPairs (S : Finset alpha) : Finset (alpha × alpha) :=
  (S ×ˢ S).filter (fun p => p.1 ≤ p.2)

theorem mem_compPairs {S : Finset alpha} {p : alpha × alpha} :
    p ∈ compPairs S ↔ (p.1 ∈ S ∧ p.2 ∈ S) ∧ p.1 ≤ p.2 := by
  classical
  rw [compPairs, Finset.mem_filter, Finset.mem_product]

/-- **A monotone injection can only add comparabilities.**  If `f` maps `S` into
`T`, is injective on `S` and monotone on `S`, then `T` has at least as many
comparable pairs as `S`. -/
theorem card_compPairs_le_of_monotoneOn {S T : Finset alpha} {f : alpha → alpha}
    (hmap : ∀ x ∈ S, f x ∈ T)
    (hmono : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → f x ≤ f y)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) :
    (compPairs S).card ≤ (compPairs T).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun p => (f p.1, f p.2)) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, mem_compPairs] at hp ⊢
    exact ⟨⟨hmap _ hp.1.1, hmap _ hp.1.2⟩, hmono _ hp.1.1 _ hp.1.2 hp.2⟩
  · intro p hp q hq hpq
    rw [Finset.mem_coe, mem_compPairs] at hp hq
    have h1 : f p.1 = f q.1 := congrArg Prod.fst hpq
    have h2 : f p.2 = f q.2 := congrArg Prod.snd hpq
    exact Prod.ext (hinj _ hp.1.1 _ hq.1.1 h1) (hinj _ hp.1.2 _ hq.1.2 h2)

/-- **A monotone injection that does not increase the shape count reflects the
order.**  Together with `card_compPairs_le_of_monotoneOn` this says that a
monotone bijection between finite sets with the same number of comparable pairs
is an order isomorphism. -/
theorem le_of_le_image_of_card_compPairs_le {S T : Finset alpha} {f : alpha → alpha}
    (hmap : ∀ x ∈ S, f x ∈ T)
    (hmono : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → f x ≤ f y)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y)
    (hcard : (compPairs T).card ≤ (compPairs S).card)
    {x y : alpha} (hx : x ∈ S) (hy : y ∈ S) (hxy : f x ≤ f y) : x ≤ y := by
  classical
  -- the induced map on comparable pairs is injective, and by the count it is onto
  have hmapsTo : ∀ p ∈ compPairs S, ((f p.1, f p.2) : alpha × alpha) ∈ compPairs T := by
    intro p hp
    rw [mem_compPairs] at hp ⊢
    exact ⟨⟨hmap _ hp.1.1, hmap _ hp.1.2⟩, hmono _ hp.1.1 _ hp.1.2 hp.2⟩
  have hinj' : ∀ (p : alpha × alpha) (hp : p ∈ compPairs S) (q : alpha × alpha)
      (hq : q ∈ compPairs S), ((f p.1, f p.2) : alpha × alpha) = (f q.1, f q.2) → p = q := by
    intro p hp q hq hpq
    rw [mem_compPairs] at hp hq
    exact Prod.ext (hinj _ hp.1.1 _ hq.1.1 (congrArg Prod.fst hpq))
      (hinj _ hp.1.2 _ hq.1.2 (congrArg Prod.snd hpq))
  have hmem : ((f x, f y) : alpha × alpha) ∈ compPairs T :=
    mem_compPairs.mpr ⟨⟨hmap _ hx, hmap _ hy⟩, hxy⟩
  obtain ⟨p, hp, hpe⟩ :=
    Finset.surj_on_of_inj_on_of_card_le (s := compPairs S) (t := compPairs T)
      (fun p _ => ((f p.1, f p.2) : alpha × alpha)) hmapsTo
      (fun p q hp hq h => hinj' p hp q hq h) hcard _ hmem
  have hp' := mem_compPairs.mp hp
  have h1 : p.1 = x := hinj _ hp'.1.1 _ hx (congrArg Prod.fst hpe).symm
  have h2 : p.2 = y := hinj _ hp'.1.2 _ hy (congrArg Prod.snd hpe).symm
  rw [← h1, ← h2]
  exact hp'.2

end Shape

/-! ## The shape of the range of a transition -/

section Trans

variable {W : Nat}

open Classical in
/-- The number of comparable pairs in the range of a transition. -/
noncomputable def shapeCount (g : TransMonoid W) : Nat := (compPairs (rangeTrans g)).card

/-- The shape count of a transition is bounded independently of any word. -/
theorem shapeCount_le_sq (g : TransMonoid W) : shapeCount g ≤ 2 ^ W * 2 ^ W := by
  classical
  have h1 : shapeCount g ≤ ((rangeTrans g) ×ˢ (rangeTrans g)).card :=
    Finset.card_filter_le _ _
  have h2 : ((rangeTrans g) ×ˢ (rangeTrans g)).card = rankTrans g * rankTrans g := by
    rw [Finset.card_product, rankTrans_eq_card_rangeTrans]
  have h3 : rankTrans g ≤ 2 ^ W := by
    have := rankTrans_le_card g
    simpa using this
  exact le_trans h1 (by rw [h2]; exact Nat.mul_le_mul h3 h3)

/-- **The shape count never decreases inside an `R`-constant block.**  Reading a
monotone letter that keeps the `R`-class maps the range bijectively and
monotonically onto the next range, so comparabilities can only be added. -/
theorem shapeCount_le_of_REquiv {a u : TransMonoid W} (hu : Monotone (MulOpposite.unop u))
    (h : REquiv (TransMonoid W) (a * u) a) : shapeCount a ≤ shapeCount (a * u) := by
  classical
  have hbij := bijOn_rangeTrans_of_REquiv h
  refine card_compPairs_le_of_monotoneOn (f := runTrans u) ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_coe.mp (hbij.mapsTo (Finset.mem_coe.mpr hx))
  · intro x _ y _ hxy
    exact hu hxy
  · intro x hx y hy hxy
    exact hbij.injOn (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy

/-- **A letter that does not raise the shape count acts as an order
isomorphism.**  Inside an `R`-constant block, if the shape count of the next
prefix does not exceed that of the current one, then the letter reflects the
order on the current range — combined with `shapeCount_le_of_REquiv` this is the
statement that the shape has stabilised. -/
theorem le_iff_of_shapeCount_le {a u : TransMonoid W} (hu : Monotone (MulOpposite.unop u))
    (h : REquiv (TransMonoid W) (a * u) a) (hsh : shapeCount (a * u) ≤ shapeCount a)
    {p q : Config W} (hp : p ∈ rangeTrans a) (hq : q ∈ rangeTrans a) :
    p ≤ q ↔ runTrans u p ≤ runTrans u q := by
  classical
  have hbij := bijOn_rangeTrans_of_REquiv h
  refine ⟨fun hpq => hu hpq, fun hpq => ?_⟩
  refine le_of_le_image_of_card_compPairs_le (f := runTrans u)
    (S := rangeTrans a) (T := rangeTrans (a * u))
    (fun x hx => Finset.mem_coe.mp (hbij.mapsTo (Finset.mem_coe.mpr hx)))
    (fun x _ y _ hxy => hu hxy)
    (fun x hx y hy hxy => hbij.injOn (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy)
    hsh hp hq hpq

/-- **A letter that returns the range to itself acts as an order automorphism.**
This is the maximal-subgroup picture: an element that keeps both the `R`-class
and the range of the current prefix permutes that range and preserves *and*
reflects the order on it. -/
theorem le_iff_of_rangeTrans_eq {a u : TransMonoid W} (hu : Monotone (MulOpposite.unop u))
    (h : REquiv (TransMonoid W) (a * u) a) (hr : rangeTrans (a * u) = rangeTrans a)
    {p q : Config W} (hp : p ∈ rangeTrans a) (hq : q ∈ rangeTrans a) :
    p ≤ q ↔ runTrans u p ≤ runTrans u q :=
  le_iff_of_shapeCount_le hu h (le_of_eq (by rw [shapeCount, shapeCount, hr])) hp hq

/-- In the situation of `le_iff_of_rangeTrans_eq` the letter is a bijection of
the range onto itself. -/
theorem bijOn_rangeTrans_self {a u : TransMonoid W}
    (h : REquiv (TransMonoid W) (a * u) a) (hr : rangeTrans (a * u) = rangeTrans a) :
    Set.BijOn (runTrans u) ↑(rangeTrans a) ↑(rangeTrans a) := by
  have := bijOn_rangeTrans_of_REquiv h
  rwa [hr] at this

/-! ## Blocks of a word -/

/-- The product of the letters of a stretch of a word is monotone as soon as all
letters are. -/
theorem monotone_blockEnd {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) (a b : Nat) :
    Monotone (MulOpposite.unop (blockEnd word a b)) := by
  have hsub : ∀ g ∈ (word.take b).drop a, g ∈ monoSubmonoid W := by
    intro g hg
    have hg' : g ∈ word :=
      ((List.drop_sublist a (word.take b)).trans (List.take_sublist b word)).mem hg
    exact hmono g hg'
  exact monoSubmonoid W |>.list_prod_mem hsub

/-- **The shape count is non-decreasing along a descent-free stretch of a word of
monotone letters.** -/
theorem shapeCount_prefixEnd_le {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) {a b : Nat} (hab : a ≤ b)
    (hno : ∀ i : Nat, a ≤ i → i < b →
      REquiv (TransMonoid W) (prefixEnd word i) (prefixEnd word (i + 1))) :
    shapeCount (prefixEnd word a) ≤ shapeCount (prefixEnd word b) := by
  classical
  have hbij := bijOn_rangeTrans_blockEnd word hab hno
  have hu : Monotone (MulOpposite.unop (blockEnd word a b)) := monotone_blockEnd hmono a b
  refine card_compPairs_le_of_monotoneOn (f := runTrans (blockEnd word a b)) ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_coe.mp (hbij.mapsTo (Finset.mem_coe.mpr hx))
  · intro x _ y _ hxy
    exact hu hxy
  · intro x hx y hy hxy
    exact hbij.injOn (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy

/-- **A block with a stable shape acts by an order isomorphism.**  If no
`R`-descent occurs between the prefix positions `a` and `b` of a word of monotone
letters and the shape count is the same at both ends, the product of the letters
in between is an order isomorphism from the range at `a` onto the range at `b`.
-/
theorem le_iff_runTrans_blockEnd_of_shapeCount_le {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) {a b : Nat} (hab : a ≤ b)
    (hno : ∀ i : Nat, a ≤ i → i < b →
      REquiv (TransMonoid W) (prefixEnd word i) (prefixEnd word (i + 1)))
    (hsh : shapeCount (prefixEnd word b) ≤ shapeCount (prefixEnd word a))
    {p q : Config W} (hp : p ∈ rangeTrans (prefixEnd word a))
    (hq : q ∈ rangeTrans (prefixEnd word a)) :
    p ≤ q ↔ runTrans (blockEnd word a b) p ≤ runTrans (blockEnd word a b) q := by
  classical
  have hbij := bijOn_rangeTrans_blockEnd word hab hno
  have hu : Monotone (MulOpposite.unop (blockEnd word a b)) := monotone_blockEnd hmono a b
  refine ⟨fun hpq => hu hpq, fun hpq => ?_⟩
  refine le_of_le_image_of_card_compPairs_le (f := runTrans (blockEnd word a b))
    (S := rangeTrans (prefixEnd word a)) (T := rangeTrans (prefixEnd word b))
    (fun x hx => Finset.mem_coe.mp (hbij.mapsTo (Finset.mem_coe.mpr hx)))
    (fun x _ y _ hxy => hu hxy)
    (fun x hx y hy hxy => hbij.injOn (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy)
    hsh hp hq hpq

/-! ## Only boundedly many shape increases -/

/-- A non-decreasing `Nat`-valued function has at most `g L - g 0` strict
increases below `L`. -/
theorem card_strictIncrease_add_le (g : Nat → Nat) :
    ∀ L : Nat, (∀ i, i < L → g i ≤ g (i + 1)) →
      ((Finset.range L).filter (fun i => g i < g (i + 1))).card + g 0 ≤ g L := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
      intro hstep
      have hL := ih (fun i hi => hstep i (by omega))
      have hlast : g L ≤ g (L + 1) := hstep L (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hc : g L < g (L + 1)
      · rw [if_pos hc, Finset.card_insert_of_notMem (by simp)]
        omega
      · rw [if_neg hc]
        omega

/-- **A block of a word of monotone letters has boundedly many shape
increases.**  Along a descent-free stretch the shape count is non-decreasing
(`shapeCount_prefixEnd_le`) and bounded by `2 ^ W * 2 ^ W` (`shapeCount_le_sq`),
so it can strictly increase at most `2 ^ W * 2 ^ W` times, however long the
stretch is.  At every other position of the block the letter acts as an order
isomorphism between the successive ranges
(`le_iff_runTrans_blockEnd_of_shapeCount_le`). -/
theorem card_shapeIncrease_le {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) {a L : Nat}
    (hno : ∀ i : Nat, a ≤ i → i < a + L →
      REquiv (TransMonoid W) (prefixEnd word i) (prefixEnd word (i + 1))) :
    ((Finset.range L).filter (fun i =>
        shapeCount (prefixEnd word (a + i))
          < shapeCount (prefixEnd word (a + i + 1)))).card ≤ 2 ^ W * 2 ^ W := by
  classical
  set g : Nat → Nat := fun i => shapeCount (prefixEnd word (a + i)) with hg
  have hstep : ∀ i, i < L → g i ≤ g (i + 1) := by
    intro i hi
    have := shapeCount_prefixEnd_le (word := word) hmono
      (a := a + i) (b := a + i + 1) (by omega)
      (fun j hj1 hj2 => hno j (by omega) (by omega))
    simpa [hg, Nat.add_assoc] using this
  have hkey := card_strictIncrease_add_le g L hstep
  have hbdd : g L ≤ 2 ^ W * 2 ^ W := shapeCount_le_sq _
  have hfilter :
      ((Finset.range L).filter (fun i =>
        shapeCount (prefixEnd word (a + i))
          < shapeCount (prefixEnd word (a + i + 1)))).card
        = ((Finset.range L).filter (fun i => g i < g (i + 1))).card := by
    apply congrArg
    apply Finset.filter_congr
    intro i _
    simp [hg, Nat.add_assoc]
  omega

/-! ## The non-crossing instance -/

/-- Every letter of a word of `NonCrossing w` elements is monotone. -/
theorem monotone_of_forall_mem_nonCrossing {w : Nat} {word : List (TransMonoid w)}
    (hword : ∀ g ∈ word, g ∈ NonCrossing w) :
    ∀ g ∈ word, Monotone (MulOpposite.unop g) :=
  fun g hg => monotone_of_mem_nonCrossing (hword g hg)

/-- **The block picture for the non-crossing monoid.**  Along a descent-free
stretch of a word of `NonCrossing w` letters, the shape count of the range is
non-decreasing and bounded by `2 ^ w * 2 ^ w`; whenever it is stable across the
stretch, the product of the letters is an order isomorphism between the two
ranges. -/
theorem le_iff_runTrans_blockEnd_nonCrossing {w : Nat} {word : List (TransMonoid w)}
    (hword : ∀ g ∈ word, g ∈ NonCrossing w) {a b : Nat} (hab : a ≤ b)
    (hno : ∀ i : Nat, a ≤ i → i < b →
      REquiv (TransMonoid w) (prefixEnd word i) (prefixEnd word (i + 1)))
    (hsh : shapeCount (prefixEnd word b) ≤ shapeCount (prefixEnd word a))
    {p q : Config w} (hp : p ∈ rangeTrans (prefixEnd word a))
    (hq : q ∈ rangeTrans (prefixEnd word a)) :
    p ≤ q ↔ runTrans (blockEnd word a b) p ≤ runTrans (blockEnd word a b) q :=
  le_iff_runTrans_blockEnd_of_shapeCount_le
    (monotone_of_forall_mem_nonCrossing hword) hab hno hsh hp hq

end Trans

end Internal
end AllenderOQ3
