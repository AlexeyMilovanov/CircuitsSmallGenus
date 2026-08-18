import AllenderOQ3.Internal.MonotoneShape

/-!
# The aperiodic cascade coordinate: a globally monotone rank/shape pair

`cascade_aperiodic_layer` (in `AllenderOQ3.Internal.CascadeAperiodic`) evaluates a
state sequence `z` by guess-and-verify, provided the number of positions at which
`z` *changes* is bounded by a constant `K`, uniformly in the length of the word.
This file supplies the corresponding bounded-change property for a rank/shape
coordinate of words of monotone letters — in particular for words over
`NonCrossing w`.  (Feeding the coordinate to `cascade_aperiodic_layer` in
addition requires a local update rule for it; only the change bound and the
resulting block structure are established here.)

The coordinate is the pair

* `rankTrans (prefixEnd word t)` — the number of configurations still reachable,
  which is non-increasing in `t` (`rankTrans_le_of_RPreorder`), and
* `shapeCount (prefixEnd word t)` — the number of comparable pairs in the range,
  which is non-decreasing along a stretch on which the rank (equivalently, by
  `rankTrans_lt_of_descent`, the `R`-class) does not drop
  (`shapeCount_prefixEnd_le`).

Neither coordinate alone is monotone along the whole word: a rank descent can
destroy comparabilities.  The *lexicographic* combination

  `shapeMeasure = (2 ^ W - rank) * (2 ^ W * 2 ^ W + 1) + shape`

is monotone along the whole word (`shapeMeasure_prefixEnd_le`), because one unit
of rank outweighs the entire range of the shape count.  Being bounded
(`shapeMeasure_le`), it can strictly increase only boundedly often, and it
strictly increases at every position at which the pair changes.  Hence

* `card_shapeCoord_changes_le` — the rank/shape pair changes at most
  `2 ^ W * (2 ^ W * 2 ^ W + 1) + 2 ^ W * 2 ^ W` times, however long the word is.

The pair is packaged as a `Fintype`-valued coordinate `shapeCoord`, which is the
form `cascade_aperiodic_layer` consumes.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/-! ## A bounded monotone measure bounds the number of changes -/

/-- A `Nat`-valued measure that never decreases along a sequence, and strictly
increases at every position where the sequence changes, bounds the number of
changes by its total variation. -/
theorem card_changes_range_add_le {Z : Type} [DecidableEq Z] (zz : Nat → Z)
    (mu : Z → Nat) :
    ∀ len : Nat,
      (∀ i, i < len → mu (zz i) ≤ mu (zz (i + 1))) →
      (∀ i, i < len → zz i ≠ zz (i + 1) → mu (zz i) < mu (zz (i + 1))) →
      ((Finset.range len).filter (fun i => zz i ≠ zz (i + 1))).card + mu (zz 0)
        ≤ mu (zz len) := by
  intro len
  induction len with
  | zero => simp
  | succ len ih =>
      intro hstep hchange
      have hL := ih (fun i hi => hstep i (by omega)) (fun i hi => hchange i (by omega))
      have hlast : mu (zz len) ≤ mu (zz (len + 1)) := hstep len (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hc : zz len ≠ zz (len + 1)
      · have hlt : mu (zz len) < mu (zz (len + 1)) := hchange len (by omega) hc
        rw [if_pos hc, Finset.card_insert_of_notMem (by simp)]
        omega
      · rw [if_neg hc]
        omega

/-- The `Fin`-indexed form of `card_changes_range_add_le`: a bounded monotone
measure bounds the number of changes of the sequence by the bound itself.  This
is exactly the `h_changes` hypothesis of `cascade_aperiodic_layer`. -/
theorem card_changes_le_of_measure {Z : Type} [DecidableEq Z] {len B : Nat}
    (z : Fin (len + 1) → Z) (mu : Z → Nat)
    (hstep : ∀ i : Fin len, mu (z i.castSucc) ≤ mu (z i.succ))
    (hchange : ∀ i : Fin len, z i.castSucc ≠ z i.succ → mu (z i.castSucc) < mu (z i.succ))
    (hbdd : ∀ i : Fin (len + 1), mu (z i) ≤ B) :
    (Finset.univ.filter (fun i : Fin len => z i.castSucc ≠ z i.succ)).card ≤ B := by
  classical
  set zz : Nat → Z := fun k => z ⟨min k len, by omega⟩ with hzz
  have hcast : ∀ i : Fin len, zz i.val = z i.castSucc := by
    intro i
    have : min i.val len = i.val := by omega
    simp only [hzz, this]
    rfl
  have hsucc : ∀ i : Fin len, zz (i.val + 1) = z i.succ := by
    intro i
    have hi := i.isLt
    have : min (i.val + 1) len = i.val + 1 := by omega
    simp only [hzz, this]
    rfl
  have hstep' : ∀ i, i < len → mu (zz i) ≤ mu (zz (i + 1)) := by
    intro i hi
    rw [hcast ⟨i, hi⟩, hsucc ⟨i, hi⟩]
    exact hstep ⟨i, hi⟩
  have hchange' : ∀ i, i < len → zz i ≠ zz (i + 1) → mu (zz i) < mu (zz (i + 1)) := by
    intro i hi hne
    rw [hcast ⟨i, hi⟩, hsucc ⟨i, hi⟩] at hne ⊢
    exact hchange ⟨i, hi⟩ hne
  have hkey := card_changes_range_add_le zz mu len hstep' hchange'
  have hlen : mu (zz len) ≤ B := by
    have : min len len = len := by omega
    simp only [hzz, this]
    exact hbdd _
  have hcard :
      (Finset.univ.filter (fun i : Fin len => z i.castSucc ≠ z i.succ)).card
        = ((Finset.range len).filter (fun i => zz i ≠ zz (i + 1))).card := by
    refine Finset.card_bij (fun (i : Fin len) _ => i.val) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_range.mpr i.isLt, ?_⟩
      rw [hcast i, hsucc i]
      exact hi.2
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      refine ⟨⟨k, hk.1⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hcast ⟨k, hk.1⟩, ← hsucc ⟨k, hk.1⟩]
      exact hk.2
  omega

/-! ## The rank/shape coordinate of a prefix -/

section Coordinate

variable {W : Nat}

/-- The rank/shape coordinate of a transition, as an element of a finite type:
the number of reachable configurations together with the number of comparable
pairs among them. -/
noncomputable def shapeCoord (g : TransMonoid W) :
    Fin (2 ^ W + 1) × Fin (2 ^ W * 2 ^ W + 1) :=
  (⟨rankTrans g, by
      have h := rankTrans_le_card g
      simp only [Config, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
      omega⟩,
   ⟨shapeCount g, by have := shapeCount_le_sq g; omega⟩)

theorem shapeCoord_eq_iff {a b : TransMonoid W} :
    shapeCoord a = shapeCoord b ↔ rankTrans a = rankTrans b ∧ shapeCount a = shapeCount b := by
  constructor
  · intro h
    exact ⟨congrArg Fin.val (congrArg Prod.fst h), congrArg Fin.val (congrArg Prod.snd h)⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- The lexicographic measure attached to the rank/shape coordinate: one unit of
rank outweighs the whole range of the shape count. -/
noncomputable def shapeMeasure (p : Fin (2 ^ W + 1) × Fin (2 ^ W * 2 ^ W + 1)) : Nat :=
  (2 ^ W - p.1.val) * (2 ^ W * 2 ^ W + 1) + p.2.val

theorem shapeMeasure_le (p : Fin (2 ^ W + 1) × Fin (2 ^ W * 2 ^ W + 1)) :
    shapeMeasure p ≤ 2 ^ W * (2 ^ W * 2 ^ W + 1) + 2 ^ W * 2 ^ W := by
  have h1 : p.1.val ≤ 2 ^ W := by have := p.1.isLt; omega
  have h2 : p.2.val ≤ 2 ^ W * 2 ^ W := by have := p.2.isLt; omega
  have h3 : (2 ^ W - p.1.val) * (2 ^ W * 2 ^ W + 1) ≤ 2 ^ W * (2 ^ W * 2 ^ W + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [shapeMeasure]
  omega

/-- The rank of a prefix never increases. -/
theorem rankTrans_prefixEnd_succ_le (word : List (TransMonoid W)) (t : Nat) :
    rankTrans (prefixEnd word (t + 1)) ≤ rankTrans (prefixEnd word t) :=
  rankTrans_le_of_RPreorder (prefixEnd_RPreorder word t)

/-- If the rank does not drop at a position, the `R`-class does not either. -/
theorem REquiv_prefixEnd_succ_of_rank_eq {word : List (TransMonoid W)} {t : Nat}
    (h : rankTrans (prefixEnd word (t + 1)) = rankTrans (prefixEnd word t)) :
    REquiv (TransMonoid W) (prefixEnd word t) (prefixEnd word (t + 1)) := by
  by_contra hne
  have hne' : ¬ REquiv (TransMonoid W) (prefixEnd word (t + 1)) (prefixEnd word t) :=
    fun hc => hne (REquiv_symm (TransMonoid W) _ _ hc)
  have := rankTrans_lt_of_descent (prefixEnd_RPreorder word t) hne'
  omega

/-- **The rank/shape measure is monotone along the whole word.**  Either the rank
drops, and the leading term grows by more than the shape count can ever be, or
the rank is stable, in which case the `R`-class is stable and the shape count is
non-decreasing. -/
theorem shapeMeasure_prefixEnd_le {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) (t : Nat) :
    shapeMeasure (shapeCoord (prefixEnd word t))
      ≤ shapeMeasure (shapeCoord (prefixEnd word (t + 1))) := by
  have hrank := rankTrans_prefixEnd_succ_le word t
  have hr0 : rankTrans (prefixEnd word t) ≤ 2 ^ W := by
    have h := rankTrans_le_card (prefixEnd word t)
    simp only [Config, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
    omega
  have hs0 := shapeCount_le_sq (prefixEnd word t)
  have hs1 := shapeCount_le_sq (prefixEnd word (t + 1))
  simp only [shapeMeasure, shapeCoord]
  rcases eq_or_lt_of_le hrank with heq | hlt
  · have hR := REquiv_prefixEnd_succ_of_rank_eq heq
    have hshape : shapeCount (prefixEnd word t) ≤ shapeCount (prefixEnd word (t + 1)) :=
      shapeCount_prefixEnd_le hmono (a := t) (b := t + 1) (by omega)
        (fun i hi1 hi2 => by
          have : i = t := by omega
          subst this
          exact hR)
    simp only [heq]
    omega
  · have hstep : (2 ^ W - rankTrans (prefixEnd word t)) + 1
        ≤ 2 ^ W - rankTrans (prefixEnd word (t + 1)) := by omega
    have hmul : ((2 ^ W - rankTrans (prefixEnd word t)) + 1) * (2 ^ W * 2 ^ W + 1)
        ≤ (2 ^ W - rankTrans (prefixEnd word (t + 1))) * (2 ^ W * 2 ^ W + 1) :=
      Nat.mul_le_mul_right _ hstep
    have hexp : ((2 ^ W - rankTrans (prefixEnd word t)) + 1) * (2 ^ W * 2 ^ W + 1)
        = (2 ^ W - rankTrans (prefixEnd word t)) * (2 ^ W * 2 ^ W + 1)
          + (2 ^ W * 2 ^ W + 1) := by ring
    omega

/-- **The measure strictly increases whenever the coordinate changes.** -/
theorem shapeMeasure_prefixEnd_lt {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) {t : Nat}
    (hne : shapeCoord (prefixEnd word t) ≠ shapeCoord (prefixEnd word (t + 1))) :
    shapeMeasure (shapeCoord (prefixEnd word t))
      < shapeMeasure (shapeCoord (prefixEnd word (t + 1))) := by
  have hrank := rankTrans_prefixEnd_succ_le word t
  have hr0 : rankTrans (prefixEnd word t) ≤ 2 ^ W := by
    have h := rankTrans_le_card (prefixEnd word t)
    simp only [Config, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
    omega
  have hs0 := shapeCount_le_sq (prefixEnd word t)
  have hs1 := shapeCount_le_sq (prefixEnd word (t + 1))
  rcases eq_or_lt_of_le hrank with heq | hlt
  · have hR := REquiv_prefixEnd_succ_of_rank_eq heq
    have hshape : shapeCount (prefixEnd word t) ≤ shapeCount (prefixEnd word (t + 1)) :=
      shapeCount_prefixEnd_le hmono (a := t) (b := t + 1) (by omega)
        (fun i hi1 hi2 => by
          have : i = t := by omega
          subst this
          exact hR)
    have hsne : shapeCount (prefixEnd word t) ≠ shapeCount (prefixEnd word (t + 1)) := by
      intro hs
      exact hne (shapeCoord_eq_iff.mpr ⟨heq.symm, hs⟩)
    simp only [shapeMeasure, shapeCoord, heq]
    omega
  · have hstep : (2 ^ W - rankTrans (prefixEnd word t)) + 1
        ≤ 2 ^ W - rankTrans (prefixEnd word (t + 1)) := by omega
    have hmul : ((2 ^ W - rankTrans (prefixEnd word t)) + 1) * (2 ^ W * 2 ^ W + 1)
        ≤ (2 ^ W - rankTrans (prefixEnd word (t + 1))) * (2 ^ W * 2 ^ W + 1) :=
      Nat.mul_le_mul_right _ hstep
    have hexp : ((2 ^ W - rankTrans (prefixEnd word t)) + 1) * (2 ^ W * 2 ^ W + 1)
        = (2 ^ W - rankTrans (prefixEnd word t)) * (2 ^ W * 2 ^ W + 1)
          + (2 ^ W * 2 ^ W + 1) := by ring
    simp only [shapeMeasure, shapeCoord]
    omega

/-- **The rank/shape coordinate of the prefixes of a word of monotone letters
changes only boundedly often**, however long the word is.  This is the
`h_changes` hypothesis of `cascade_aperiodic_layer` for the aperiodic (shape)
layer of the cascade. -/
theorem card_shapeCoord_changes_le {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) (len : Nat) :
    (Finset.univ.filter (fun i : Fin len =>
        shapeCoord (prefixEnd word i.castSucc.val)
          ≠ shapeCoord (prefixEnd word i.succ.val))).card
      ≤ 2 ^ W * (2 ^ W * 2 ^ W + 1) + 2 ^ W * 2 ^ W := by
  classical
  refine card_changes_le_of_measure
    (z := fun i : Fin (len + 1) => shapeCoord (prefixEnd word i.val))
    (mu := shapeMeasure) ?_ ?_ ?_
  · intro i
    simp only [Fin.val_succ, Fin.val_castSucc]
    exact shapeMeasure_prefixEnd_le hmono _
  · intro i hne
    simp only [Fin.val_succ, Fin.val_castSucc] at hne ⊢
    exact shapeMeasure_prefixEnd_lt hmono hne
  · intro i
    exact shapeMeasure_le _

/-- **A stretch on which the rank/shape coordinate is constant is an
order-isomorphism stretch.**  If the pair `(rank, shape)` does not change
between the prefix positions `a` and `b`, then no `R`-descent happens in between,
so the product of the intervening letters is a bijection from the range at `a`
onto the range at `b`, and it both preserves and reflects the order.  Together
with `card_shapeCoord_changes_le` this splits any word of monotone letters into a
bounded number of maximal order-isomorphism stretches. -/
theorem orderIso_blockEnd_of_shapeCoord_const {word : List (TransMonoid W)}
    (hmono : ∀ g ∈ word, Monotone (MulOpposite.unop g)) {a b : Nat} (hab : a ≤ b)
    (hconst : ∀ t, a ≤ t → t ≤ b →
      shapeCoord (prefixEnd word t) = shapeCoord (prefixEnd word a)) :
    Set.BijOn (runTrans (blockEnd word a b))
        ↑(rangeTrans (prefixEnd word a)) ↑(rangeTrans (prefixEnd word b)) ∧
      ∀ p ∈ rangeTrans (prefixEnd word a), ∀ q ∈ rangeTrans (prefixEnd word a),
        (p ≤ q ↔ runTrans (blockEnd word a b) p ≤ runTrans (blockEnd word a b) q) := by
  have hno : ∀ i : Nat, a ≤ i → i < b →
      REquiv (TransMonoid W) (prefixEnd word i) (prefixEnd word (i + 1)) := by
    intro i hi1 hi2
    have h1 := (shapeCoord_eq_iff.mp (hconst i hi1 (by omega))).1
    have h2 := (shapeCoord_eq_iff.mp (hconst (i + 1) (by omega) (by omega))).1
    exact REquiv_prefixEnd_succ_of_rank_eq (by omega)
  have hsh : shapeCount (prefixEnd word b) ≤ shapeCount (prefixEnd word a) :=
    le_of_eq (shapeCoord_eq_iff.mp (hconst b hab (le_refl b))).2
  refine ⟨bijOn_rangeTrans_blockEnd word hab hno, fun p hp q hq => ?_⟩
  exact le_iff_runTrans_blockEnd_of_shapeCount_le hmono hab hno hsh hp hq

/-- The non-crossing instance: for a word of `NonCrossing w` letters the
rank/shape coordinate changes at most `2 ^ w * (2 ^ w * 2 ^ w + 1) + 2 ^ w * 2 ^ w`
times. -/
theorem card_shapeCoord_changes_le_nonCrossing {w : Nat} {word : List (TransMonoid w)}
    (hword : ∀ g ∈ word, g ∈ NonCrossing w) (len : Nat) :
    (Finset.univ.filter (fun i : Fin len =>
        shapeCoord (prefixEnd word i.castSucc.val)
          ≠ shapeCoord (prefixEnd word i.succ.val))).card
      ≤ 2 ^ w * (2 ^ w * 2 ^ w + 1) + 2 ^ w * 2 ^ w :=
  card_shapeCoord_changes_le (monotone_of_forall_mem_nonCrossing hword) len

end Coordinate

end Internal
end AllenderOQ3
