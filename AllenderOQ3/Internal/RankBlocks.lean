import AllenderOQ3.Internal.TransRank

/-!
# The rank labels the `R`-blocks of a word

Along the prefix transitions of a word the rank `rankTrans` (the number of
configurations in the image) is non-increasing, takes values in `[1, 2 ^ W]`,
and strictly drops at every `R`-descent.  Consequently two prefix positions with
the same rank are `R`-equivalent, so the rank *value* is a label for the maximal
`R`-constant blocks of the word: there are at most `2 ^ W` such blocks and each
of them is the set of positions carrying one rank value, an interval.

This is the block decomposition used by the word-problem recogniser: the block
boundaries can be guessed by guessing, for each of the constantly many rank
values, the first and last position carrying it.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {W : Nat}

/-- The rank of the prefix transitions is non-increasing. -/
theorem rankTrans_prefixEnd_antitone (w : List (TransMonoid W)) {a b : Nat} (hab : a ≤ b) :
    rankTrans (prefixEnd w b) ≤ rankTrans (prefixEnd w a) :=
  rankTrans_le_of_RPreorder (prefixEnd_RPreorder_of_le w hab)

/-- The rank of a prefix transition is between `1` and `2 ^ W`. -/
theorem rankTrans_prefixEnd_mem (w : List (TransMonoid W)) (a : Nat) :
    1 ≤ rankTrans (prefixEnd w a) ∧ rankTrans (prefixEnd w a) ≤ 2 ^ W := by
  refine ⟨rankTrans_pos _, ?_⟩
  have h := rankTrans_le_card (prefixEnd w a)
  simpa using h

/-- **The rank labels the blocks.**  Two prefix positions of a word carrying the
same rank are `R`-equivalent, and so is every position between them. -/
theorem REquiv_prefixEnd_of_rankTrans_eq (w : List (TransMonoid W)) {a b : Nat} (hab : a ≤ b)
    (h : rankTrans (prefixEnd w a) = rankTrans (prefixEnd w b)) :
    REquiv (TransMonoid W) (prefixEnd w a) (prefixEnd w b) := by
  refine REquiv_prefixEnd_of_no_descent w hab ?_
  intro i hai hib
  by_contra hne
  have hdrop : rankTrans (prefixEnd w (i + 1)) < rankTrans (prefixEnd w i) :=
    rankTrans_lt_of_descent (prefixEnd_RPreorder w i)
      (fun hcon => hne (REquiv_symm (TransMonoid W) _ _ hcon))
  have h1 : rankTrans (prefixEnd w i) ≤ rankTrans (prefixEnd w a) :=
    rankTrans_prefixEnd_antitone w hai
  have h2 : rankTrans (prefixEnd w b) ≤ rankTrans (prefixEnd w (i + 1)) :=
    rankTrans_prefixEnd_antitone w hib
  omega

/-- The positions carrying a given rank form an interval: if `a ≤ i ≤ b` and the
ranks at `a` and `b` agree, then the rank at `i` is that same value. -/
theorem rankTrans_prefixEnd_eq_of_between (w : List (TransMonoid W)) {a i b : Nat}
    (hai : a ≤ i) (hib : i ≤ b) (h : rankTrans (prefixEnd w a) = rankTrans (prefixEnd w b)) :
    rankTrans (prefixEnd w i) = rankTrans (prefixEnd w a) := by
  have h1 : rankTrans (prefixEnd w i) ≤ rankTrans (prefixEnd w a) :=
    rankTrans_prefixEnd_antitone w hai
  have h2 : rankTrans (prefixEnd w b) ≤ rankTrans (prefixEnd w i) :=
    rankTrans_prefixEnd_antitone w hib
  omega

end Internal
end AllenderOQ3
