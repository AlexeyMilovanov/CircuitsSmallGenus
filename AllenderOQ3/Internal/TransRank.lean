import AllenderOQ3.Internal.TransitionMonoid

/-!
# Rank of a transition and the sharp `R`-descent bound

`card_prefix_RDescents_le` bounds the number of `R`-descents along a word of
layer letters by `|TransMonoid W|`, which is doubly exponential in the width and
therefore useless for a *polynomial* size bound.  This file replaces it by the
sharp bound.

The **rank** of a transition is the number of configurations it can produce.
Because `TransMonoid W` is the opposite of the endomorphism monoid, Green's
right preorder is kernel inclusion (`RPreorder_iff_ker_subset`), so:

* `rankTrans_le_of_RPreorder` — going down the `R`-order can only lose rank;
* `rankTrans_lt_of_descent` — a *strict* `R`-descent loses at least one unit of
  rank;
* `card_prefix_RDescents_le_card_config` — hence a word has at most
  `|Config W| = 2 ^ W` `R`-descents, however long it is.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {W : Nat}

open Classical in
/-- The rank of a transition: the number of configurations in its range. -/
noncomputable def rankTrans (g : TransMonoid W) : Nat :=
  (Finset.univ.image (runTrans g)).card

open Classical in
theorem rankTrans_pos (g : TransMonoid W) : 0 < rankTrans g := by
  classical
  refine Finset.card_pos.mpr ⟨runTrans g (fun _ => false), ?_⟩
  exact Finset.mem_image.mpr ⟨fun _ => false, Finset.mem_univ _, rfl⟩

theorem rankTrans_le_card (g : TransMonoid W) : rankTrans g ≤ Fintype.card (Config W) := by
  classical
  simpa [rankTrans, Finset.card_univ] using
    (Finset.card_image_le (s := (Finset.univ : Finset (Config W))) (f := runTrans g))

/-- The range of a product is the image of the range of the left factor. -/
theorem image_runTrans_mul (b c : TransMonoid W) :
    Finset.univ.image (runTrans (b * c))
      = (Finset.univ.image (runTrans b)).image (runTrans c) := by
  classical
  rw [Finset.image_image]
  rfl

/-- Going down Green's right preorder can only lose rank. -/
theorem rankTrans_le_of_RPreorder {a b : TransMonoid W}
    (h : RPreorder (TransMonoid W) a b) : rankTrans a ≤ rankTrans b := by
  classical
  obtain ⟨c, rfl⟩ := h
  rw [rankTrans, rankTrans, image_runTrans_mul]
  exact Finset.card_image_le

/-- **A strict `R`-descent loses rank.** -/
theorem rankTrans_lt_of_descent {a b : TransMonoid W}
    (h : RPreorder (TransMonoid W) a b) (hne : ¬ REquiv (TransMonoid W) a b) :
    rankTrans a < rankTrans b := by
  classical
  rcases lt_or_eq_of_le (rankTrans_le_of_RPreorder h) with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨c, rfl⟩ := h
    -- equal ranks force `runTrans c` to be injective on the range of `b`
    have hcard : ((Finset.univ.image (runTrans b)).image (runTrans c)).card
        = (Finset.univ.image (runTrans b)).card := by
      rw [← image_runTrans_mul]
      exact heq
    have hinj : Set.InjOn (runTrans c) ↑(Finset.univ.image (runTrans b)) :=
      Finset.injOn_of_card_image_eq hcard
    refine hne ⟨⟨c, rfl⟩, ?_⟩
    refine (RPreorder_iff_ker_subset b (b * c)).mpr ?_
    intro x y hxy
    refine hinj ?_ ?_ (by simpa using hxy)
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)

open Classical in
/-- **The sharp `R`-descent bound.**  Along the prefix transitions of any word of
layer letters, the positions where the `R`-class strictly drops number at most
`|Config W| = 2 ^ W` — exponentially better than the generic bound
`|TransMonoid W|`, and the bound that makes a polynomial-size recogniser
possible. -/
theorem card_prefix_RDescents_le_card_config (w : List (TransMonoid W)) (L : Nat) :
    (Finset.univ.filter fun i : Fin L =>
        ¬ REquiv (TransMonoid W) (prefixEnd w i.val) (prefixEnd w (i.val + 1))).card
      ≤ Fintype.card (Config W) := by
  classical
  set K := Fintype.card (Config W) with hK
  have hmono : ∀ a b : Nat, a ≤ b →
      rankTrans (prefixEnd w b) ≤ rankTrans (prefixEnd w a) := fun a b hab =>
    rankTrans_le_of_RPreorder (prefixEnd_RPreorder_of_le w hab)
  have hdrop : ∀ i : Nat, ¬ REquiv (TransMonoid W) (prefixEnd w i) (prefixEnd w (i + 1)) →
      rankTrans (prefixEnd w (i + 1)) < rankTrans (prefixEnd w i) := by
    intro i hi
    refine rankTrans_lt_of_descent (prefixEnd_RPreorder w i) ?_
    intro hcon
    exact hi (REquiv_symm (TransMonoid W) _ _ hcon)
  have hcard : (Finset.univ.filter fun i : Fin L =>
      ¬ REquiv (TransMonoid W) (prefixEnd w i.val) (prefixEnd w (i.val + 1))).card
      ≤ (Finset.Icc 1 K).card := by
    refine Finset.card_le_card_of_injOn
      (fun i : Fin L => rankTrans (prefixEnd w (i.val + 1))) ?_ ?_
    · intro i _
      refine Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨rankTrans_pos _, ?_⟩)
      exact rankTrans_le_card _
    · intro i hi j hj hij
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi hj
      by_contra hne
      -- the later of the two descents would have to lose rank, but the rank is
      -- already constant between the two positions
      have key : ∀ p q : Fin L, p < q →
          ¬ REquiv (TransMonoid W) (prefixEnd w q.val) (prefixEnd w (q.val + 1)) →
          rankTrans (prefixEnd w (p.val + 1)) ≠ rankTrans (prefixEnd w (q.val + 1)) := by
        intro p q hpq hqd heq
        have h1 : rankTrans (prefixEnd w q.val) ≤ rankTrans (prefixEnd w (p.val + 1)) :=
          hmono _ _ (by exact_mod_cast Nat.succ_le_of_lt hpq)
        have h2 := hdrop q.val hqd
        omega
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact key i j hlt hj.2 hij
      · exact key j i hgt hi.2 hij.symm
  simpa using hcard

open Classical in
/-- The sharp descent bound, spelled out: at most `2 ^ W` descents. -/
theorem card_prefix_RDescents_le_two_pow (w : List (TransMonoid W)) (L : Nat) :
    (Finset.univ.filter fun i : Fin L =>
        ¬ REquiv (TransMonoid W) (prefixEnd w i.val) (prefixEnd w (i.val + 1))).card
      ≤ 2 ^ W := by
  have h := card_prefix_RDescents_le_card_config w L
  simpa using h

end Internal
end AllenderOQ3
