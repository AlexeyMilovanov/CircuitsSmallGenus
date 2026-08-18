import AllenderOQ3.Internal.MonoidWord

/-!
# The width-`W` transition monoid

A layer of a bounded-width cylindrical circuit acts on the finite set of Boolean
configurations `Fin W → Bool`.  Composing the layers of a word gives the
*transition monoid* of the circuit.  We package it as the multiplicative
opposite of `Function.End (Fin W → Bool)`, so that the monoid product is
"first `f`, then `g`" in *time* order; with that convention the prefix products
of a word are right multiples of one another, i.e. non-increasing in Green's
right preorder `Internal.RPreorder`.

Combining `prefixEnd_RPreorder` with `Internal.card_RDescents_le` bounds the
number of prefix positions at which the `R`-class of the transition actually
drops by the (finite) cardinality of the transition monoid.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/-- A configuration of a width-`W` layer. -/
abbrev Config (W : Nat) := Fin W → Bool

/-- The width-`W` transition monoid: self-maps of configurations, multiplied in
time order (`g * h` means "first `g`, then `h`"). -/
abbrev TransMonoid (W : Nat) := (Function.End (Config W))ᵐᵒᵖ

variable {W : Nat}

instance instFintypeTransMonoid : Fintype (TransMonoid W) :=
  Fintype.ofEquiv (Config W → Config W) MulOpposite.opEquiv

/-- Package a configuration transformation as an element of the transition
monoid. -/
def ofConfigMap (f : Config W → Config W) : TransMonoid W := MulOpposite.op f

/-- Run a transition on a configuration. -/
def runTrans (g : TransMonoid W) (x : Config W) : Config W := g.unop x

@[simp] theorem runTrans_ofConfigMap (f : Config W → Config W) (x : Config W) :
    runTrans (ofConfigMap f) x = f x := rfl

@[simp] theorem runTrans_one (x : Config W) : runTrans (1 : TransMonoid W) x = x := rfl

/-- The transition monoid multiplies in time order. -/
@[simp] theorem runTrans_mul (g h : TransMonoid W) (x : Config W) :
    runTrans (g * h) x = runTrans h (runTrans g x) := rfl

/-- The transition realised by a word of layers. -/
def wordEnd (w : List (TransMonoid W)) : TransMonoid W := w.prod

@[simp] theorem wordEnd_nil : wordEnd ([] : List (TransMonoid W)) = 1 := rfl

@[simp] theorem wordEnd_cons (g : TransMonoid W) (w : List (TransMonoid W)) :
    wordEnd (g :: w) = g * wordEnd w := List.prod_cons

/-- Concatenation of words composes their transitions. -/
theorem wordEnd_append (w₁ w₂ : List (TransMonoid W)) :
    wordEnd (w₁ ++ w₂) = wordEnd w₁ * wordEnd w₂ := List.prod_append

theorem runTrans_wordEnd_append (w₁ w₂ : List (TransMonoid W)) (x : Config W) :
    runTrans (wordEnd (w₁ ++ w₂)) x = runTrans (wordEnd w₂) (runTrans (wordEnd w₁) x) := by
  rw [wordEnd_append, runTrans_mul]

/-- The transition realised by the first `n` layers of a word. -/
def prefixEnd (w : List (TransMonoid W)) (n : Nat) : TransMonoid W := wordEnd (w.take n)

@[simp] theorem prefixEnd_zero (w : List (TransMonoid W)) : prefixEnd w 0 = 1 := by
  simp [prefixEnd]

theorem prefixEnd_length (w : List (TransMonoid W)) : prefixEnd w w.length = wordEnd w := by
  simp [prefixEnd]

/-- One more layer multiplies the prefix transition on the right. -/
theorem prefixEnd_succ (w : List (TransMonoid W)) (n : Nat) :
    prefixEnd w (n + 1) = prefixEnd w n * wordEnd ((w[n]?).toList) := by
  rw [prefixEnd, prefixEnd, List.take_add_one, wordEnd_append]

/-- **Prefix transitions descend in Green's right preorder.**  Reading one more
layer can only move the transition down the `R`-order. -/
theorem prefixEnd_RPreorder (w : List (TransMonoid W)) (n : Nat) :
    RPreorder (TransMonoid W) (prefixEnd w (n + 1)) (prefixEnd w n) :=
  ⟨wordEnd ((w[n]?).toList), prefixEnd_succ w n⟩

open Classical in
/-- **At most `|TransMonoid W|` `R`-descents along a word.**  The positions where
the `R`-class of the prefix transition strictly drops number at most the size of
the transition monoid; equivalently, a word of any length splits into at most
`|TransMonoid W| + 1` maximal `R`-constant blocks. -/
theorem card_prefix_RDescents_le (w : List (TransMonoid W)) (L : Nat) :
    (Finset.univ.filter fun i : Fin L =>
        ¬ REquiv (TransMonoid W)
            (prefixEnd w (i.castSucc : Fin (L + 1)).val)
            (prefixEnd w (i.succ : Fin (L + 1)).val)).card
      ≤ Fintype.card (TransMonoid W) := by
  refine card_RDescents_le (TransMonoid W)
    (fun i : Fin (L + 1) => prefixEnd w (i : Nat)) ?_
  intro i
  have h : ((i.succ : Fin (L + 1)) : Nat) = ((i.castSucc : Fin (L + 1)) : Nat) + 1 := by
    simp
  simp only [h]
  exact prefixEnd_RPreorder w _



/-- Prefix transitions of a word descend in Green's right preorder at any
distance, not just one step. -/
theorem prefixEnd_RPreorder_of_le (w : List (TransMonoid W)) {a b : Nat} (hab : a ≤ b) :
    RPreorder (TransMonoid W) (prefixEnd w b) (prefixEnd w a) :=
  RPreorder_of_le_nat (TransMonoid W) (prefixEnd w) (prefixEnd_RPreorder w) a b hab

/-- **Inside a descent-free block the transition stays in one `R`-class.**
Together with `card_prefix_RDescents_le` (at most `|TransMonoid W|` descents)
this is the block decomposition of a word of layer letters: the word splits into
boundedly many maximal blocks on which the prefix transition keeps one and the
same `R`-class. -/
theorem REquiv_prefixEnd_of_no_descent (w : List (TransMonoid W)) {a b : Nat} (hab : a ≤ b)
    (h : ∀ i : Nat, a ≤ i → i < b →
      REquiv (TransMonoid W) (prefixEnd w i) (prefixEnd w (i + 1))) :
    REquiv (TransMonoid W) (prefixEnd w a) (prefixEnd w b) :=
  REquiv_of_no_descent (TransMonoid W) (prefixEnd w) a b hab h

/-- Elements of the transition monoid are determined by their action on
configurations. -/
theorem transMonoid_ext {a b : TransMonoid W}
    (h : ∀ x, runTrans a x = runTrans b x) : a = b :=
  MulOpposite.unop_injective (funext h)

/-- Two transitions are equal exactly when they act in the same way. -/
theorem transMonoid_ext_iff {a b : TransMonoid W} :
    a = b ↔ ∀ x, runTrans a x = runTrans b x :=
  ⟨fun h _ => by rw [h], transMonoid_ext⟩

/-- **Green's right preorder in the transition monoid is kernel inclusion.**
Because `TransMonoid W` is the *opposite* of the endomorphism monoid, `a ≤_R b`
does not say that the range of `a` is contained in the range of `b`; it says
that the kernel (as a partition of configurations) of `b` refines that of `a`,
i.e. `b` separates at least as much as `a`. -/
theorem RPreorder_iff_ker_subset (a b : TransMonoid W) :
    RPreorder (TransMonoid W) a b ↔
      ∀ x y : Config W, runTrans b x = runTrans b y → runTrans a x = runTrans a y := by
  classical
  constructor
  · rintro ⟨c, rfl⟩ x y hxy
    simp only [runTrans_mul, hxy]
  · intro h
    refine ⟨ofConfigMap (fun z =>
      if hz : ∃ x : Config W, runTrans b x = z then runTrans a hz.choose else z), ?_⟩
    refine transMonoid_ext (fun x => ?_)
    have hex : ∃ x' : Config W, runTrans b x' = runTrans b x := ⟨x, rfl⟩
    simp only [runTrans_mul, runTrans_ofConfigMap, dif_pos hex]
    exact (h _ _ hex.choose_spec).symm

/-- **Green's right equivalence in the transition monoid is equality of
kernels.** -/
theorem REquiv_iff_ker_eq (a b : TransMonoid W) :
    REquiv (TransMonoid W) a b ↔
      ∀ x y : Config W, (runTrans a x = runTrans a y ↔ runTrans b x = runTrans b y) := by
  simp only [REquiv, RPreorder_iff_ker_subset]
  constructor
  · rintro ⟨h1, h2⟩ x y
    exact ⟨h2 x y, h1 x y⟩
  · intro h
    exact ⟨fun x y hxy => (h x y).mpr hxy, fun x y hxy => (h x y).mp hxy⟩

end Internal
end AllenderOQ3
