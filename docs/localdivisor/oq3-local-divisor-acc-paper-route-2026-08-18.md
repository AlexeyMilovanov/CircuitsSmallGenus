# An elementary local-divisor route for the remaining OQ3 word problem

## Verdict

For the theorem now proved on paper for the cylindrical monoid — **every local
subgroup is abelian** — the full holonomy cascade is not needed.  There is a
finite-monoid induction using local divisors.  Its circuit part is a
guess-and-verify construction of exactly the kind already supported by
`ACCJoin`, `ACCNot`, modulus lifting, and `MonoidWordACCGen`.

The minimal missing result is the **marked local-divisor compression lemma** in
Section 4 below.  Once that lemma is available, induction on the cardinality of
the monoid proves `MonoidWordACCGen M` for every finite monoid all of whose
subgroups are abelian.  Applying `monoidWordACC_of_gen` closes
`monoidWordACC_nonCrossing` after the new paper proof of abelianity is imported.

The exact replacement for Barrington--Therien is therefore the following much
narrower theorem.

> **Abelian-local fixed-word theorem.**  Let `M` be a finite monoid.  Assume
> that for every idempotent `e`, the unit group of the local monoid `e M e`
> is abelian (equivalently, every subgroup of `M` is abelian).  Then
> `MonoidWordACCGen M`.

This formulation talks only about the fixed monoid word evaluator already used
by OQ3.  It does not assert the general Barrington--Therien characterization,
does not use Krohn--Rhodes or holonomy, and does not cover nonabelian solvable
groups.  Sections 2--5 give a constructive proof.

For Lean, the hypothesis can be kept first-order and independent of a library
of Green relations.  One convenient definition is: whenever `e^2=e`, and
`a,a'` and `b,b'` are two pairs satisfying

`e a=a e=a`, `e a'=a' e=a'`, `a a'=a' a=e`, and the analogous equations
for `b,b'`,

then `a b=b a`.  These are exactly two invertible elements of the local monoid
with identity `e`.  This predicate is equivalent to the displayed
“all subgroups abelian” condition and is particularly easy to transport
through the explicit group-lifting argument below.

This route proves the abelian-local special case needed by OQ3.  For arbitrary
solvable, possibly nonabelian local groups, one still needs a group-extension
argument (or Barrington--Therien).

## 1. Why the existing easy cases do not by themselves suffice

The current Lean development proves quantitative word-problem results for:

* finite commutative monoids (`monoidWordACCGen_of_comm`);
* `R`-trivial and `L`-trivial monoids;
* reset monoids;
* submonoids, quotients, and hence divisors.

Those classes do not exhaust finite monoids with abelian subgroups.  In
particular, an arbitrary aperiodic monoid need be neither `R`- nor `L`-trivial.
Likewise, decomposing a word only at Green-rank drops fails at rank one: an
arbitrarily long reset trajectory can remain in one rank class.  This is the
already formalized obstruction to the old epoch/F3c shortcut.

What is missing is not another bounded-change coordinate.  It is a closure
principle that recursively exposes a smaller monoid even while the word stays
at the same rank.  A local divisor supplies exactly that.

## 2. The local divisor

Let `M` be a finite monoid and let `c in M`.  Define

`M_c = cM intersect Mc`.

An element of `M_c` can be written both as `x c` and as `c y`.  Define

`(x c) circle (c y) = x c y`.

This is well-defined and associative, and `c` is its identity.  Thus `M_c` is
a monoid, called the local divisor at `c`.

If `c` is not a unit, then `|M_c| < |M|`.  Indeed `M_c subseteq cM`; equality
`|cM|=|M|` would give `cM=M`, hence a right inverse of `c`, which in a finite
monoid makes `c` a unit.

The local divisor is a divisor of `M`.  Put

`S_c = {x in M : c x in M c}`.

This is a submonoid, and

`theta : S_c -> M_c`, `theta(x)=c x`,

is a surjective monoid homomorphism, where the codomain multiplication is
`circle`.  If `c x=a c`, then

`theta(x) circle theta(y) = (a c) circle (c y) = a c y = c x y`.

Consequently the property “all subgroups are abelian” passes from `M` to
`M_c`.  Here is a complete proof of the finite-semigroup fact used in that
sentence; it is not being left as another black box.

Let `phi : S -> T` be a surjective homomorphism of finite monoids and let `H`
be a subgroup of `T`.  The identity `e_H` of `H` need not be the identity of
`T`.  Thus `U=phi^{-1}(H)` is in general a subsemigroup, not a submonoid.  Take
a minimal nonempty two-sided ideal `I` of the finite semigroup `U`.  The image
`phi(I)` is a nonempty ideal of the group `H`, hence is all of `H`.  A finite
semigroup contains an idempotent, so choose an idempotent `f in I`.  Its image
is the only idempotent of `H`, namely `e_H`.

The set `f I f`, with the original multiplication, is a group with identity
`f`.  Indeed, for `z in f I f`, minimality gives

`U^1 z U^1 = I`,

where `U^1` means that a formal identity is allowed.  In particular
`f=a z b` for some `a,b in U^1`.  Put `A=f a f` and `B=f b f`.  In the finite
local monoid `f U^1 f` we have `A z B=f`.  The element `A z` has right inverse
`B`, hence is a unit (one-sided inverses are two-sided in a finite monoid).
Writing `q=(A z)^{-1}`, the element `A` has right inverse `z q`, so `A` is a
unit; and `z` has left inverse `q A`, so `z` is a unit.  From `A z B=f` we get
`B=(A z)^{-1}=z^{-1}A^{-1}`, and hence `B A=z^{-1}`.  This inverse belongs to
`f I f`, because `f in I` and `I` is an ideal.  Thus `f I f` is a group.
Finally, for every `h in H`, choose `y in I` with
`phi(y)=h`.  Then `f y f in f I f` and

`phi(f y f)=e_H h e_H=h`.

Thus every subgroup of `T` is a quotient of a subgroup of `S`.  In particular,
if all subgroups of `S` are abelian, so are all subgroups of `T`.  Applying
this first to a submonoid of `M` and then to its quotient proves the claimed
inheritance for the divisor `M_c`.

## 3. The algebraic word factorization

Let a word over `M` use a distinguished letter `c` and otherwise letters from
a submonoid `N`.  Write its occurrences of `c` as

`w = u_0 c u_1 c ... c u_k`,

where every `u_i` is an `N`-word, and write the same symbols for their products
in `N`.

For every internal gap define

`q_i = c u_i c in M_c`  (`1 <= i < k`).

Then

`q_1 circle ... circle q_{k-1}`

is the original-M element

`c u_1 c ... c u_{k-1} c`.

The identity of `M_c` is `c`, so this remains correct for one occurrence of
`c`: the empty local product is `c`.  Therefore, if the word contains a `c`,

`prod_M(w) = u_0 * prod_{M_c}(q_i) * u_k`.

If it contains no `c`, its product is simply computed in `N`.

## 4. Marked local-divisor compression lemma

### Statement

Fix a finite monoid `M`, a nonunit `c`, and a finite set `B subseteq M` with
`N=<B>` and `c notin N`.  Suppose

`MonoidWordACCGen N`

and

`MonoidWordACCGen M_c`.

Then the word product for words over `B union {1,c}` has the generalized ACC
property, with depth and size exponent depending only on the fixed finite
data.

### Derived local-divisor word

For a word `a_0,...,a_{L-1}` over `B union {1,c}`, make an `M_c`-valued word
`v_0,...,v_{L-1}` as follows.

* If `t` is an occurrence of `c` and the next occurrence is `s>t`, put

  `v_t = c (a_{t+1} ... a_{s-1}) c`.

* At every other position put `v_t=c`, the identity of `M_c`.

If the `c` positions are `p_1<...<p_k`, then

`prod_circle(v_0,...,v_{L-1}) = c u_1 c ... c u_{k-1} c`.

**The construction is block-local.**  To build the output circuit for a
requested block `[start+a,start+b)`, first restrict to exactly that block and
then define “next occurrence” only up to its right endpoint.  Equivalently,
define a fresh total derived-letter function for this `(a,b)`, equal to the
local identity `c` outside the block, invoke the `M_c` evaluator on its full
length, and retain that one circuit.  The output family is allowed to choose a
different auxiliary derived word for each `(a,b)`.

A single derived word made from the whole ambient window would be wrong.  For
example, take the finite Rees quotient of the free monoid on `{a,c}` in which
all words of length at least three are identified with zero.  In the ambient
word `c a c`, the subblock `c a` contains only one `c`, so its local middle
product must be the identity `c` and its product is `c a`.  A globally defined
“next `c`” would see the `c` just outside the subblock, put `c a c=0` at the
first position, and incorrectly return zero.  This is the principal endpoint
condition that the Lean statement of the compression lemma must expose.

### Recognizing one derived letter

For fixed `t` and `q in M_c`, the predicate `v_t=q` is an OR of the following
constant-depth tests.

1. `a_t != c`, in which case `q=c`.
2. `a_t=c` and there is no later `c`, again with `q=c`.
3. For a guessed `s>t` and `u in N`:

   * `a_t=c` and `a_s=c`;
   * every position strictly between them is different from `c`;
   * the `N`-product of that open interval is `u`;
   * `c u c=q`.

Map occurrences of `c` temporarily to `1_N`; this gives an `N`-valued word on
which the recursive `MonoidWordACCGen N` circuits recognize every fixed block
product.  The “no intervening `c`” conjunction makes that product the genuine
product of the gap.  There are only `O(L*|N|)` disjuncts for one derived
letter.  Unbounded AND/OR joins therefore give constant depth and polynomial
size.

The generalized rather than the original `MonoidWordACC` interface is
essential here.  The derived-letter recognizers already contain the recursive
`N` circuits.  `MonoidWordACCGen M_c` accepts recognizers of this new constant
depth, and its output modulus can be chosen divisible by the modulus used for
the `N` circuits.

### Recovering the full product

The final predicate `prod_M(w)=g` is an OR of:

* the no-`c` case, together with the `N`-product of the whole word; and
* choices of first and last `c` positions `p<=r`, products `u_0,u_k in N`, and
  `h in M_c`, checking

  `u_0 * h * u_k = g`,

  where `u_0` is the prefix product before `p`, `u_k` the suffix product after
  `r`, and `h` the product of the entire derived word.

“First” and “last” are verified by unbounded conjunctions saying that no
earlier/later position is `c`.  There are `O(L^2)` boundary guesses and only
constantly many algebraic values.  Thus the final circuit again has constant
depth and polynomial size.

Soundness follows from the factorization in Section 3.  Completeness uses the
actual first and last `c` and the actual gap products.  Blocks outside the
promised window are assigned the constantly-false circuit, exactly as in the
existing `RTrivialWordACC` implementation.

### Modulus and quantitative bookkeeping

Starting from input modulus `m`:

1. invoke `MonoidWordACCGen N`, obtaining modulus `m_N` divisible by `m`;
2. build all gap and derived-letter recognizers over `m_N`;
3. invoke `MonoidWordACCGen M_c`, obtaining `m_c` divisible by `m_N`;
4. lift the `N` and original-letter circuits to `m_c` and make the final joins.

Each recursion level adds a fixed depth and replaces the size by a fixed
polynomial.  Since the monoids are fixed and their cardinality strictly drops,
the total depth is constant and the final exponent is constant.

More explicitly, for a valid requested block let `ell` be its expanded length.
The recursive `N` call supplies exact product recognizers for every interval
inside `[0,ell)`.  A derived-letter recognizer has `O(ell*|N|)` candidate
branches.  The `M_c` call is made with this common polynomial upper bound as
its input `size`.  The final first/last-boundary join has
`O(ell^2*|N|^2*|M_c|)` branches.  Since expansion multiplies `ell` by a
constant depending only on `M`, all three bounds are powers of
`size+len+2`.  For `a>b` or `b>len`, use the constantly-false circuit;
therefore soundness still holds for every pair `(a,b)` while completeness is
required exactly on the promised window.

## 5. Induction for abelian-local finite monoids

We now prove:

> If every subgroup of a finite monoid `M` is abelian, then
> `MonoidWordACCGen M`.

Choose an inclusion-minimal monoid generating set `A`.

If every member of `A` is a unit, then every element of `M` is a unit.  Thus
`M` is a group, and by hypothesis it is abelian.  The existing theorem
`monoidWordACCGen_of_comm` applies.

Otherwise choose a nonunit `c in A`.  Put `N=<A\{c}>`.  Minimality of `A`
gives `c notin N`, so `N` is a proper submonoid and `|N|<|M|`.  The local
divisor `M_c` also has smaller cardinality.  Both inherit the property that all
subgroups are abelian, so induction gives the generalized word theorem for
both.  The compression lemma gives it for words over `A union {1}`.

Finally, fix once and for all a word `rep(m)` over `A` for every `m in M`.
Let `R` be the maximum representation length and pad shorter representations
on the right by identities.  Replace each input letter by its length-`R`
representation.  The `j`-th expanded symbol is recognized by an OR over the
constantly many values `m` whose fixed representation has that symbol.
Products are unchanged, length grows only by the constant factor `R`, and the
generalized modulus/depth interface absorbs the extra recognition layer.
Thus arbitrary `M`-valued words reduce to the alphabet handled above.

This completes the induction.

Two choices in this induction are essential.

* One cannot merely pick an arbitrary nonunit `c` and take
  `N=<M\{c}>`: this `N` need not be smaller.  In the monoid
  `{1,a,0}` with `a^2=0`, choosing `c=0` gives `0 in <{1,a}>` and hence
  `N=M`.  The inclusion-minimal generating set is what guarantees strict
  decrease.
* When `M` is a group every `c` is a unit and its local divisor has the same
  size.  The commutative-group evaluator is therefore a genuine base case,
  not an optional optimization.

## 6. Exact Lean gap and relation to the current development

The current files already provide:

* the generalized interface `MonoidWordACCGen`;
* its commutative base case;
* modulus lifting;
* submonoid and quotient/divisor closure;
* unbounded `OR`/`AND` assembly and polynomial size estimates;
* the ordinary `MonoidWordACC` reduction after the generalized theorem.

The shortest new Lean route is therefore:

1. define the finite local divisor `LocalDivisor M c`, its multiplication and
   identity;
2. prove it is smaller for nonunit `c` and is a divisor of `M`;
3. define either a small alphabet-restricted wrapper around
   `MonoidWordACCGen`, or state the marked compression lemma directly for the
   fixed alphabet `B union {1,c}`;
4. formalize the block-local marked local-divisor compression lemma of
   Section 4;
5. perform well-founded induction on `Fintype.card M` with a minimal generating
   set and fixed representations;
6. instantiate with the now paper-proved abelian-local property of
   `NonCrossing W` and apply `monoidWordACC_of_gen`.

`RTrivialWordACC`, `LTrivialWordACC`, and the rank/shape epoch machinery remain
useful tests and possible optimization lemmas, but they are not required by
this induction.  In particular, this route avoids the unfinished absolute
holonomy coordinates and the false rank-one stretch hypothesis.

## 7. Adversarial checks

The construction explicitly handles the two old failure modes.

* **Rank-one/reset trajectories:** every new occurrence of `c` produces a
  local-divisor letter.  The argument does not require rank or shape to change.
* **Moving basepoints:** the recursive state is the actual gap product in `N`
  and then the actual product in `M_c`; no per-letter group exponent is measured
  relative to an input-dependent range.

The tempting stronger shortcut

`MonoidWordACC N and MonoidWordACC M_c => MonoidWordACC M`

with the non-generalized interface is insufficient for nesting: the
`M_c`-letters are themselves recognized by circuits for `N`-block products,
not by depth-two input recognizers.  `MonoidWordACCGen` is precisely the repair.

There is also a concrete reason the already formalized commutative,
`R`-trivial, and `L`-trivial cases cannot replace the induction.  Adjoin an
identity to the `2 by 2` rectangular band with multiplication
`(i,j)(k,l)=(i,l)`.  All of its local groups are trivial, but it is
noncommutative, has nontrivial `R`-classes (fixed first coordinate), and has
nontrivial `L`-classes (fixed second coordinate).
