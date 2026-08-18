# N4: incidence-resolved cylindrical refinement

## 0. The exact issue with the printed HMV predicate

Let the vertices of two consecutive layers be cyclically numbered by
`[k]`.  HMV, TR02-066, p. 3, prints the following condition for arcs
`a -> c` and `b -> d`:

* every vertex strictly between `a` and `b` may connect only into `[c,d]`;
* every vertex strictly between `b` and `a` may connect only into `[d,c]`.

Taken literally for *all* pairs of arcs, including pairs with a common
endpoint, this is not by itself a safe combinatorial encoding of a
cylindrical embedding.  (If the intended convention silently excludes
such pairs, that convention still supplies no order on the separate arc
incidences at the common endpoint.)  For example, under the all-pairs
reading the
geometrically cylindrical transition

```text
U = (1,2,3),  V = (1,2,3),
E = {1->1, 2->1, 3->3}
```

is rejected by the printed predicate: applying it to `1->1` and `2->1`
uses `(2,1)={3}` and `[1,1]={1}`, and would force vertex `3` to connect
only to target `1`.  Conversely,
`K_{2,3}` from sources `1,2` to all three targets, with source `3`
isolated, passes the literal predicate: pairs with the same source impose
no condition, and for pairs with distinct sources the only strictly
intermediate source is the isolated one.  Yet it has no common cyclic
order of its six arc incidences.  Indeed, the three incidences at source
`1` and the three at source `2` would have to form two cyclic blocks.  A
cycle with two nonempty blocks has only two block-boundary adjacencies,
whereas each of the three target fibers would require its source-`1` and
source-`2` incidences to be an adjacent two-element block.  Thus at most
two of the three target blocks can exist.

This is not a problem for Hansen's geometric theorem.  In the proof of
Hansen, TR03-025, Theorem 2, p. 6, he explicitly obtains the stronger and
correct finite certificate:

> order outgoing arcs by traversing the separating curve and taking the
> local outgoing order, and order incoming arcs at the next layer in the
> corresponding way; the two arc orders coincide.

That common arc-incidence order is the hypothesis used below.  If every
vertex is first split into consecutive incidence ports, the matching of
outgoing to incoming ports satisfies HMV's cyclic-interval formula
literally.  Thus the proof below is finite combinatorics after one precise
geometric-to-combinatorial interface; it is not a consequence of the
printed vertex predicate alone.

## 1. Definitions

A **cyclic word** on a finite set is a linear word modulo cyclic rotation.
Let `X,Y` be cyclically ordered finite sets and let
`E subset X times Y` be the arcs of one layered transition.  Write
`Out(x)` and `In(y)` for the corresponding sets of arcs.

An **arc-order certificate** for `(X,Y,E)` consists of a cyclic word
`Omega` containing every arc of `E` exactly once, with these two
properties:

1. `Omega` is obtained by going through `X` in its cyclic order and, for
   every `x`, writing all arcs of `Out(x)` as one consecutive (possibly
   empty) block;
2. the same `Omega` is obtained by going through `Y` in its cyclic order
   and, for every `y`, writing all arcs of `In(y)` as one consecutive
   (possibly empty) block.

The internal orders of the two kinds of blocks are part of the
certificate.  A transition, and then a layered graph, is called
**incidence-cylindrical** if every transition has such a certificate.

### Lemma 1 (certificate and the exact cyclic-interval condition)

Split every `x` into one port `(x,e)` for every `e in Out(x)`, retaining
the block order in `Omega`, and split every `y` similarly into ports
`(e,y)`.  Join `(x,e)` to `(e,y)`.  On these two port circles, the exact
HMV cyclic-interval condition holds.

**Proof.** Number both port circles by the positions of `Omega`.  The
port matching is `j -> j`, up to a common cyclic rotation.  Given two
matching arcs at positions `a,b`, every port in the open cyclic interval
`(a,b)` maps to the corresponding port in `[a,b]`, and likewise in the
opposite interval.  This includes the wrap-around and adjacent cases in
HMV's definition.  There are no shared endpoints after splitting.  QED.

### Lemma 2 (geometric source of the certificate)

Every geometrically layered cylindrical transition has an arc-order
certificate.

**Proof.** Use the separating-curve arc order constructed explicitly in
Hansen's proof of Theorem 2.  Equivalently, after an arbitrarily small
strict-monotonicity perturbation, intersect the arcs with a regular circle
strictly between the two layer circles; every arc then meets it exactly
once.  Reading the intersections around the circle gives `Omega`.
Moving the circle toward the source boundary does not change the order;
near a source vertex all its outgoing intersections form one consecutive
block in the local rotation.  Moving it toward the target boundary gives
the consecutive incoming blocks in target order.  These are the same
intersection points and hence the same cyclic word.  This is exactly the
arc-order equality established on p. 6 of Hansen's proof of Theorem 2.
QED.

Conversely, an arc-order certificate realizes a transition on an annulus:
draw one disjoint axial strand for each position of `Omega` and join each
consecutive source or target block to its vertex inside a disjoint small
boundary sector.  Place degree-zero source or target vertices in arbitrary
gaps between consecutive strand sectors on their boundary circle; they
have no arcs and impose no further constraint.  Hence this certificate is precisely the finite data
needed below.

## 2. Precise refinement theorem

### Theorem N4

Fix `W,F`.  Let `C` be a finite layered incidence-cylindrical `ADRCircuit`
whose wire relation is a set, with layers `V_0,...,V_h`, `|V_i| <= W`, and
with every AND/OR gate having at most `F` predecessors.  In this document,
“COPY” abbreviates a unary OR gate, true is a nullary AND gate, and false is
a nullary OR gate; these are not additional constructors.  Literal nodes
have no predecessor.  For every AND/OR gate
`g`, let `y_g` be a fresh independent Boolean input which is to be
combined with the old inputs by the same operation as `g`.

Every old layer is processed uniformly as the target of a strip. For `V_0`
the source is a virtual empty layer and its arc word is empty. Thus first-layer
AND/OR gates receive their ports through the same leaf-and-fold construction as
all later gates; there is no separate relabelling convention.

Then there is an equivalent layered incidence-cylindrical circuit `C'`
such that:

1. every computational node is a fan-in-at-most-two AND/OR gate (including
   the unary/nullary encodings above); its other nodes are literals;
2. after substituting arbitrary bits for all `y_g`, every old checkpoint
   layer has exactly the same value vector as in `C` with `y_g` adjoined
   to gate `g`;
3. its total width is at most
   `K = (F+1)W` (and at most `max(1,K)` in the empty degenerate case);
4. every target strip, including the virtual strip into `V_0`, uses at most
   `ceil(log_2(F+1)) + 2` transitions;
5. for fixed `W,F`, its size is `O_{W,F}(|C|)`.

By the realization following Lemma 2, `C'` is geometrically layered
cylindrical, i.e. it belongs to the geometric circuit class to which the
Hansen/HMV upper-bound argument is intended to apply.

If an AND/OR gate without a fresh port is allowed and has no old predecessor,
its existing nullary AND/OR semantics supplies the neutral value.  In the OQ3
application every refined gate has its fresh port, so each reduction word is
nonempty.

## 3. Construction for one target layer

Fix a target layer `V=V_i`. If `i>0`, use the old transition

```text
U = V_{i-1}  --->  V = V_i
```

with arc set `E` and arc-order certificate `Omega`. If `i=0`, take `U`
to be a virtual empty source, `E` and `Omega` to be empty, and retain the
given cyclic order of `V_0`. For `g in V`, let `E_g = In(g)`, listed in
the order of its consecutive block in `Omega`; in the virtual strip every
`E_g` is empty.

### 3.1 Leaf-and-port layer

Create a layer `L^0` as follows.

* For every old arc `e=(u,g)`, create a COPY node `z_e` and the arc
  `u -> z_e`.
* For every AND/OR target `g`, create the fresh input node `p_g` carrying
  `y_g`; it has no incoming arc.
* Traverse targets `g` in the cyclic order of `V`.  The block `B_g^0`
  consists of the nodes `z_e` for `e in E_g`, in target-incidence order,
  followed by `p_g` if `g` is AND/OR.  Concatenating the blocks gives the
  cyclic order of `L^0`.

Empty incoming blocks cause no ambiguity.  If several successive targets
have no old incoming arcs, their fresh ports are simply written in target
order in the common gap.  If there are no arcs at all, the target order
alone orders the nonempty port blocks.

The transition `U -> L^0` is incidence-cylindrical.  Its arcs are indexed
by old arcs `e`.  In source-block order they form `Omega`; in the order of
their one-element incoming blocks at the `z_e` nodes they again form
`Omega`.  Inserting the isolated `p_g` nodes changes neither arc word.
This is the promised complete treatment of fan-out: two occurrences of
the same predecessor in two target bundles become two different COPY
nodes `z_e,z_f`, while the old source is allowed to fan out to both.

### 3.2 Simultaneous adjacent-pair reductions

Put `Q=F+1` and `L=ceil(log_2 Q)`.  For an AND/OR target `g`, its active
word `A_g^0` is `B_g^0`; it has

```text
q_g = |E_g|+1 <= F+1 = Q
```

entries and is therefore nonempty.  This includes an old unary OR gate: it is
still an old computation target and its word contains both its old input and
its fresh port.  A literal target has no active word and is left as an input at
the final checkpoint.  COPY nodes introduced *by the refinement* are merely
unary OR rails and do not receive new ports.

Inductively, from the linearly ordered active word

```text
A_g^j = (a_1,...,a_r)
```

form `A_g^{j+1}` by the following disjoint operations:

* replace `(a_1,a_2),(a_3,a_4),...` by gates using the operation of `g`;
* if `r` is odd, replace the last singleton by a COPY node.

Perform this for every target simultaneously, and order layer `L^{j+1}`
by concatenating the resulting target blocks in the cyclic order of `V`.
After `L` rounds every nonempty block has one root, since
`|A_g^j| = ceil(q_g/2^j)`.

Every transition `L^j -> L^{j+1}` is incidence-cylindrical.  List its
arcs target block by target block, and inside a block list the children in
the order of `A_g^j`.  On the source side every child has exactly one
outgoing arc, so this is source-block order.  On the target side, the one
or two incoming arcs of every new parent are consecutive, the parents are
in their output order, and hence this is the identical target-block arc
word.  Lemma 1 verifies the cyclic-interval condition, including the
last-to-first wrap.  No argument assumes that the old predecessor sets
were disjoint: disjointness is obtained from the edge-occurrence COPY
nodes before reduction.  AND and OR targets may be arbitrarily mixed,
because different target blocks have no edges between them.

To spell out the cyclic cut: choose any boundary between two target
blocks as a temporary beginning of the written word.  Pairing is only
inside a block.  Rotating this temporary cut changes neither cyclic word
nor certificate.  If there is only one nonempty target block, choose any
of its incidences as first; associativity makes the chosen parenthesization
semantically irrelevant.

### 3.3 Return to the checkpoint layer

Use a final layer with the old cyclically ordered vertex set `V`.
For every target with a root, add the one arc `root_g -> g` and label `g`
as a unary OR (the COPY encoding).  Retain an old literal target as that input node with no
incoming arc.  The roots occur in target order, so the root-to-checkpoint
arcs have the same cyclic word on both sides.  This last transition is
incidence-cylindrical.

Relabelling an old AND/OR target as unary OR is harmless: its operation has
already been performed in its reduction tree, and all arcs of the next
old transition still leave the same checkpoint value.

## 4. Correctness

For every old arc `e=(u,g)`, `z_e` has the value of `u`.  Inductively,
associate with each active node at reduction level `j` the consecutive
subword of `B_g^0` below it.  A COPY preserves its subword's value; a
binary gate computes the AND or OR of the two adjacent subwords.
Consequently the root has value

```text
AND({ value(u) : (u,g) in E } union {y_g})
```

for an AND target, and the analogous OR value for an OR target.  A
one-leaf tree is a COPY chain, so the cases of zero old inputs and one
total input are included.  Associativity proves independence of the
balanced parenthesization.  When the old gate semantics is presented as
an unordered predecessor set, the usual commutativity of Boolean AND/OR
identifies this ordered fold with that set semantics.  Literal input nodes are
immediate; a unary old OR/AND gate is covered by the same port-augmented fold
as every other old computation gate.
The final unary copy therefore restores precisely the required value at every
old target. Induction over `i=0,...,h`, beginning with the virtual empty-source
strip, proves equality at every old checkpoint and hence at the output. For an
AND/OR gate `g` in `V_0`, its initial active word is the singleton port
`p_g`; its fold and final COPY therefore produce exactly `y_g`. Literal
vertices in `V_0` are retained as inputs. The empty source needs no cyclic
numbering: the empty arc word has a unique source-side listing, while the first
nonempty order is the already supplied order of `V_0`.

## 5. Quantitative bounds

For one target strip, including the virtual first strip,

```text
for an AND/OR target g: |E_g|+1 <= F+1,
for an input target g: |E_g|   = 0,
therefore |L^0| = sum_g |B_g^0| <= (F+1)|V| <= (F+1)W = K.
```

The number of active nodes never increases in a reduction round, so every
micro-layer also has width at most `K`; a checkpoint has width at most
`W <= K` when `F>=0` and `W>0`.  Repeated halving gives one root after
`L=ceil(log_2(F+1))` rounds. Including the leaf transition and final
checkpoint transition gives `L+2` transitions per target strip.

There are at most `K` nodes on each of at most `L+1` new layers per target
strip. After deleting empty old layers, there is one target strip per old
layer, including `V_0`, so the number of strips is at most the old number
`N` of vertices. Hence

```text
|C'| <= N + (L+1) K N = O_{W,F}(N).
```

This deliberately loose estimate already gives linear size for fixed
`W,F`.  A gate-by-gate count gives `O((F+log(F+1))N)`.

## 6. No exact-width padding is needed by N4

`TotalWidthAtMost` is an upper bound, so shorter layers are left shorter.
The singleton paths already present in the construction are unary-OR rails
and synchronize trees of unequal depths.  Consequently the refinement adds
neither isolated padding nodes nor any syntax absent from `ADRCircuit`.
Any exact-coordinate padding needed in a future proof of the quantitative
cylindrical ACC principle belongs to that separate transfer; it is not part
of N4 and does not change the proved bound `(F+1)W`.

## 7. Global gluing

Start with the virtual strip into `V_0`, then apply the strip construction
between every two consecutive old checkpoint layers, always retaining the
checkpoint's old cyclic vertex order. The last layer of strip `i` and first
layer of strip `i+1` are therefore literally the same checkpoint layer.
Cylindricity is a condition on each adjacent pair only, and every new adjacent
pair has an explicit arc-order certificate above. Hence the concatenated
circuit is incidence-cylindrical. The per-strip semantic statement composes by
induction, and the quantitative bounds sum linearly.

## 8. What has and has not been simplified

Once the common arc-order certificate is given, everything from the
leaf layer onward is elementary finite combinatorics: finite cyclic words,
edge occurrences, adjacent pairing, COPY chains, and counting.  This is
substantially friendlier to Lean than collars, rectangles, terminal arc
segments, and micro-circles.

One geometric fact has not disappeared: the cylindrical core supplied by
Hansen must provide the common outgoing/incoming arc-incidence order.
Fortunately Hansen's proof of Theorem 2 explicitly constructs exactly
that order.  Thus a clean formal interface may take `ArcOrderCertificate`
as the output of the external Hansen bridge.  If instead one takes only
the printed HMV vertex-interval predicate as input, N4 is not proved:
without an additional incidence convention/certificate, that predicate
does not contain the data used by the refinement.

So this is a real local simplification of old Lemma 8.2, but not a removal
of the Hansen/geometric interface: it compresses the geometric part to
Lemma 2 and makes all subsequent refinement combinatorial.

The N4 refinement, port substitution, and the remainder of the OQ3 assembly
are internal.  The quantitative conversion of a normalized
incidence-cylindrical circuit to `ACC^0` remains exactly
`QuantitativeCylindricalACCPrinciple`, one of the two external facts.  A future
optional project may derive it from a geometric transition monoid and the
Barrington--Therien solvable-monoid word theorem.  The earlier placeholder
modules for that project were deliberately removed because they contained no
such proof.  No appeal to the unsafe literal reading of HMV's unsplit vertex
predicate is made.
