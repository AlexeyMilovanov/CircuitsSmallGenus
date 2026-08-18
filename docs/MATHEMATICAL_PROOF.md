# Allender OQ3: mathematical proof used by the Lean project

## 1. The theorem

Let `C_n` be a polynomial-size family of properly layered AND/OR circuits.  A
layer contains at most a fixed number `w` of computation gates; literal gates
do not count toward this width and may have arbitrary fanout.  Suppose the
orientable genus of the underlying graph is at most

```text
A * (log_2(n+1))^k
```

for all sufficiently large `n`.  Then the language decided by the family is in
nonuniform `ACC^0`, with one fixed modulus, one fixed depth, and polynomial
size.  This is exactly `AllenderOQ3Statement`.

The proof below uses the three frozen principle signatures isolated in
`ExternalFacts.lean`.  The finite-attainment principle is proved internally;
only the Hansen incidence-order and quantitative ACC principles remain
external.

Throughout Sections 3--7, *rotation-planar* means “admits a rotation of
rotation genus zero”.  This is the finite predicate `RotationPlanar`; it is not
a separately formalized topological embedding predicate.  The attainment of
the finite minimum is kernel-proved.  External Fact 2 deliberately packages
both the standard realization of a genus-zero rotation and Hansen's extraction
of a common arc-incidence order.  This is the exact trust split in the Lean
signatures.

## 2. Deterministic semantics and pruning

Because every edge increases the ADR layer by exactly one, gate values are
defined uniquely by induction on the layer.  The existential valuation in
`ADRAccepts` therefore agrees with the ordinary evaluation of the circuit.

Delete every gate that is not an ancestor of the designated output.  This does
not alter the output value, cannot increase width or genus, and preserves the
layer condition.  Literal-output circuits are handled directly by a constant
depth ACC circuit.  Hence the nontrivial case has a computation output and
every retained computation gate reaches it.

For the genus claim, delete every incident edge first and apply edge-deletion
monotonicity, then delete the now-isolated unwanted vertices.  The latter step
does not change the Euler defect: one vertex, one connected component, and the
explicit isolated-face correction disappear together.  Thus pruning really
cannot increase the exact rotation genus used here.

The numeric layer labels may initially be very sparse and arbitrarily large;
they must not be used as a size bound.  In the pruned nontrivial circuit, every
retained vertex has a directed path to the output.  Choose a retained vertex
of minimum layer.  Its path meets every integer layer between that minimum and
the output layer, because every edge raises the layer by exactly one.  Thus
there are no empty layers in this interval and its length is at most the gate
count.  Translate every retained layer by subtracting the minimum.  This
preserves every edge equation `layer(u)+1=layer(v)`, width, semantics, and the
underlying rotation graph, and now the number of transitions is at most
`|C|-1`.  The one-gate/empty-predecessor case has span zero.  This internal
layer-compression lemma is used before all cuts and block decompositions.

## 3. A genus budget for vertex-disjoint nonplanar subgraphs

Work directly with the rotation-system genus defined in `Model.lean`.

First prove edge-deletion monotonicity.  Given a rotation, erase the two darts
of one undirected edge and splice their predecessors and successors in the
vertex and face permutations.  If the edge is not a bridge, deleting it either
merges two face cycles or splits one face cycle; the Euler defect is unchanged
or decreases by two.  If it is a bridge, its two darts belong to one face, and
the component/isolated-vertex correction gives the same conclusion.  The
pendant and isolated-`K_2` cases are included explicitly.  Thus deletion never
increases rotation genus, and hence never increases minimum genus.

For one fixed rotation, the Euler defect is the sum of the defects of its
connected components.  Each defect is a nonnegative even integer, and a
component without a zero-genus rotation contributes at least one to genus.
Consequently, if a graph of genus `g` contains `r` vertex-disjoint connected
nonplanar subgraphs, retain only their edges.  They become distinct components
(all other vertices are isolated), so `r <= g`.

This is the only genus-packing statement needed.  Full Battle--Harary--Kodama--
Youngs additivity of minimum genus is unnecessary.

## 4. The layer-planarizer theorem

For every connected subgraph `H` that is not rotation-planar, let

```text
I(H) = [minimum layer met by H, maximum layer met by H].
```

Every edge changes the layer by one.  Connectivity therefore implies that `H`
contains a vertex on every integer layer in `I(H)`.

If `I(H_1), ..., I(H_r)` are pairwise disjoint, then the `H_i` are
vertex-disjoint.  The genus budget gives `r <= g`.  The elementary greedy
packing/piercing theorem for finite integer intervals now supplies at most `g`
layer numbers meeting every interval `I(H)`: repeatedly select an interval
with least right endpoint, record that endpoint, and delete all intervals
containing it.

Let `P` be the resulting set of layers and delete every vertex on a layer in
`P`.  If the residual graph were not rotation-planar, one of its connected
components would not be rotation-planar.  Its interval is pierced by some
`p in P`, while connectivity forces `H` to contain a vertex on layer `p`, a
contradiction.  Therefore `|P| <= g` and deletion of the layers in `P`
planarizes the graph.

## 5. Constant state on a layer

Fix once and for all `w` slots for computation gates in every layer, padding
unused slots by zero.  A state is therefore an element of `{0,1}^w`, a fixed
finite set of size `q = 2^w`.  Literal values are functions of the original
input and are never part of the carried state.

For a transition from layer `i` to `i+1`, the next state is determined by the
current state and the literals feeding the computation gates in layer `i+1`.
An exceptional one-layer transition is consequently an AC0 relation on two
constant-size states and the original input.  Every one-step, exceptional,
and block relation explicitly requires all unused padded slots in both endpoint
states to be zero; therefore no spurious run through a dummy coordinate is
ever admitted.

## 6. Cutting without restoring deleted vertices

Define `X = {i | i in P or i+1 in P}` and call exactly the transitions indexed
by `X` exceptional.  Thus `|X| <= 2|P|`.  A regular block is a maximal
consecutive interval of transition indices outside `X`; an empty interval is
the identity relation.  Every vertex and edge in a regular block belongs to
the graph after deleting all `P`-layers, so the block is literally a
rotation-planar subgraph.  Its first-layer state is hardwired by deleting
omitted incoming edges and treating the existing first-layer gates as formal
Boolean inputs.  Deleted computation vertices are never reinserted and no
shared apex is introduced.  The chronological list of initial, exceptional,
regular-block, and final relations has exactly the same runs as the original
circuit, by induction over transition indices.

The complete computation becomes a chain consisting of:

- an initial relation;
- at most `2|P|` exceptional transition relations;
- at most `|P|+1` planar-block relations;
- a final output test.

Thus the number of relations is at most `3g+3`.

## 7. The parameterized planar bridge

We prove the following quantitative statement by induction on computation
width `w`:

```text
for every w there exist M,d,e such that, for every n and every
rotation-planar well-formed ADR circuit C of computation width at most w,
there is an equivalent ACC[M] circuit A with
depth(A) <= d and |A| <= (|C|+1)^e.
```

Here `M,d,e` depend only on `w`, not on `n`, `C`, its shape, or the number of
literal occurrences.  This per-circuit-in-`|C|` invariant is what later gives
common parameters for all planar blocks.

### 7.1 Base case

At width zero, a retained output is a literal or an empty computation gate.
It has a direct constant-size ACC implementation.  In the actual ADR syntax,
a Boolean copy is a unary OR gate, true is a nullary AND gate, and false is a
nullary OR gate; no extra COPY or constant constructors are assumed.

### 7.2 The cylindrical core

After ancestor pruning, choose a computation gate `v` in the earliest active
layer and let `D` be the computation vertices lying on a directed path from
`v` to the output `o`.  The directed graph `D` has unique source `v`, unique
sink `o`, and meets every computation layer between them.  Let `R` be the
remaining computation vertices.  No vertex of `D` reaches a vertex of `R`;
all computation ancestors of an external predecessor of `D` lie in `R`.
Since `D` removes at least one computation vertex from every active layer,
`R` has computation width at most `w-1`.

The core is a subgraph of the rotation-planar source circuit.  Internal
edge-deletion surgery supplies minimum rotation genus zero for the core.
The internal finite-attainment theorem supplies a zero-genus rotation, and
External Fact 2 gives an `IncidenceCylinder` for `D`.

### 7.3 External values and beta ports

For each gate `g` in `D`, separate its predecessors into internal computation
predecessors, external computation predecessors in `R`, and literal
predecessors.  Define

```text
beta_g = AND(all external and literal predecessor values), if g is AND;
beta_g =  OR(all external and literal predecessor values), if g is OR,
```

with the usual empty identities.  For every external predecessor `h`, take the
predecessor-closed ancestor circuit with output `h`.  Every computation vertex
in it lies in `R`, so it is rotation-planar and has width at most `w-1`.
Invoke the induction hypothesis on these circuits.  There are at most `w|D|`
external computation-edge occurrences; sharing equal outputs is optional, and
even one call per occurrence remains polynomial.  One additional unbounded
AND or OR over those outputs and the genuine literals computes `beta_g`.
Gate `g` is now its original operation applied to its internal inputs and one
formal late input port carrying `beta_g`.

### 7.4 Incidence-resolved fanin reduction

The common cyclic arc word in `IncidenceCylinder` makes fanin reduction purely
finite and combinatorial.  For one old transition, first create one COPY node
`x_e` for every old arc `e`, followed in each target block by the formal port
`p_g`.  In every target block, repeatedly combine adjacent pairs by the target
gate's operation and pass an unmatched last signal through a unary copy.  The
common arc word certifies every micro-transition: tail fibres and head fibres
are consecutive blocks in the same cyclic word.

If the old width is `W` and fanin is at most `F`, the first micro-layer has at
most `FW+W` nodes, the reduction takes `ceil(log_2(F+1))` rounds, and its total
size is linear for fixed `F,W`.  Empty fibres are represented by the port;
unequal tree depths use unary copies.  Consecutive refined strips glue because
their root order is the original next-layer order.  The full proof, including
the failure of the weaker printed HMV predicate, is in
`INCIDENCE_REFINEMENT.md`.

Every COPY produced by this construction is encoded as a unary OR gate in the
actual `ADRCircuit` syntax.  Neutral constants, if needed, are nullary AND/OR
gates.  The construction therefore yields an ordinary ADR circuit, and a
direct layer induction proves that this encoding preserves the described
values.  Since External Fact 3 needs only an upper width bound, no isolated
padding nodes are added.

The result is an HMV-normal circuit of fixed total width with an
`IncidenceCylinder`.  External Fact 3 supplies its ACC wrapper as a function
of the beta ports.

### 7.5 Exact port substitution

The refined circuit temporarily has an enlarged input type consisting of the
original inputs and one formal variable `y_g` for each port.  Fix injections
of both summands into this finite input type.  In the ACC wrapper, keep every
literal occurrence as a distinct node (the edge relation is Boolean, so
parallel occurrences cannot be represented by one repeated edge).  Replace a
positive occurrence of `y_g` by a unary-copy node fed by the output of the
already constructed `beta_g` circuit, and a negative occurrence by a NOT node
fed by that output.  Reindex all nodes, keep genuine `x_i`/`not x_i` literals
at ACC layer zero, and shift the wrapper's nonliteral layers above the common
beta depth.  A layer induction proves semantic substitution; the construction
adds constant depth and polynomial size, preserves `WellFormedACC`, and removes
all formal port variables.  Concretely, each formal literal vertex of the
wrapper is one occurrence; the replacement creates at most one new unary
copy/NOT vertex for it.  Hence the number of added vertices is at most the
wrapper size, while the shared beta output may fan out freely.

### 7.6 One modulus and quantitative induction

At induction level `w`, finitely many fixed moduli occur: those from level
`w-1` and from the fixed cylindrical monoid.  Let `M_w` be their least common
multiple (and include `2`).  If `q` divides `M_w`, simulate a `MOD_q` zero test
by feeding `M_w/q` distinct shared copies of every predecessor into a
`MOD_M_w` gate.  Residue tests are obtained by adding a fixed number of true
constants (nullary AND gates), and finite residue sets by OR.  Each required
multiplicity is realized by distinct unary-copy nodes, shared across converted
MOD gates; fanout is free, so the conversion is linear up to a constant
depending only on `w`.  To preserve strict ACC layering, send every old layer
`ell` to layer `2*ell`, place the shared copies of its outputs on layer
`2*ell+1`, and leave every converted target on the doubled layer of its old
target.  Original edges went strictly forward, so all new edges do too;
literal gates remain exactly on layer zero, and the depth only doubles.  Fixed
true constants used for residue shifts are placed on a positive layer below
their MOD target.

For completeness, make the quantitative induction explicit.  Suppose the
width-`w-1` compiler has size at most
`A_(w-1)(N+1)^(p_(w-1))` and depth `d_(w-1)`.  A width-`w` core with `N`
vertices has at most `wN` external-computation predecessor occurrences.  The
fixed-width cylindrical wrapper, including symbol selectors, simple-edge
normalization, and modulus conversion, has size at most
`C_w(N+1)^(c_w)` and adds a fixed depth `delta_w`.  Sharing is optional; even
one recursive call per occurrence gives

```text
S_w(N) <= wN A_(w-1)(N+1)^(p_(w-1))
          + C_w(N+1)^(c_w) + C'_w(N+1).
```

It is therefore enough to choose

```text
p_w = max(p_(w-1)+1, c_w, 1),
A_w >= w A_(w-1) + C_w + C'_w,
d_w = d_(w-1) + 1 + delta_w.
```

All constants depend only on `w`.  Since the original computation width is a
fixed constant, this proves a fixed depth and a polynomial size bound for the
planar bridge.  Finally remove the leading coefficient: an `ADRCircuit` has
`N>=1` because it contains `output : Fin N`, hence `N+1>=2`.  Increasing the
exponent by `ceil(log_2(max(1,A_w)))` absorbs `A_w` into a bound of the exact
form `(N+1)^e` required downstream.

## 8. Planar block relations

For each planar interval and each pair of boundary states `(s,t)`, hardwire the
start state and ask whether the block produces the end state.  There are only
`q^2` pairs.  Apply the planar bridge to each output bit and conjoin the padded
state equalities.  All block positions, lengths, and state pairs share the same
modulus, depth, and polynomial exponent because the bridge parameters depend
only on the fixed source width.  The source size exponent is used only when
converting the per-circuit bound in `|C|` into a polynomial bound in `n`.

Initial and final relations are explicit.  With padded zero state `zeta`, let
`I_x(zeta,t)` assert that `t` is the genuine first computation-layer state, and
let `O(s,zeta)` assert that `s` is padded-valid and its output coordinate is
one.  Acceptance is the `(zeta,zeta)` entry of the composed relation

```text
O compose E_r compose ... compose E_1 compose I_x.
```

## 9. Composing polylogarithmically many constant-state relations

Let `B = floor(log_2(n+1))`; handle the finitely many cases `B < 2` by truth
tables.  Compose a block of at most `B` relations by the depth-two formula

```text
T(a,b) = OR over s_1,...,s_(B-1)
           AND_j R_j(s_(j-1),s_j).
```

For a final block of actual length `ell<B`, either use the identical formula
with only `ell-1` intermediate states, or pad the block on the right by
`B-ell` identity relations.  We use the latter convention below, so the
displayed `B`-ary formula is literal for every block.

The state set is fixed, so the number of state sequences is at most

```text
q^B <= (2^B)^q <= (n+1)^q.
```

One round therefore has polynomial size and adds two Boolean layers.  More
precisely, if the initial chain length is at most `C B^k`, enlarge the finite
small-input cutoff until `B >= 2C`.  Writing
`m_(j+1) = ceil(m_j/B)`, one has `m_j = ceil(m_0/B^j)`; after `k` rounds there
are at most `C+1 <= B` relations and one final round suffices.  For `k=0`, the
first round already suffices.  Thus a chain of length
`O((log(n+1))^k)` becomes one relation after at most `k+1` rounds above the
cutoff.
The exponent `k` is fixed by the source family, so total added depth is
constant.  Existing entry circuits are shared as a DAG rather than copied.
AND and OR gates do not alter the fixed modulus.

## 10. Exact family quantifiers

For all sufficiently large `n`, the genus hypothesis and the layer-planarizer
give at most

```text
A * (log_2(n+1))^k
```

cut layers, hence a polylogarithmic relation chain.  Sections 7--9 give one
modulus `M`, one depth bound `d`, and a polynomial size bound independent of
`n`.  Absorb fixed coefficients by increasing the exponent.

Choose a threshold large enough both for the source genus bound and for the
blocking inequalities.  Every positive input length below it is implemented
by a finite truth-table DNF and absorbed into the same constants.  At `n=0`,
use exactly one empty AND or empty OR gate according to the sole truth value;
this satisfies the exact bound `(0+1)^e = 1`.

Classical choice assembles the individual ACC circuits into one family.  The
initial/final relation identity and deterministic ADR semantics prove that it
decides the original language.  This is `InNonuniformACC0 L`, completing the
conditional theorem.

## 11. Why the invalid ADR05 step is absent

ADR05 attempted to decompose handles in one chosen surface embedding into
East/West stripes; that topological assertion is false.  The present proof
never locates or serializes handles.  It uses only the abstract genus budget,
one-dimensional intervals of layers, and deletion of all vertices on the
selected layers.  Every long remaining block is literally a subgraph of a
genus-zero graph.  Thus no form of the invalid stripe lemma is used.
