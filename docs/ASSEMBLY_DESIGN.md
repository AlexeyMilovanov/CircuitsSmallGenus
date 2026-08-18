# E2-c assembly design: the holonomy tower for `(NonCrossing w, Config w)`

Status: 2026-08-17.  This is the authoritative design for closing
`letterWordACCGen_impl`.  It replaces all previous assembly sketches (the
prefix-R-block scheme is refuted — see `HMV_ALGEBRA_NOTES.md` §2 — and remains
forbidden).  The design follows the classical holonomy (Zeiger/Eilenberg,
"Automata, Languages and Machines" vol. B, ch. XII) decomposition of the finite
transformation semigroup `(M, Q)`, `M = NonCrossing w`, `Q = Config w`,
specialized to our two proved ACC gadgets.  Cyclicity of every group that
appears is exactly the heart H1/H2 (pinned in Lean as
`IsCyclic (realizedSubgroup S)`-style statements; machine-verified at w ≤ 3).

## 0. Reductions already in place (proved)

* `wordEnd = h` ⟺ conjunction over the ≤ 2^w start configurations `q₀` of
  "trajectory endpoint from `q₀` equals `h(q₀)`" (`transMonoid_ext_iff`); the
  conjunction is an `accOrAnd` layer.  So it suffices to ACC-recognize
  point-trajectory endpoints.
* Letters are single certified layer maps (`LetterWordACCGen`), each value
  recognized by a given depth-2 circuit of size ≤ `size`.
* Gadgets: `cascade_aperiodic_layer` (deterministic letter+driver-driven
  coordinate with ≤ K changes along every run ⇒ endpoint recognizers, and by
  instantiating on prefixes, per-position recognizers of size poly(len));
  `cascade_cyclic_layer` (product of `g₀^{κ(letter, driver)}` in a cyclic
  group ⇒ MOD-count recognizers, again also on prefixes).

## 1. The tower coordinates

Fix the word `ℓ_1 … ℓ_len` (values in the generator set).  All notions below
are *per input x*; the circuits recognize their values via guess-and-verify.

**Skeleton (constant data, hard-wired per w).**  Let `𝒮 ⊆ 𝒫(Q)` be the family
of subsets reachable from `Q` by images of monoid elements, preordered by
"reachable from" (`T ≼ S` iff `T = image of S under some m ∈ M`).  Let the
*holonomy classes* be the mutual-reachability SCCs of `(𝒮, ≼)`; `depth(𝒮)` ≤
`2^w` because reachability within an SCC preserves cardinality and a
cardinality drop is irreversible.  For each `S ∈ 𝒮` fix its *brick family*
`B(S)` (maximal proper reachable subsets of `S`, covering `S` — add singletons
as degenerate bricks where needed) and for each SCC fix a base object and, for
every member, a reference bijection to the base (spanning-tree choice).  The
*holonomy group* `H(S)` is the group of permutations of `B(S)` induced by
elements of `M` mapping `S` onto `S`; by H2 it is **cyclic**.

**Level-0 coordinate (aperiodic): the SCC trace.**
`A_t := SCC(R_t)` where `R_t := image of Q under ℓ_1…ℓ_t`.  Along the run `A_t`
moves monotonically down the SCC DAG, so it changes ≤ `depth(𝒮)` times:
bounded-change.  Care spot A (see §3): `A_t` alone does not satisfy a
letter-driven update law; the aperiodic gadget must be applied to the pair
coordinate `(A_t, R_t-representative)` as described in §2.

**Level-i coordinates (i = 1 … ≤ 2^w): brick index + holonomy alignment.**
Given the level-(i−1) data (the current set `C^{i-1}_t ∈ 𝒮` containing the
trajectory point, together with its epoch), track
* `b^i_t ∈ B(C^{i-1}_t)` — which brick contains the current point
  (constant-size index; deterministic update from letter + upper coordinates
  within an epoch);
* `g^i_t ∈ H(C^{i-1}_·)` — the holonomy alignment of the brick relative to the
  reference bijections, updated by `g^i_{t+1} = g^i_t · δ(ℓ_{t+1}, uppers)`
  with `δ` a fixed finite table: a **cyclic** coordinate for
  `cascade_cyclic_layer`, with the upper coordinates as `driver`.
The current set at level i is `C^i_t := (reference of g^i_t) (b^i_t)`, and the
trajectory point is recovered at the bottom level where `|C^k_t| = 1`.

**Epochs.**  An *epoch event at level i* occurs when the image of `C^{i-1}_t`
under the next letter leaves the holonomy class (degenerates into a brick of a
lower class).  Each level-i event strictly descends the constant-height
reachability order *relative to the current level-(i−1) epoch*, so the number
of level-i events is at most `depth(𝒮)` per level-(i−1) epoch; the total
number of events across all levels is bounded by `depth(𝒮)^{2^w}` — a constant
`K(w)`.  All event positions and the entering data are guessed
(`≤ len^{K(w)} · const` guesses, an `accOrAnd` disjunction) and verified by
the same coordinates' recognizers on prefixes.

## 2. Mapping to the gadgets

Within a fixed guess of all epoch boundaries and entering data:
* each level's brick index `b^i_t` follows a deterministic update driven by
  (letter, upper coordinates) — recognized by `cascade_aperiodic_layer`
  *applied within the epoch* (where its change count is bounded: care spot B);
  alternatively, and more robustly, `b^i_t` is absorbed into the guessed
  entering data plus the cyclic alignment (the brick walk within an epoch is
  the orbit of the entering brick under the cyclic holonomy action, so it is
  determined by `g^i_t` and the entering brick — no separate aperiodic
  coordinate is needed at levels ≥ 1).
* each `g^i_t` is a `cascade_cyclic_layer` instance: `N :=` the (constant)
  order of the holonomy group, `κ :=` the δ-table, `driver :=` the
  recognizers of the upper coordinates at the same position (obtained by
  instantiating the upper levels' construction on prefixes).
* the final read-off ANDs: all guessed epochs verified (the coordinate at the
  claimed boundary equals the claimed value — recognizers on prefixes), and
  the bottom-level singleton at `t = len` equals the target.

Depth: constant per level (the gadgets add ≤ max(d+2,1)+5 each), ≤ `2^w + 1`
levels, plus the guessing OR — constant `depth(w)`.  Size: each level
multiplies by poly(len) (prefix instantiations) and the guessing multiplies by
`len^{K(w)} · const(w)` — total `(size + len + 2)^{exponent(w)}`.

## 3. Care spots (the two places where the classical proof is delicate)

**A. Well-definedness of the update laws.**  The naive coordinates ("the SCC
of R_t", "which brick") do not satisfy letter-only update laws; the classical
fix (Zeiger coding) is that the *pair* (guessed epoch data, alignment
coordinate) does.  Concretely: within an epoch the current set is
`C^{i-1}_t = ρ(g, b)` for the guessed entering data and the cyclic coordinate,
so the δ-table can be indexed by `(letter, entering data, g, b)` — all
constant-size.  The Lean development must define the coordinates in this
*relative* form from the start; do not attempt absolute coordinates.

**B. The event-count bound.**  The bound "events at level i ≤ depth per
level-(i−1) epoch" needs the fact that after a level-i degeneration the new
holonomy class is strictly lower *in the same relative order*, which is where
`≼`-antisymmetry-up-to-SCC enters.  This is Eilenberg's height function; port
it faithfully (height of an SCC in the DAG), and prove the per-epoch bound by
"height strictly drops at each event".

**C. Where H1/H2 enter.**  Only through the cyclicity of `H(S)` (the δ-tables
land in cyclic groups, enabling `cascade_cyclic_layer`).  No other appeal to
the geometry is needed by the assembly; conversely the assembly makes no sense
without it (with non-cyclic `H(S)` the alignment coordinate would need a
non-abelian word problem — impossible in ACC⁰ by Barrington).

## 4. Suggested Lean decomposition (E2-c-1 … E2-c-5)

1. `HolonomySkeleton.lean` — `𝒮` as a `Finset (Finset (Config w))` (closure of
   `{Finset.univ}` under images), the reachability preorder, SCCs, height;
   bricks `B(S)`; all constant-size data with decidable definitions; the
   height-drop lemma.
2. `HolonomyGroups.lean` — `H(S)` as a subgroup of `Equiv.Perm (B(S))`
   (analogue of `realizedSubgroup`); **uses H1/H2 for `IsCyclic`**; the
   δ-tables and their `unitShift`-style additivity.
3. `HolonomyCoordinates.lean` — the relative coordinates of §1–§2 as functions
   of the word prefix; the deterministic update laws; the event positions and
   the `K(w)` bound (care spot B).
4. `HolonomyCascade.lean` — instantiate `cascade_cyclic_layer` /
   `cascade_aperiodic_layer` level by level on the coordinates, with prefix
   instantiations for drivers; the guessing `accOrAnd`.
5. `LetterWordAssembly.lean` — the top conjunction over start configurations;
   size/depth bookkeeping; `letterWordACCGen_impl`.

Each file is independently buildable and none requires the interval geometry
beyond H1/H2; E2-b (rotation form of H1/H2 via HMV L9–L11 for generators) can
proceed in parallel.
