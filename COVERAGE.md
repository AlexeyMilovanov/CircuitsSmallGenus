# Coverage

## Frozen exact model

- `AllenderOQ3/Model.lean`: exact corrected ADR, rotation-genus, ACC, and OQ3
  definitions.
- `AllenderOQ3/Incidence.lean`: finite common arc-word certificate.
- `AllenderOQ3/ExternalFacts.lean`: three frozen principle signatures; rotation attainment is kernel-proved and ExternalFacts is sorry-free with one internal hole.

## Active target

- `turing_candidate_000003_of_principles`: internal conditional proof target.
- `turing_candidate_000003`: exact final theorem, wired to one proved principle
  and the external facts, with one internal hole remaining.

## Internal milestones

- **Milestone 1a** (Deterministic ADR valuation), in
  `AllenderOQ3.Internal.Semantics` — reuse these; do not re-prove:
  - `edge_layer_lt` — every edge strictly increases the layer.
  - `adrValuation_unique` — `ADRValuation c x ·` has at most one solution
    (strong induction on `c.layer`; usable on later-constructed circuits).
  - `adrValuation_exists` (via helper `adrValuation_exists_below`) — a solution
    exists.
  - `evalADR c hc x` — the canonical noncomputable evaluation, with
    `adrValuation_iff_eq_evalADR` characterizing it.
  - `adrAccepts_iff` — `ADRAccepts c x ↔ evalADR c hc x c.output = true`.

- **Milestone 1b** (Directed layer geometry), in `AllenderOQ3.Internal.LayerPath`:
  - `EdgeReach` — reflexive-transitive closure of the *directed* edge relation.
  - `edgeReach_layer_le` — directed reachability never lowers the layer.
  - `edgeReach_meets_layer` — discrete intermediate value theorem: every layer
    between the endpoints of a directed path is attained on that path.

- **Milestone 1c** (Subcircuit restriction), in `AllenderOQ3.Internal.Subcircuit`:
  - `SubEmbedding` — injective, predecessor-closed selection of gates.
  - `restrict` — induced subcircuit, with `restrict_kind/layer/edge` simp lemmas.
  - `wellFormed_restrict`, `totalWidth_restrict` — well-formedness and width are
    preserved.
  - `eval_restrict`, `adrAccepts_restrict` — the restricted circuit computes the
    same values as the original at every retained gate.

- **Milestone 1d** (Greedy piercing), in `AllenderOQ3.Internal.IntervalPiercing`:
  - `PairwiseDisjointIntervals`, `greedy_disjoint_subfamily`, `greedy_pierce` —
    a finite family of closed integer intervals has a pairwise disjoint
    subfamily `J` and an equinumerous piercing set `P`.

- **Milestone 1e** (Orbit bounds), in `AllenderOQ3.Internal.OrbitCount`:
  - `exists_minRep`, `minRep_unique` — canonical minimal-rank representative for finite equivalence relations.
  - `vertexReachable_equiv` — undirected graph reachability is an equivalence relation.
  - `componentCount_pos`, `componentCount_ge_of_pairwise_unreachable` — bounding connected component count from below via minimal representatives.
  - `permCycleCount_pos` — similar counting for equivalence classes of finite permutation orbits.

  Still open: the main assembly `turing_candidate_000003_of_principles`.

- **Milestone 1f** (Ancestor pruning), in `AllenderOQ3.Internal.Prune`:
  - `subEmbeddingOfFinset` — turns a predecessor-closed `Finset` of gates into a
    `SubEmbedding`, so `restrict` applies to a concrete gate set (built from
    `Finset.equivFin`).
  - `ancestorSet`, `mem_ancestorSet`, `output_mem_ancestorSet`,
    `ancestorSet_predClosed` — the directed ancestor cone of the output (via
    `EdgeReach`, never the undirected `VertexReachable`) and its
    predecessor-closure.
  - `width_restrict` — computation-width transport along `restrict`, mirroring
    the already proven `totalWidth_restrict`.
  - `prunedCircuit`, `wellFormed_prunedCircuit`, `adrAccepts_prunedCircuit`,
    `totalWidth_prunedCircuit`, `width_prunedCircuit`,
    `gateCount_prunedCircuit_le`, `edgeReach_output_of_pruned` — the
    ancestor-pruned circuit: well-formed, accepting exactly the same inputs, with
    both width bounds and the gate count preserved, and every remaining gate
    reaching the output.
  - `layer_le_output_of_pruned`, `gateCount_le_of_totalWidth`,
    `gateCount_prunedCircuit_le_of_totalWidth` — every pruned gate lies at or
    below the output layer, and a layered circuit of total width `w` with all
    layers `≤ L` has at most `(L + 1) * w` gates, giving a size bound for the
    pruned circuit.

- **Milestone 2** (Layer compression and total width bridge), in
  `AllenderOQ3.Internal.LayerCompress` and `AllenderOQ3.Internal.TotalWidth`.
  Proven (reuse these; do not re-prove):
  - `exists_min_gate` — some gate attains the minimum layer.  **New this iteration:**
    proved from the finite minimal-representative principle `exists_minRep`
    (`OrbitCount`) with the trivial equivalence, avoiding all `Finset.inf'` API.
  - `minActiveLayer` — the minimum layer occupied by any gate.  **Redefined this
    iteration** through `exists_min_gate`/`Classical.choose` (same value as the
    previous `Finset.univ.inf' … c.layer`), so its two companion lemmas hold
    definitionally.
  - `minActiveLayer_le`, `exists_layer_eq_minActiveLayer` — **new this iteration:**
    `minActiveLayer c` is a lower bound for every gate layer and is attained.
    `minActiveLayer_le` supplies the `hm : ∀ g, m ≤ c.layer g` hypothesis that
    `wellFormed_shiftLayers`/`width_shiftLayers` require for `m = minActiveLayer c`.
  - `shiftLayers` — translating the pruned active layer interval to start at 0.
  - `wellFormed_shiftLayers` — layer translation preserves well-formedness (needs
    `hm : ∀ g, m ≤ c.layer g`).
  - `width_shiftLayers` — layer translation preserves the computation-width bound.
    Requires `hm : ∀ g, m ≤ c.layer g`.  Without `hm` the statement is *false*:
    truncated `Nat` subtraction collapses layers `0 … m` onto layer `0`, which can
    increase the width.  `hm` holds for the intended shift `m = minActiveLayer c`
    (via `minActiveLayer_le`).
  - `accepts_shiftLayers` — layer translation preserves acceptance (`Iff.rfl`).
  - `layer_occupied_of_between` — **closed this iteration:** every integer layer
    between `minActiveLayer c` and the output layer is attained by some gate
    (min-layer gate + directed discrete IVT `edgeReach_meets_layer`).
  - `layerSpan_lt_gateCount` — **closed this iteration:** the active layer span is
    strictly below the gate count, eliminating sparse layer labels (the occupied
    layers inject `Icc (minActiveLayer c) (layer output)` into `image c.layer`).
  - `literal_succ_isComputation` (with helper `isComputation_eq_false`) — the
    target of an edge out of a literal gate is a computation gate.

  Now closed (previously mislabelled as open here; all `sorry`-free — reuse, do
  not re-prove):
  - `genus_shiftLayers` (`LayerCompress`) — layer translation preserves rotation
    genus, via a field-by-field rotation transport (`CircuitDart`,
    `UnderlyingAdj`, `componentCount`, `underlyingEdgeCount`,
    `isolatedVertexCount`, `facePermutation`, `gateCount` are all defeq across
    `shiftLayers c m`/`c`).
  - `card_live_literals_le`, `totalWidth_of_computationWidth` (`TotalWidth`) —
    bounding total width via computation width and literal fan-in bounds.

- **Milestone 4 opener** (Genus budget, §3), in
  `AllenderOQ3.Internal.GenusBudget` — `sorry`-free, reuse:
  - `rotationPlanar_iff_genus_zero` — `RotationPlanar c ↔ orientableCircuitGenus
    c = 0` (forward via `Nat.sInf_le` on the genus set; backward via
    `exists_rotation_genus_eq`).
  - `not_rotationPlanar_imp_genus_pos` — `¬ RotationPlanar c → 1 ≤
    orientableCircuitGenus c`, the per-component base contribution of the packing
    argument.
  - `genus_packing` — `r` pairwise-disjoint connected non-rotation-planar induced
    subgraphs `⟹ r ≤ orientableCircuitGenus c` (the only genus-packing statement
    §4 needs; no full BHKY additivity).  Supporting files `EulerDefect`,
    `BlockGenus`, `BlockMerge`, `ComponentBlock` are `sorry`-free and feed it.

- **ACC-side semantics** (mirror of Milestone 1a for `ACCCircuit`), in
  `AllenderOQ3.Internal.ACCSemantics` — `sorry`-free, reuse:
  - `accValuation_unique`, `accValuation_exists` (via `accValuation_exists_below`),
    `evalACC`, `accValuation_iff_eq_evalACC`, `accAccepts_iff` — deterministic ACC
    evaluation, covering the `notGate` and `modGate` cases in addition to the ADR
    ones.

- **Milestone 1b extension** (Undirected layer geometry), in
  `AllenderOQ3.Internal.LayerPath` — `sorry`-free, reuse:
  - `underlyingAdj_layer_succ` — every undirected adjacency shifts the layer by
    exactly one in one direction or the other.
  - `connected_meets_layer` — discrete intermediate value theorem for the
    *undirected* graph: if `v` is reachable from `u` then every layer between the
    layers of `u` and `v` is realised by a vertex still connected to `u`.

- **ACC assembly combinators**, in `AllenderOQ3.Internal.ACCBuild` — `sorry`-free,
  reuse:
  - `accUnion` — disjoint union of two `ACC[m]` circuits over the same inputs
    (left gates via `Fin.castAdd`, right gates via `Fin.natAdd`, no cross edges,
    layers unchanged, output inherited from the left circuit), with the
    `kind`/`layer`/`edge` simp lemmas and `accUnion_edge_to_left/_right`.
  - `wellFormedACC_accUnion`, `accUnion_layer_le` — well-formedness (including the
    layer-zero-iff-literal and unique-`notGate`-input conditions) and a common
    depth bound are preserved; `accUnion_gateCount` gives the size.
  - `accValuation_accUnion`, `evalACC_accUnion_left/_right`, `accAccepts_accUnion`
    — gluing valuations, restriction of the canonical valuation to each side, and
    the acceptance transfer.

- **Bounded-width configurations**, in `AllenderOQ3.Internal.StateRelation` —
  `sorry`-free, reuse.  Refit this iteration to the corrected §5 semantics
  ("literal values are functions of the original input and are never part of
  the carried state"):
  - `LayerIndexing`, `State`, `PaddedValid` — a slot `Fin gateCount → Fin w`
    that is injective **only on computation gates of a common layer**
    (`injOnLayer`), width-`w` configurations, and the padding predicate.
    NOTE: `LayerIndexing c w` is inhabited only when `0 < w` (a literal gate also
    needs a slot, but no `Fin 0` exists while `gateCount ≥ 1`).  Producing one
    from `ADRHasWidthAtMost c w` together with `0 < w` is now **done**:
    `exists_layerIndexing_of_width` (B0a) in
    `AllenderOQ3.Internal.WidthDiagnostic` — the acceptance test that this
    machinery is instantiable from the OQ3 hypothesis (which supplies `0 < width`).
    The slot of a computation gate is its rank among the computation gates of its
    own layer; literal gates are parked in slot `0`.
  - `predValue`, `GateStepValue`, `OneStep` — the purely local transition
    relation between the configuration of layer `i` and that of layer `i + 1`;
    `predValue` reads a **literal** predecessor directly from the input `x` and a
    **computation** predecessor from the carried state `s`.
  - `oneStep_deterministic` — the successor configuration is unique.
  - `stateOf`, `stateOf_slot`, `paddedValid_stateOf`, `oneStep_stateOf` — the
    configurations read off a genuine `ADRValuation` satisfy the relation, so it
    is not vacuous.  `stateOf`/`stateOf_slot` range over computation gates only,
    and `stateOf_slot` therefore requires the read gate to be a computation gate.

- **Slot assignment existence (B0a)**, in `AllenderOQ3.Internal.WidthDiagnostic`
  — `sorry`-free, reuse:
  - `exists_layerIndexing_of_width` — `ADRHasWidthAtMost c w` and `0 < w` give
    `Nonempty (LayerIndexing c w)`.

- **Ceiling-division chain collapse (§9)**, in
  `AllenderOQ3.Internal.CeilDivChain` — `sorry`-free, reuse:
  - `ceilDivStep`, `ceilDivStep_le` — one merging round `m ↦ ⌈m / B⌉` divides the
    bound by `B`.
  - `iterate_ceilDiv_le` — `k` rounds take a count bounded by `C * B ^ k` down to
    `C`; with `C = 1` this is the "chain collapses in `⌈log_B m₀⌉` rounds" fact.

- **Literal-output branch of the conditional**, in
  `AllenderOQ3.Internal.Assembly`:
  - `acc_of_literal_output` — if `c.kind c.output = .literal i b` then
    `literalACC n i b` computes the same Boolean function as `c`.  Pairs with the
    `h_out_comp` computation-output theorems to case-split
    `conditional_of_bridge`.

- **Milestone 4 continued** (Edge budget, §3), in
  `AllenderOQ3.Internal.EdgeBudget` — `sorry`-free, reuse:
  - `deleteEdgeNat`, `deleteEdges` — single and iterated edge deletion addressed
    by raw endpoint indices (so deletion can be folded over a list), with
    `deleteEdgeNat_eq_deleteEdge` / `deleteEdgeNat_eq_self` identifying them with
    the `Surgery`/`DeleteEdge` construction.
  - `genus_deleteEdgeNat_le`, `genus_deleteEdges_le` — deleting any set of edges
    never increases the rotation genus.
  - `wellFormed_deleteEdges`, `width_deleteEdges`, `deleteEdges_gateCount` —
    well-formedness, computation width and gate count are preserved.
  - `rotationPlanar_deleteEdges` — a rotation-planar circuit stays rotation-planar
    after deleting any set of edges.

- **Milestone 6** (Layer planarizer, §4), in
  `AllenderOQ3.Internal.LayerPlanarizer` — `sorry`-free, reuse (this is the real
  proof; the earlier `: True` stub is gone):
  - `deleteLayers` (+ `wellFormed_deleteLayers`, `width_deleteLayers`, edge simp
    lemmas) — delete every gate on a chosen layer set by isolating it.
  - `connected_meets_interval`, `disjoint_intervals_imp_vertex_disjoint`,
    `layerLo`/`layerHi` and their membership lemmas — layer intervals of a set.
  - `layerPlanarizer` — for well-formed `c` with `orientableCircuitGenus c ≤ g`
    there is `P` with `P.card ≤ g` and `RotationPlanar (deleteLayers c P)`
    (greedy piercing of the nonplanar-component intervals + `genus_packing`).

- **Milestone 7** (Bounded-width relation chain, §5–§6, §8–§9), `sorry`-free:
  - `AllenderOQ3.Internal.StateChain`: `InitState`, `Reach` (block relation),
    `reach_add` (composition), `reach_deterministic`, `adrAccepts_iff_reach`.
    Post-refit, `adrAccepts_iff_reach` carries the hypothesis
    `h_out_comp : (c.kind c.output).isComputation = true` — the nontrivial
    computation-output case of §2; a literal output is handled separately by
    `output_literal_of_width_zero`/`literalACC`.
  - `AllenderOQ3.Internal.Blocking`: `reach_blocks`, `adrAccepts_iff_blocks` —
    acceptance as an OR (over `q+1` config sequences) of AND (over `q` blocks of
    length `B`) of constant-size relations; `adrAccepts_iff_blocks` also carries
    the `h_out_comp` hypothesis.
  - `AllenderOQ3.Internal.BlockLocality`: `relevantInputs`, `blockGates`,
    `reach_congr_relevantInputs`, `card_relevantInputs_le`, `card_blockGates_le` —
    a block relation depends only on a bounded set of inputs.  Post-refit the two
    counting bounds are stated over `TotalWidthAtMost c w` (they count literal
    gates), so they apply to circuits of bounded **total** width (e.g. the
    post-N4 refined core), not directly to the raw arbitrary-fan-in OQ3 source.
  - `AllenderOQ3.Internal.LocalPredicate`: `localCircuit`, `exists_local_acc`,
    `accTruthTable_layer_le`, `accTruthTable_gateCount_le` — an ACC circuit for a
    local predicate on `r` relevant inputs, with depth/size bounds.
  - `AllenderOQ3.Internal.CutChain` (§6): `cutSet`, `mem_cutSet`
    (`i ∈ cutSet P ↔ ∃ j ∈ P, i = j ∨ i = j + 1`), `card_cutSet_le`
    (`(cutSet P).card ≤ 2 * P.card`); the regular/exceptional decomposition
    types `CutSequence`/`ComposeChain` with `composeChain_iff_reach` (a cut
    sequence composes to exactly the block relation `Reach idx x i (j - i)`),
    `cutSequence_le`, and `exists_cutSequence` (a length-one-gap chain always
    exists), plus the canonical maximal-gap chain and its relation count:
    `numRel`, `cutCount`, `cutCount_succ_of_mem`, `cutCount_eq_of_gap`,
    `exists_cutSequence_le` (a chain on `[i, j]` with
    `numRel seq ≤ 2 * cutCount X i j + 1`) and `exists_cutSequence_cutSet_le`
    (`numRel seq ≤ 4 * P.card + 1` for `X = cutSet P`, i.e. `O(g)`; the exact
    `≤ 3g+3` constant of the paper is not needed).  Still to build: the ACC
    assembly of the chain.

- **ACC composition combinators**, in `AllenderOQ3.Internal.ACCJoin` and
  `AllenderOQ3.Internal.ACCTruthTable` — `sorry`-free, reuse:
  - `accJoin`, `accOrAnd`, `wellFormedACC_accOrAnd`, `accOrAnd_layer_le`,
    `accAccepts_accOrAnd` — depth-two OR-of-AND composition of ACC blocks (the
    §9 round operator).
  - `accTruthTable` (+ `wellFormedACC_`/`evalACC_`/`accAccepts_accTruthTable`) —
    depth-two DNF ACC circuit deciding any decidable predicate on `Fin n → Bool`
    (§9 `B < 2`, §10 small-`n` and `n = 0`).

## Target contract (the planar bridge)

The single anonymous `sorry` in `Target.lean` was split into two strictly smaller
named obligations along the seam that isolates the external facts.  The seam type
`PlanarBridgeStatement` and the proved base pieces stay in
`AllenderOQ3.Internal.Assembly`; the two cruxes were relocated (iteration 12) into
their own terminal files so the consumer can import the whole §8–§9 ACC toolchain
without an import cycle: `AllenderOQ3.bridge_of_principles` lives in
`AllenderOQ3/Internal/Bridge.lean` and `AllenderOQ3.conditional_of_bridge` in
`AllenderOQ3/Internal/FinalAssembly.lean` (both in `namespace AllenderOQ3`, so the
fully qualified names — and `Target.lean` — are unchanged):

- `PlanarBridgeStatement : Prop` — for each computation width `w`, uniform
  `M, d, e` compiling every well-formed rotation-planar width-`w` ADR circuit to
  an equivalent `ACC[M]` circuit of depth `≤ d` and size `≤ (|C|+1)^e`
  (`docs/MATHEMATICAL_PROOF.md` §7).
- `bridge_of_principles : (Fact1) → (Fact2) → (Fact3) → PlanarBridgeStatement`
  (§7; still open) and
  `conditional_of_bridge : PlanarBridgeStatement → AllenderOQ3ConditionalStatement`
  (§3–6, §8–10, with §7 granted; still open).

`turing_candidate_000003_of_principles` is now
`fun h1 h2 h3 => conditional_of_bridge (bridge_of_principles h1 h2 h3) h1 h2 h3`.

Proven pieces of the bridge (in `AllenderOQ3.Internal.Assembly`, `sorry`-free —
reuse, do not re-prove):

- `output_literal_of_width_zero` — at computation width `0` the output gate is a
  literal (the filter witnessing a computation gate at its own layer would be a
  member of an empty set).
- `literalACC`, `wellFormedACC_literalACC`, `accAccepts_literalACC` — the one-gate
  `ACC[2]` circuit computing a single literal, well-formed and with its acceptance
  characterised.
- `bridge_base` — the `w = 0` case of `PlanarBridgeStatement`, with witnesses
  `M = 2`, `d = 0`, `e = 0`.
- `properLayered_of_wellFormed` — `WellFormedADR c → ProperLayered c`, the shape
  needed to invoke external fact 2.
- `bridge_of_normalized` — external facts 2 and 3 composed (§7.5): for an
  `HMVNormal`, rotation-planar, single-source/single-sink circuit of total width
  `≤ W` one gets the uniform `ACC[M]` simulation.  What remains for
  `bridge_of_principles` is exactly the normalization of an arbitrary well-formed
  rotation-planar width-`w` circuit into that shape.

There were three temporary internal `sorry`s (see the iteration-16 note at the end:
`conditional_of_bridge` is now proved, so only the first two remain):

- `bridge_of_principles` (§7, the crux, in `Internal/Bridge.lean`) and
  `conditional_of_bridge` (§3–6, §8–10, in `Internal/FinalAssembly.lean`) — both
  faithful statements.
- `FaninReduce.incidenceRefinement` (§7.4, N4) — a faithful interface, now
  carrying **N4 property 2**.  Besides `HMVNormal c'`,
  `TotalWidthAtMost c' ((F+1)*W)`, `Nonempty (IncidenceCylinder c')`, and
  `c'.output = emb c.output`, its conclusion asserts the value-preservation clause
  `∀ g, vc' (emb g) = vc g`, relating any `ADRValuation` of `c'` on
  `Fin.addCases x y` to the `PortAugmentedADRValuation` of `c` on `(x, y)`
  (the port-augmented semantics defined in the same file).  It is therefore no
  longer vacuous; only its proof is open.  Not yet imported by either target.
§8 is now closed: `PlanarBlock.planarBlockRelation` (B2c) is **proved**, and with it
`PlanarBlock.exists_acc_planarBlock` (B2b), which is its per-`(k, l, s, t)`
specialization.  B2c builds, from the proved single-bit relation
`PlanarBlock.planarBlockBit`, a width-`w` conjunction pinning the whole boundary state
`t`: for each slot occupied by a computation gate of layer `l` the corresponding
single-bit circuit (negated, via the new `ACCNot.accNot`, when `t` is `false` there),
and a constant for each unoccupied slot (justified by `StateChain.reach_padded`).  The
conjunction is `ACCJoin.accJoin … .andGate`, its correctness comes from
`StateChain.reach_iff_bits` (determinism plus totality `StateChain.exists_reach` of the
block relation), and the size bound from `PlanarBlock.pow_absorb`.

`PolylogCompose` (§9) no longer has `: True` stubs: its round-count arithmetic is the
proved `CeilDivChain.iterate_ceilDiv_le`, packaged for §9 as the proved
`polylogCompose_collapse` (`k + 1` rounds suffice above the cutoff `2 * C ≤ B`).  The
B3a/B3c ACC-composition leaves are now proved as well: `ACCCompose.accComposeMany` is the
`B`-ary round (one `accOrAnd` over candidate intermediate-state paths) with semantics
`accAccepts_accComposeMany`, well-formedness `wellFormedACC_accComposeMany` and added depth
`2` (`accComposeMany_layer_le`); `ACCChain.accChainPow` iterates it, realizing a chain of
`B ^ r` relations in depth `d + 2 * r` (`accAccepts_accChainPow`, `accChainPow_layer_le`,
`wellFormedACC_accChainPow`), the chain semantics being the relational composite
`ACCChain.StepChain`.  Padding with the identity relation (`accChainPad`) gives the §9
collapse `accAccepts_accChainCollapse`: a chain of `m ≤ C * B ^ k` relations of depth `≤ d`
becomes a single `ACC[M]` circuit of depth `≤ d + 2 * (k + 1)`, the round count being the
one fixed by `polylogCompose_collapse`.  `ACCCompose.accComposeTwo` remains as the `B = 2`
special case.  Nothing in the main assembly depends on these yet.  `PlanarBlock`
does already carry the B2a block surgery `hardwireState` — mask the block to
layers `[k, l] \ P` (via `maskCircuit`/`blockMask`), then hardwire the layer-`k`
computation gates to nullary `andGate`/`orGate` according to the start state `s`
— together with `wellFormedADR_hardwireState`, `width_hardwireState`
(`TotalWidthAtMost` preserved), `genus_hardwireState`/`rotationPlanar_hardwireState`
(genus/planarity inherited from `maskCircuit c (blockMask …)` via
`transportRotation`), and the projection simp lemmas
`hardwireState_{gateCount,layer,output,edge}`.  The boundary-layer evaluation of
the surgery is also in place: `hardwireState_edge_into_k_false` (no edge enters
layer `k`), `hardwireState_kind_at_k` (a layer-`k` computation gate is the
nullary gate dictated by `s`) and `hardwireState_value_at_k` (every valuation of
the hardwired block satisfies `value g = s (idx.slot g)` on layer `k`).  What
remains for §8 is nothing: the ACC block relation obtained from
`PlanarBridgeStatement` is proved (see B2c above).

The interior evaluation of the surgery is now **proved** (`sorry`-free), in the
`BlockEval` section of `PlanarBlock`:

- `AgreeOnLayer idx value j s` — the state `s` carries the values of `value` on the
  computation gates of layer `j`.
- `hardwireState_kind_eq`, `hardwireState_edge_eq_interior` — away from the hardwired
  layer `k` the block keeps the gate kinds of `c`, and on a `P`-free interval it keeps
  every edge of `c` into an interior gate.
- `predValue_of_agree`, `gateStepValue_iff_value`, `oneStep_of_agree`,
  `agree_of_oneStep` — the local step relation of `c` and the block's own equations
  agree on the interior.
- `exists_reach_of_agree`, `agree_of_reach` — the two halves of the induction along the
  interval.
- `adrAccepts_hardwireState_iff_reach` — the payoff: for `k ≤ l`, an interval `[k, l]`
  disjoint from `P`, and an output computation gate on layer `l`,
  `ADRAccepts (hardwireState c idx P k l s outGate) x ↔
   ∃ t, Reach idx x k (l - k) s t ∧ t (idx.slot outGate) = true`.

On top of these, `planarBlockBit` is proved: assuming the planar bridge
(`PlanarBridgeStatement`), a well-formed circuit `c` of computation width `≤ wc` whose
`P`-deleted graph is rotation-planar admits parameters `M, d, e` — extracted from the
bridge at width `wc` once, hence uniform in the interval, the boundary state and the
output gate — such that for every `P`-free interval `[k, l]`, every boundary state `s`
and every output computation gate on layer `l` there is an `ACC[M]` circuit of depth
`≤ d` and size `≤ (c.gateCount + 1) ^ e` deciding
`∃ t, Reach idx x k (l - k) s t ∧ t (idx.slot outGate) = true`.  This is the single
output-bit case of B2c; what B2c adds — and now proves — is the conjunction over all
`w` slots pinning the whole boundary state `t`.

Two further §8 prerequisites are also proved: `adrHasWidthAtMost_hardwireState`
(computation width, the notion `PlanarBridgeStatement` consumes, is preserved by the
surgery — via `hardwireState_isComputation`) and `rotationPlanar_maskCircuit_block`
(the masked block is a subgraph of the planarized `deleteLayers c P`, so it is planar,
discharging the hypothesis of `rotationPlanar_hardwireState`).

## Remaining internal obligations (concrete sub-leaves, iteration 14 review)

(Superseded by the iteration-16 note below: `conditional_of_bridge` is now proved.)
At the time of the iteration-14 review all three temporary internal `sorry`s remained
(`bridge_of_principles`, `FaninReduce.incidenceRefinement`, `conditional_of_bridge`);
the build is green.
The dependency inventory below is verified against the sources this iteration.

**`conditional_of_bridge` (Stream C, §3–6/§8–10).**  Every prerequisite is proved
and `sorry`-free — `adrAccepts_iff_reach`/`adrAccepts_iff_blocks` (StateChain/Blocking),
the §6 cut decomposition `composeChain_iff_reach` + `exists_cutSequence_cutSet_le`
(`CutChain`, `≤ 4·|P|+1` relations), the ACC relations `exists_acc_{initState,oneStep,
outputState}` (`ACCOneStep`, `ACC[2]`, depth ≤ 3, size `≤ 10·|C|+10`), the block relation
`planarBlockRelation` (`PlanarBlock`, deciding `Reach idx x k (l-k) s t`), the
common-modulus lift `accModulusLift` + `evalACC_accModulusLift_of_pos` +
`accModulusLift_{layer_le,gateCount_le}` (`ModulusLift`), the §9 collapse
`accAccepts_accChainCollapse` + `wellFormedACC_accChainCollapse` +
`accChainCollapse_layer_le` (`ACCChain`), the round-count `polylogCompose_collapse`,
the small-`n`/`n=0` truth table `accTruthTable`, and the literal-output base
`acc_of_literal_output`.  Two concrete sub-leaves remain:

  1. **Collapsed-chain polynomial size bound** (the one missing analytic lemma).
     `ACCCompose.accComposeMany_gateCount` gives the exact count but there is no
     `≤ polynomial` bound.  Needed: `accComposeMany_gateCount_le` (one round:
     `gateCount ≤ Fintype.card (Fin (B+1) → State w) · (B·G + 1) + 1`, with
     `Fintype.card (Fin (B+1) → State w) = (2^w)^(B+1)`) and the induction
     `accChainPow_gateCount_le` over the `k+1` rounds; then, with `B = Nat.log2 (n+1)`
     and fixed `w, k`, `(2^w)^(B+1)·(B+1)^{k+1}·G₀ ≤ (n+1)^e` for a fixed `e`.
  2. **Final glue.**  Prune+compress to width `w`; `layerPlanarizer` for `n ≥ threshold`;
     rewrite acceptance via `adrAccepts_iff_reach` + `composeChain_iff_reach`; build the
     `Nat → State w → State w → ACCCircuit n M` relation family (init / exceptional
     one-step / planar block / output test) all lifted to a common modulus (`L = 2·M`);
     apply `accAccepts_accChainCollapse`; read the `(ζ, ζ)` entry; discharge `n<threshold`
     and `n=0` by `accTruthTable`; assemble the family with `Classical.choice` and package
     `InNonuniformACC0`.

**`bridge_of_principles` (Stream B, §7).**  `bridge_base` (w=0) and `bridge_of_normalized`
(facts 2⊕3, §7.5) are proved; `PortSubst.accPortSubst` (§7.5) and `ModulusLift` (§7.6) are
reusable.  Open prerequisites: **N4** `FaninReduce.incidenceRefinement` (§7.4, the long
pole; interface faithful, now carrying property 2), §7.2 core extraction, §7.3 beta-port
circuits + width induction, and the §7.6 quantitative recurrence `S_w,d_w,p_w`.

## Iteration 15: Stream C plumbing proved (`sorry`-free)

The following are new, fully proved results.  They close leaf 1 of the iteration-14
packet (the collapsed-chain size bound) and, beyond it, most of the *mechanical* part
of leaf 2, so that what is left in `conditional_of_bridge` is circuit preprocessing and
parameter bookkeeping rather than chain plumbing.

**Size of the §9 collapse (`ACCCompose.lean`, `ACCChain.lean`).**
* `card_statePath` — `Fintype.card (Fin (B+1) → State w) = (2 ^ w) ^ (B + 1)`.
* `accComposeMany_gateCount_le` — one `B`-ary round: `≤ N * (B * G + 1) + 1`.
* `accChainPow_gateCount_le` — `r` rounds: `≤ (N * (B + 1) + 1) ^ r * (G₀ + 1)`.
* `accChainPad_gateCount_le`, `accChainCollapse_gateCount_le` — the same bound for the
  padded collapse.
* `collapse_size_poly`, `accChainCollapse_gateCount_poly` — with `B = ⌊log₂ (n+1)⌋`,
  `G₀ ≤ (n+1) ^ e₀`, `1 ≤ n`, the collapse has size `≤ (n+1) ^ ((2w+2)(k+1)+e₀+1)`.
* `exists_acc_relation_family`, `exists_acc_stepChain` — the packaged §9 statement:
  chain of `m ≤ C · B ^ k` relations, each an `ACC[M]` circuit of depth `≤ d` and size
  `≤ G ≤ (n+1)^e₀`, collapses to one `ACC[M]` circuit of depth `≤ d + 2(k+1)` and
  polynomial size.
* `bracketRel`, `stepChain_bracketRel` — folding the initial-state relation and the
  output test into the chain, so acceptance is read at a single base point `(z, z)`.

**Flattening the §6 decomposition (`CutStepChain.lean`, new file).**
* `cutRel` — the `Nat`-indexed family of relations of a `CutSequence`.
* `stepChain_cutRel_iff_composeChain` — the flat `StepChain` composite equals
  `ComposeChain`.
* `adrAccepts_iff_stepChain_bracketRel` — `ADRAccepts c x` iff the bracketed flat chain
  connects `z` to `z`.
* `ACCRealizes`, `accRealizes_false`, `accRealizes_congr`, `accRealizes_modulusLift`
  (common-modulus lifting), `exists_acc_cutRel`, `exists_acc_bracketRel`.
* `exists_acc_adrAccepts` — Stream C assembled at the relational level: from
  `ACCRealizes` for (i) one-step relations at cut layers, (ii) gap block relations,
  (iii) the initial-state relation and (iv) the output test, plus the counting
  hypotheses, one obtains a single `ACC[M]` circuit of depth `≤ d + 2(k+1)` and size
  `≤ (n+1) ^ ((2w+2)(k+1)+e₀+1)` deciding `ADRAccepts c`.

**Small inputs and family packaging (`ACCTruthTable.lean`, `FamilyPackage.lean`).**
* `accTruthTable_gateCount_zero/_succ`, `accTruthTable_gateCount_le_pow` — below a fixed
  threshold the truth-table circuits fit one polynomial size bound.
* `inNonuniformACC0_of_large_inputs` — splice a family defined for `n ≥ threshold` with
  truth tables below it and conclude `InNonuniformACC0`.

**Cutoff arithmetic (`PolylogCompose.lean`).**
* `le_log2_succ_of_pow_le` — `c ≤ ⌊log₂ (n+1)⌋` once `2 ^ c ≤ n`, which discharges
  `2 * C ≤ B` above a threshold.

## Iteration 16: `conditional_of_bridge` is **proved** (`sorry`-free)

Stream C is closed.  `AllenderOQ3.conditional_of_bridge` (in
`AllenderOQ3/Internal/FinalAssembly.lean`) no longer has a `sorry`; only
`bridge_of_principles` (§7) and `FaninReduce.incidenceRefinement` (§7.4, N4) remain among
the temporary internal obligations.  `#print axioms AllenderOQ3.conditional_of_bridge`
reports `[propext, Classical.choice, Quot.sound]`.

New supporting material:

* **Bridge parameters made uniform** (`Assembly.lean`, `PlanarBlock.lean`).
  `PlanarBridgeAt w M d e` names the body of `PlanarBridgeStatement`, so
  `PlanarBridgeStatement = ∀ w, ∃ M d e, 2 ≤ M ∧ PlanarBridgeAt w M d e` (definitionally
  the previous statement).  `planarBlockBit_at` and `planarBlockRelation_at` take the
  bridge data with its parameters *already fixed*; the original `planarBlockBit` /
  `planarBlockRelation` are one-line corollaries.  This is what lets the whole circuit
  family share one modulus `2 * M`, one depth and one size exponent.
* **Glue toolkit** (`Glue.lean`, new file):
  `accRealizes_mono`, `accRealizes_composeStates` (two-step composition of realizations
  over the intermediate state, via `accComposeTwo`), the polynomial-bound arithmetic
  `const_mul_pow_le`, `pow_add_pow_le`, `succ_le_pow_succ`, the exponent
  `assemblySizeExp`, `reach_one_iff`, and `notMem_of_gap`.
* **The gap/cut interface** (open item 3 of the previous iteration) is resolved by
  `notMem_of_gap`: if the open interval `(p, q)` avoids `cutSet P = P ∪ (P+1)` and
  `q ≥ p + 2`, then the *closed* interval `[p, q-1]` avoids `P` (the endpoint `p` is
  excluded because `p ∈ P` would put `p+1 ∈ cutSet P` inside the gap).  A gap relation is
  therefore realized as a `planarBlockRelation_at` block on `[p, q-1]` composed with one
  `exists_acc_oneStep` transition at layer `q-1`; a gap of length one is a bare one-step
  relation.
* **`acc_of_bridge_at_length`** (`FinalAssembly.lean`) — the per-input-length core:
  slot assignment (`exists_layerIndexing_of_width`), §4 planarizer (`layerPlanarizer`),
  §8 block relations and §5 local relations lifted to the common modulus `2 * M`
  (`accRealizes_modulusLift`), then the §6/§9 collapse `exists_acc_adrAccepts`.  No
  prune/layer-compress step is needed: the maximal-gap cut sequence has `O(|P|)` relations
  regardless of sparse layers, and the size bound comes straight from the hypothesis
  `(family n).gateCount ≤ (n+1)^sizeExponent`.
* **Parameters.** `C = 4 * factor + 3`, `k = logExponent`,
  `threshold' = max threshold (2 ^ (2 * C))` (so `le_log2_succ_of_pow_le` discharges
  `2 * C ≤ ⌊log₂ (n+1)⌋`), and the literal-output branch is handled by
  `acc_of_literal_output` at modulus `2` lifted to `2 * M`; the two branches are merged
  with `max` on the depth and on the size exponent before
  `inNonuniformACC0_of_large_inputs`.

## Iteration 16 (second leaf): §7.2 core extraction

`AllenderOQ3/Internal/CoreExtract.lean` (new file, `sorry`-free) starts Stream B's §7.2:

* `isComputation_of_edge`, `edgeReach_eq_of_layer_le` — a gate with an incoming edge is a
  computation gate; a directed path that does not raise the layer is trivial.
* `coreSet c v o` / `mem_coreSet` / `coreSet_forward` — the cylindrical core through `v`:
  the computation gates on a directed path from `v` to `o`.
* `exists_mem_coreSet_layer` — the core meets every layer between `v` and `o`.
* `exists_core_width_lt` — **the §7.2 width drop**: in a circuit where every gate reaches
  the output (i.e. after ancestor pruning, cf. `Prune.edgeReach_output_of_pruned`), there is
  a computation gate `v` such that at every layer the computation gates *outside* the core
  through `v` number `< w`, i.e. the remainder `R` has computation width at most `w - 1`.
  (Stated as `card + 1 ≤ w`, which avoids truncated subtraction and also records `1 ≤ w`.)

This is the width-induction step §7.3 needs; the beta-port circuits and N4 remain open.

## Iteration 17: §7.2 core-with-ports properties and §7.6 size arithmetic

`AllenderOQ3/Internal/CorePorts.lean` is now part of the library (it is imported by
`AllenderOQ3/Internal.lean`; previously it was an orphan module that the default build
never compiled).  It is `sorry`-free, and the following new results were added to it:

* `coreSet_exists_pred`, `coreSet_exists_succ` — every core gate other than `v` has a
  predecessor in the core, and every core gate other than `o` has a successor in the core.
* `uniqueSink_coreWithPorts`, `uniqueSource_coreWithPorts` — **the §7.2 single-source /
  single-sink property**: `∃! t, IsGraphSink (coreWithPorts …) t` (the output) and
  `∃! s, IsGraphSource (coreWithPorts …) s` (the entry gate `v`).  These are exactly the
  two hypotheses `Assembly.bridge_of_normalized` consumes besides `HMVNormal`,
  planarity and the total-width bound.
* `totalWidthAtMost_coreWithPorts_of_widthAtMost` — the *total* width of the core is
  bounded by the *computation* width of the source circuit (every core gate is a
  computation gate of `c` on the same layer).  This is the width input that External
  Fact 3 needs, and it is sharper than the earlier `≤ c.gateCount` bound.
* `predecessorCount_coreWithPorts_le_orig` and the general fanin form
  `predecessorCount_coreWithPorts_le_fanin` (`≤ F` for any `F`), with the previous
  `predecessorCount_coreWithPorts_le` (`F = 2`) now a corollary.

`AllenderOQ3/Internal/BridgeArith.lean` (new file, `sorry`-free) supplies the §7.6
quantitative bookkeeping:

* `three_pow_le` — `T^a + T^b + T^k ≤ T^(max (max a b) k + 2)` for `2 ≤ T`.
* `mul_self_pow_le` — `N * (N+1)^p ≤ (N+1)^(p+1)`.
* `size_recurrence_absorb` — **the §7.6 size collapse**: from
  `S ≤ w·N·A·(N+1)^p + C·(N+1)^k + C'·(N+1)` and `1 ≤ N` one gets the pure form
  `S ≤ (N+1)^e` with `e = max (max (w·A + p + 1) (C + k)) (C' + 1) + 2`, which is the
  shape `PlanarBridgeAt` requires.

The four top-level scratch files `CorePortsTest*.lean` (never part of any build target)
were also cleaned up: they no longer contain `sorry`s or duplicate declarations.  The
`sorry`-ed scratch claim `isGraphSink_coreWithPorts_output` stated *without*
`WellFormedADR` is in fact false, and `CorePortsTest2.lean` now records the explicit
counterexample `not_isGraphSink_coreWithPorts_of_cycle` (a one-gate AND circuit with a
self-loop) together with the well-formed statement proved in `CorePorts.lean`.

The two temporary internal obligations `bridge_of_principles` (§7) and
`FaninReduce.incidenceRefinement` (§7.4, N4) remain open.

## Iteration 18: trust-audit cleanup and §7.2/§7.3 leaves (`sorry`-free)

The two temporary internal obligations `bridge_of_principles` (§7) and
`FaninReduce.incidenceRefinement` (§7.4, N4) are still open; everything listed here is new
and `sorry`-free.

**Trust audit.**  The two scratch files that still carried `sorry`s were closed:
* `CorePortsTest3.lean` — its two claims are now the renamed `_test` copies
  `totalWidthAtMost_coreWithPorts_card_test` and
  `predecessorCount_coreWithPorts_le_two_test`, the second delegating to
  `CorePorts.predecessorCount_coreWithPorts_le`.
* `CorePortsTest2.lean` — the `sorry`-ed claim (the output of `coreWithPorts` is a graph
  sink *without* `WellFormedADR`) is false, and the file now records the explicit
  counterexample `not_isGraphSink_coreWithPorts_of_selfLoop` (a one-gate AND circuit with a
  self-loop).  The correct well-formed statement stays in `CorePorts.lean`.
Both files compile cleanly with `lake env lean`.

**Fan-in from total width** (`TotalWidth.lean`, `CorePorts2.lean`).
* `predecessorCount_le_of_totalWidth` — in a properly layered circuit all predecessors of a
  gate lie on the single layer `layer g - 1`, so a total-width bound is a fan-in bound.
* `predecessorCount_coreWithPorts_le_width` — the extracted core has fan-in `≤ w` whenever
  the source circuit has computation width `≤ w`.  This supplies the `F` of the N4
  interface.
* `incidenceCylinder_coreWithPorts` — External Fact 2 applied to the core: proper layering,
  planarity and the unique source/sink of `CorePorts` give `Nonempty (IncidenceCylinder …)`.
* `width_ancestorCone_lt` no longer carries its unused `ADRHasWidthAtMost c w` hypothesis.

**Genus monotonicity under restriction** (`RestrictGenus.lean`, new file).
* `imageMask`, `maskedSubEmbedding`, `restrict_maskCircuit_imageMask` — a restriction is the
  restriction of the circuit masked to the edges inside the retained set.
* `genus_restrict_le` — restriction never increases the rotation genus (mask, then delete
  the now isolated outside gates), and `rotationPlanar_restrict` — a subcircuit of a
  rotation-planar circuit is rotation planar.  This closes the gap left by
  `genus_restrict_isolated`, which only covers isolated vertices.
* `rotationPlanar_prunedCircuit`, `rotationPlanar_ancestorCone`.
* Ancestor-cone package for the width induction: `wellFormedADR_ancestorCone`,
  `width_ancestorCone`, `gateCount_ancestorCone_le` and
  `adrAccepts_ancestorCone` (`ADRAccepts (ancestorCone c h) x ↔ evalADR c hc x h = true`).

**§7.3 beta ports** (`BetaPorts.lean`, `BetaPortACC.lean`, `BetaBridge.lean`, new files).
* `betaPort c v o value g` — the gate's own operation applied to the values of its
  predecessors *outside* the core, with `forall_pred_split` / `exists_pred_split` splitting
  the predecessors of a core gate into internal and external ones.
* `portAugmentedADRValuation_coreWithPorts` — **the §7.3 semantic statement**: every
  valuation of `c` restricts along the core embedding to a `PortAugmentedADRValuation` of
  `coreWithPorts c v o ho` with the beta values on the ports.  This is exactly the input
  consumed by `FaninReduce.incidenceRefinement`.
* `externalPreds`, `mem_externalPreds` — the external predecessors of a core gate.
* `literalACCMod`, `wellFormedACC_literalACCMod`, `accAccepts_literalACCMod`,
  `exists_acc_literal_gate` — the one-gate `ACC[M]` circuit for a literal, at an arbitrary
  modulus.
* `exists_acc_betaPort` — one unbounded `AND`/`OR` (`ACCJoin.accJoin`) over the circuits of
  the external predecessors computes the beta port; depth `d + 1`, size `≤ |c|·G + 1`.
* `exists_acc_betaPort_of_bridge` — the same with the block circuits supplied by the width
  induction hypothesis `PlanarBridgeAt w M d e` applied to the ancestor cones, giving size
  `≤ |c|·(|c|+1)^e + 1`.
* `exists_acc_betaPort_of_widthDrop` — the §7.2 width drop (`CorePorts2.width_ancestorCone_lt`)
  discharges the ancestor-cone width hypothesis, so the beta ports of the core of a
  width-`w` circuit come from the bridge at width `w - 1`.

What §7 still needs on top of this: N4 itself, the §7.5 port substitution applied to the
wrapper produced by External Fact 3, and the §7.6 parameter recurrence (whose arithmetic is
already available in `BridgeArith`).

### Interface gap noticed while assembling §7

`FaninReduce.incidenceRefinement` currently bounds only the *total width* of the refined
circuit `c'`, not its gate count.  External Fact 3 returns an `ACC` circuit of size
`≤ (c'.gateCount + 1) ^ exponent`, so without a bound of the form
`c'.gateCount ≤ K · (c.gateCount + 1)` (with `K` depending only on `F` and `W`) the §7.6
size recurrence cannot be closed: the wrapper size is not expressible in terms of the
original `|c|`.  Such a bound is available from the construction of
`docs/INCIDENCE_REFINEMENT.md` (bounded width times a bounded number of micro-layers per
old layer), so the natural next step is to add that clause to the N4 interface before
attacking `bridge_of_principles`.

## Iteration 19: `bridge_of_principles` is **proved** (§7 width induction)

Stream B is closed except for N4.  `AllenderOQ3.bridge_of_principles`
(`AllenderOQ3/Internal/Bridge.lean`) no longer has a `sorry`: it is the induction on the
computation width, with `Assembly.bridge_base` as the base case and the new
`Internal.bridge_step` as the induction step.  The only temporary internal obligation left
in the whole development is `FaninReduce.incidenceRefinement` (§7.4, N4);
`#print axioms AllenderOQ3.bridge_of_principles` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`, the `sorryAx` coming exactly from that
one interface.

**N4 interface completed** (`FaninReduce.lean`).  Following the "interface gap" noted at
the end of iteration 18, the conclusion of `incidenceRefinement` now also carries the size
clause `c'.gateCount ≤ (F + 2) * ((F + 1) * W + 1) * c.gateCount` (§5 of
`docs/INCIDENCE_REFINEMENT.md`: at most `|c|` target strips, each of at most
`⌈log₂ (F+1)⌉ + 1 ≤ F + 1` micro-layers of width at most `K = (F+1)·W`).  Without it the
§7.6 recurrence cannot be closed, because External Fact 3 measures the wrapper in terms of
`|c'|`.  Nothing was weakened: this is an extra conjunct in the conclusion.

**New file `AllenderOQ3/Internal/PruneReach.lean`** (`sorry`-free):
* `edgeReach_prunedCircuit_of_edgeReach`, `edgeReach_output_prunedCircuit` — every gate of
  `prunedCircuit c` reaches the output *inside the pruned circuit* (the ancestor cone is
  closed along directed paths to the output).  This is the hypothesis `hreach` of
  `CoreExtract.exists_core_width_lt`, which was previously available only in the form
  "reaches the output of the original circuit".

**New file `AllenderOQ3/Internal/BridgeStep.lean`** (`sorry`-free):
* `bridgeStepModulus`, `bridgeStepDepth`, `n4SizeConst`, `bridgeStepSizeExp` — the
  parameters produced by one induction step (`M = 2·M₁·M₂`, so that both the wrapper
  modulus `M₂`, the induction-hypothesis modulus `M₁` and the literal branch's modulus `2`
  divide it).
* `wrapper_size_le`, `bridgeStep_size_arith` — the §7.6 arithmetic: the wrapper size
  `(|c'|+1)^{e₂}` is `≤ (N+1)^{(K+2)e₂}` once `|c'| ≤ K·N`, and the resulting recurrence
  collapses to the pure form `(N+1)^e` via `BridgeArith.size_recurrence_absorb`.
* `accPortSubst_realizes` — the packaged §7.5 substitution: if the port circuits `B`
  compute `y x` and the wrapper `A` decides `Q x` on `Fin.addCases x (y x)`, then
  `accPortSubst A B` is well formed, has depth `≤ dA + dB + 2`, size
  `≤ 3·|A| + Σ|B i|`, and decides `Q`.
* `acc_of_computation_output` — the main case of the step: prune-free hypotheses
  (`hreach`, computation output), core extraction through the earliest computation gate,
  the beta ports from `BetaBridge.exists_acc_betaPort_of_widthDrop`, N4, External Fact 3,
  modulus lifting of both sides to `2·M₁·M₂`, port substitution, and the size collapse.
* `bridge_step` — adds the degenerate literal-output branch (via `acc_of_literal_output`
  lifted to the common modulus) and the ancestor pruning, and packages the parameters.

**New file `AllenderOQ3/Internal/IncidenceToolkit.lean`** (`sorry`-free), infrastructure
for the one remaining obligation (N4):
* `cyclicRotation_iff_isRotated` — `AllenderOQ3.CyclicRotation` is exactly Mathlib's
  `List.IsRotated`; hence `cyclicRotation_refl/symm/trans` and `cyclicRotation_of_eq`.
* `cyclicListingOfFintype` — every finite type carries a `CyclicListing`.
* `GroupedAlong key ls w` and `flatMap_filter_of_groupedAlong` — a word decomposed into
  consecutive blocks along a nodup listing is reassembled by grouping: this is the
  combinatorial content of Lemma 1 of `docs/INCIDENCE_REFINEMENT.md`.
* `arcOrderCertificate_of_eq`, `arcSource`, `arcTarget`,
  `arcOrderCertificate_of_doubleGrouped`, `incidenceCylinder_of_words` — a single arc word
  per transition, listing every arc once and grouped both along the source order and along
  the target order, *is* an incidence certificate.  This is the interface through which the
  N4 construction will discharge `Nonempty (IncidenceCylinder c')`.
* `groupedAlong_flatMap` — the converse construction: concatenating key-homogeneous blocks
  along a nodup listing produces a word grouped along that listing.
* `groupedAlong_map` — grouping transports along a relabelling of letters and keys.
* `groupedAlong_nil` and `groupedAlong_of_nodup_map_sublist` — the empty word is grouped
  along any listing, and a word whose letters have distinct keys occurring in the listing
  order is grouped along it (the singleton-block transitions of the refinement).
* `cyclicRotation_flatMap`, `nodup_of_cyclicRotation`, `mem_of_cyclicRotation` and
  `arcOrderCertificate_of_rotatedDoubleGrouped` — Lemma 1 up to rotation: the two
  groupings need only be along *rotations* of the layer listings, and the source-major and
  target-major words need only agree up to rotation.  This is the form in which a
  transition of the refinement inherits its certificate from the given one, where only the
  cyclic (not the linear) order of a checkpoint layer is fixed.
* `incidenceArc`-side reading of the semantics: `incomingArc`,
  `forall_pred_iff_forall_mem_incoming`, `exists_pred_iff_exists_mem_incoming` and
  `length_incoming_eq_predecessorCount` — for a properly layered circuit the incoming list
  of a certificate enumerates the predecessors of a target without repetition, so the set
  semantics of an AND/OR gate becomes a statement about that list, whose length is exactly
  `predecessorCount` (this is what bounds a target block by the fan-in).
* `incidenceCylinder_of_edgeFree` — the degenerate edge-free case.

**New file `AllenderOQ3/Internal/AbstractCircuit.lean`** (`sorry`-free).  `ADRCircuit`
indexes gates by `Fin gateCount`, whereas the N4 refinement wants to build its gate set as
a structured finite type (old gates + fresh ports + copy rails + fold nodes).  This file
is the bridge:
* `ADRSpec n G` — circuit data on an arbitrary finite gate type `G`; `ofSpec` transports it
  to an `ADRCircuit n` along `Fintype.equivFin G`, with `specEmb : G → Fin (ofSpec s).gateCount`
  and the simp lemmas `ofSpec_kind`, `ofSpec_layer`, `ofSpec_edge`, `ofSpec_output`,
  `ofSpec_gateCount`.
* `card_filter_ofSpec`, `predecessorCount_ofSpec`, `fanin_ofSpec`, `hmvNormal_ofSpec`,
  `totalWidth_ofSpec`, `wellFormed_ofSpec` — every structural obligation of the N4
  interface (`WellFormedADR`, `HMVNormal`, `TotalWidthAtMost`, gate count) may be checked
  on `G`.
* `SpecValuation` and `adrValuation_ofSpec_iff` — the semantics likewise.
* `SpecLayerVertex`, `SpecTransitionArc`, `specLayerVertexEquiv`, `specTransitionArcEquiv`
  and `incidenceCylinder_ofSpec` — one arc word per transition, given on `G` and grouped
  along the abstract source and target layer orders, already makes `ofSpec s`
  incidence-cylindrical.  Combined with `IncidenceToolkit`, the whole N4 construction can
  therefore be carried out, and verified, without ever touching gate numerals.

**Remaining gap after iteration 19.**  `AllenderOQ3.Internal.incidenceRefinement`
(`AllenderOQ3/Internal/FaninReduce.lean`) is still the single temporary internal `sorry`;
the three external `sorry`s present at that checkpoint were unchanged.  With the two toolkits above the
remaining work is exactly the construction of §3 of `docs/INCIDENCE_REFINEMENT.md`, and
each of its obligations now has a named interface:

1. choose the gate type `G` (checkpoint copies of the old gates, one fresh port per
   computation gate, one copy node per old arc, and the fold nodes of a strip) and the
   `ADRSpec` data on it, with new layer `stride * old layer + stage`;
2. `wellFormed_ofSpec`, `hmvNormal_ofSpec`, `fanin_ofSpec`, `totalWidth_ofSpec` and
   `ofSpec_gateCount` discharge the structural clauses from counts on `G` -- the fan-in
   input being `length_incoming_eq_predecessorCount`;
3. `adrValuation_ofSpec_iff` reduces the semantic clause to `SpecValuation`, and
   `forall_pred_iff_forall_mem_incoming` / `exists_pred_iff_exists_mem_incoming` turn the
   old gate semantics into the ordered fold over the certificate's incoming list;
4. `incidenceCylinder_ofSpec` reduces `Nonempty (IncidenceCylinder c')` to one arc word per
   new transition; `groupedAlong_flatMap`, `groupedAlong_nil`,
   `groupedAlong_of_nodup_map_sublist` and `groupedAlong_map` supply the groupings of the
   leaf, fold and checkpoint transitions, and
   `arcOrderCertificate_of_rotatedDoubleGrouped` absorbs the fact that the old certificate
   fixes only the *cyclic* order of a checkpoint layer.
## Current release status after iteration 20 and trust-boundary cleanup

- `incidenceRefinement` and the complete N4 interface are kernel-proved, including
  `HMVNormal`, total width `(F+1)W`, the explicit linear gate-count bound,
  `IncidenceCylinder`, output embedding, and port-augmented semantics.
- The conditional OQ3 theorem and every project-specific proof module contain no
  `sorry` and do not depend on `sorryAx`.
- `External.rotationZeroPlanarity` is now kernel-proved from
  `Internal.exists_rotation_genus_eq`; it no longer belongs to the trust boundary.
- Both external facts are now proved from internal holes: `hansenArcOrder` and
  `quantitativeCylindricalACC`. Only one internal hole remains.

## Iteration 5 (external-facts loop): trust-boundary repair + E1/E2 inventory

**Repair (adversarial review of the Gemini stage).**  The Gemini stage had
replaced the two actionable external proof bodies with `axiom` declarations
(`ExternalFacts.lean:35,38`) — a forbidden shortcut that fakes a green build by
turning honest `sorry` leaves into permanent unprovable assumptions.  Reverted
to the frozen reference form `theorem hansenArcOrder : HansenArcOrderPrinciple
:= by sorry` and likewise for `quantitativeCylindricalACC`.  This restores the
audited trust boundary (the two facts are honest open holes, not axioms).
The redundant scratch `AllenderOQ3/Internal/Test.lean` (a draft of
`incidenceCylinder_shiftLayers` carrying a motive `sorry`, already superseded by
the `sorry`-free version in `CylNormal.lean`) was stripped to an inert
doc-comment, and the obsolete `fix_test.sh` helper (its `StGraph.lean` sed-edits
are already live) was neutralized.

**E1 (Hansen arc order) — `sorry`-free, built via `Internal.lean`:**
- `AllenderOQ3.Internal.StGraph` — proper-layered st-preliminaries:
  `properLayered_acyclic`, `exists_pred_of_ne_source`/`exists_succ_of_ne_sink`,
  `mem_st_path`, `source_alone_in_layer`/`sink_alone_in_layer`,
  `connected_of_unique_source` (`componentCount c = 1`), `isolated_free`.
- `AllenderOQ3.Internal.DartClass` — up/down dart classification
  (`dartIsUp`, `dartIsUp_dartReverse`, `two_mul_underlyingEdgeCount`,
  `exists_updown_dart_of_internal`).
- `AllenderOQ3.Internal.DartSwitch` — Euler/Morse switch-corner counting:
  `exists_switch_of_cycle` (generic cycle lemma), `switchCount`,
  `one_le_switchCount_of_internal`, `card_internal_le_sum_switchCount`,
  `card_upDarts_eq_card_downDarts`, `card_upDarts_eq_edgeCount`.  This is the
  counting half of the corner sandwich (E1-B3).

**E2 (quantitative cylindrical ACC) — `sorry`-free, built via `Internal.lean`:**
- `AllenderOQ3.Internal.MonoidWord` — Green's right preorder `RPreorder`,
  `REquiv`, `card_RDescents_le` (≤ |M| strict R-descents along any word).
- `AllenderOQ3.Internal.TransitionMonoid` — the width-`W` transition monoid
  `TransMonoid W = (Function.End (Config W))ᵐᵒᵖ` (finite), `runTrans`, `wordEnd`,
  `prefixEnd`, `prefixEnd_RPreorder`, and `card_prefix_RDescents_le` (the E2-D2
  milestone: prefix transitions of a layer word have ≤ |TransMonoid W|
  R-descents).

**E2 normalization transport — `AllenderOQ3.Internal.CylNormal` (orphaned):**
Not yet imported by `Internal.lean`, so its content is not on the
`turing_candidate_000003` axiom path.  Proved and `sorry`-free:
`predecessorCount_restrict`, `hmvNormal_restrict/prunedCircuit/shiftLayers`,
the `shiftLayerVertex(Inv)`/`shiftTransitionArc(Inv)` transport bijections,
`cyclic_rotation_map`, `mapCyclicListing`, `mapArcOrderCertificate`, and the
full `incidenceCylinder_shiftLayers` (certificate transport through the layer
renumbering `shiftLayers`).  The **single supporting internal `sorry`** in the
whole tree is `incidenceCylinder_prunedCircuit` (E2-B1: certificate transport
through ancestor pruning), documented in place as a self-contained
`List.filter`/`List.filter_flatMap` leaf.  Recommended next step: verify
`CylNormal.lean` compiles under `lake build`, close `incidenceCylinder_prunedCircuit`,
and import `CylNormal` into `Internal.lean`.
- The final exact theorem depends on `sorryAx` only through those two frozen facts.

## Iteration 6

`AllenderOQ3.Internal.CylNormal` is now **compiled, `sorry`-free, and imported
by `Internal.lean`**.  Three things changed.

1. `incidenceCylinder_shiftLayers` did *not* compile before (three errors: two
   `simp made no progress` in `outgoing_exact`/`incoming_exact` and a
   `motive is not type correct` in `commonArcWord`).  It is reproved by
   indexing the shifted layers as `m + ell` instead of `ell + m`; then the
   successor layer `m + (ell + 1)` is *definitionally* `(m + ell) + 1`, the
   source/target listings of the transported certificate line up on the nose,
   and the whole construction is a one-line application of the already proved
   `mapArcOrderCertificate`.  New transport bijections: `shiftLV`,
   `shiftLVinv`, `shiftTA`, `shiftTAinv` (with their round-trip lemmas).

2. The former supporting internal `sorry`, `incidenceCylinder_prunedCircuit`,
   is **closed**.  It is derived from a new, more general lemma
   `incidenceCylinder_restrict`: an incidence cylinder transports through *any*
   predecessor-closed restriction `restrict c f out`.  The construction is a
   `List.filterMap` (not a `map`), built from the partial inverses
   `restrictLV` / `restrictTA` of the embeddings `embLV` / `embTA`, plus three
   generic list lemmas proved here: `cyclicRotation_filterMap`,
   `filterMap_flatMap_eq`, `flatMap_filterMap_eq`.  The two facts that make the
   common arc word survive are that every arc into a retained head has a
   retained tail (`SubEmbedding.predClosed`), so a non-retained tail contributes
   an empty outgoing block, and that filtering both sides of a `CyclicRotation`
   by the same partial map preserves it.

3. Convenience `Nonempty` forms: `nonempty_incidenceCylinder_restrict`,
   `nonempty_incidenceCylinder_prunedCircuit`,
   `nonempty_incidenceCylinder_shiftLayers`.

Status: `lake build` is green, and the **only** remaining `sorry`s in the whole
tree are the two permanent external facts `External.hansenArcOrder` and
`External.quantitativeCylindricalACC` in `AllenderOQ3/ExternalFacts.lean`.
There are now zero supporting internal holes.

## Necklace layer (E1, user session 2026-08-16): proved infrastructure — reuse, do not re-prove

`AllenderOQ3/Internal/CutNecklace.lean` (`sorry`-free except the three named
genus-zero obligations) + `NecklaceAssembly.lean`:

- `isCutDart`, `CutDart`, `cutDartReverse` — darts crossing transition `ell`.
- `dart_layer_cases` — every dart moves between adjacent layers (ProperLayered).
- First-return machinery (`firstReturnTime/_pos/_mem/_not_mem`, `firstReturnPerm`)
  — Kac-style return map of a permutation to a subset, fully proved.
- `firstReturn r ell` — face permutation returned to the cut darts.
- **`walk_source_above` + `firstReturn_down` (the alternation lemma)** — after an
  upward crossing the face walk stays strictly above the cut and re-crosses
  downward.  This is what makes the necklace well defined.
- `neckPerm` (cross + reverse), `neckPerm_up` — preserves upward crossings.
- `upOfArc`/`arcOfUpDart` — transition arcs ≃ upward cut darts (under ProperLayered).
- `arcNext`, `arcNext_injective`, `arcPerm` — the necklace permutation on arcs.
- `orbitPeriod/_pos/_return`, `orbitList`, `orbitList_pow_injective`,
  `orbitList_nodup`, `self_mem_orbitList`, `orbitList_closed` — generic orbit words.
- `necklaceWord` (real definition: orbit of a canonical arc; `[]` on empty
  transitions), `necklaceWord_nodup` — proved.
- `listingOfPrefix`, `necklaceLayerOrder` — real definitions of the layer
  listings (targets of the necklace below; `cyclicListingOfFintype` fallback).
- `hansenArcOrder_impl` (NecklaceAssembly) — kernel-checked reduction of the whole
  Hansen principle to exactly three obligations, all stated WITH the full
  hypotheses (ProperLayered, `rotationGenus r = 0`, unique source and sink):
  1. `necklaceWord_complete` — the necklace of every transition is a single
     cycle (use `MinCorner`/`DartSwitch` Euler counting: at genus zero every
     face is unimodal, and necklaces merge across layers via the block rewrite;
     base layer = the rotation cycle at the source).
  2. `necklace_groupedAlong_source` — out-fibers are contiguous (faces born at
     a min corner of the tail separate consecutive out-darts).
  3. `necklace_groupedAlong_target` — in-fibers are contiguous, coherently with
     the listing induced one level below.

`MinCorner.lean` (gemini draft, now verified green, 0 sorries) and the
`DartSwitch` additions build; `FullLayerIndexing` builds and is registered.
`NonCrossing.lean` does NOT compile (typeclass failures at :61-65) and is NOT
in the roll-up — repair or replace before use.  `ExternalFacts.lean` and
`BetaBridge.lean` were reverted to the frozen main versions; gemini root
scratch files moved to `iter_007_proof/agent_scratch/01_gemini/root-scratch/`.

## Face unimodality layer (E1, user session 2026-08-16, second pass) — proved, reuse

`AllenderOQ3/Internal/FaceUnimodal.lean` (`sorry`-free, registered in the
roll-up).  The equality case of the Euler–Morse sandwich and its consequences:

- `card_minCorners_eq_faceCount` — at genus zero with unique source/sink (and
  ≥1 edge), #minCorners = `permCycleCount (facePermutation r)`.  Uses the
  proved `switchCount_eq_one_of_internal` to pin `K = |internal|` and the
  `{s,t}`-complement count.
- `minCorner_unique_in_faceOrbit`, `existsUnique_minCorner_in_faceOrbit` —
  **every face orbit has exactly one min corner** (surjectivity of the
  rep→corner choice map forced by the card equality; `minRep_unique`).
- Max side, all proved: `card_up_next_split`, `card_down_next_split`,
  `card_up_prev_split`, `card_minCorner_shift`, `card_downUp_shift` (the
  rotation-bijection shift), `card_maxCorners_eq_minCorners`,
  `card_maxCorners_eq_faceCount`, `exists_maxCorner_in_faceOrbit`,
  `maxCorner_unique_in_faceOrbit`, `existsUnique_maxCorner_in_faceOrbit` —
  **every face orbit has exactly one max corner**.
- **Necklace-step identities** (hypothesis-light, no genus needed):
  `revDart_cut_of_up/down`, `rotDart_cut_of_corner/maxCorner`,
  `firstReturn_of_minCorner`, `neckPerm_of_minCorner`,
  `firstReturn_of_maxCorner`, `neckPerm_of_maxCorner` — at a min (resp. max)
  corner `(d, r.rotation d)` the face walk from `dartReverse c d` returns to
  the cut of layer `c.layer d.source` (resp. `c.layer d.target`) in ONE step,
  landing on `r.rotation d`; hence `neckPerm` maps the reversed corner darts
  to each other.  These are the local adjacency facts for the three grouping
  obligations: consecutive out-darts (min corner at the tail) and consecutive
  in-darts (max corner at the head) of a vertex rotation are
  necklace-adjacent.

Suggested route for the remaining three `CutNecklace` obligations: walk the
`arcPerm` orbit; at each step the crossing enters a vertex fiber and, by the
unique max corner of the face and `neckPerm_of_maxCorner`, either continues
inside the same in-fiber (contiguity) or leaves it for good; single-orbit
(`necklaceWord_complete`, via `necklaceWord_complete_of_single_orbit`) follows
by the upward induction over layers with the block rewrite, whose base is the
rotation cycle at the source (`cyclicAtVertex` + `source_alone_in_layer`).

Also proved (`CutNecklace`): `walk_source_below`, `firstReturn_up`,
`neckPerm_down` — the descending mirror of the alternation lemma, so
`neckPerm` preserves both crossing directions.

**Key design note for the grouping obligations (verified informally, not yet
formalized).**  The corner-step identities live on the *descending* side
(`neckPerm ⟨rev d⟩ = ⟨rev (rot d)⟩`), while `arcPerm` walks the *ascending*
side.  The bridge is: at genus zero `firstReturn r ell` is an **involution**
on the cut darts, because every straddling face crosses the cut exactly
twice.  Proof route, fully reduced to proved material: (1) min corners of a
face orbit = its down→up positions and max corners = its up→down positions
(this is how `exists_minCorner_in_faceOrbit` finds them); by
`existsUnique_min/maxCorner_in_faceOrbit` each occurs exactly once, so the
ascending darts form ONE contiguous block of the face cycle; (2) along an
ascending run sources increase by exactly 1 per step
(`facePermutation_source`), so each intermediate level is crossed exactly
once per run — two crossings total per straddling face; (3) hence the first
return from one crossing is the other, and `firstReturn ∘ firstReturn = id`.
Consequences: `neckPerm⁻¹ = cutDartReverse ∘ neckPerm ∘ cutDartReverse`, and
the min-corner identity transports to the arc level as
`arcPerm (arcOfUpDart (rot d)) = arcOfUpDart d` — consecutive out-darts of a
vertex are `arcPerm`-consecutive (in reversed rotation order), which is the
source-grouping local step; the max-corner identity gives the target-grouping
step directly.  Single-orbit then follows by the upward induction whose base
is the rotation cycle at `s`.

## First-return involutivity (E1, user session 2026-08-16, third pass) — proved, reuse

`AllenderOQ3/Internal/FirstReturnChain.lean` (`sorry`-free, registered):

- `dartIsUp_of_layer`, `dartIsUp_eq_false_of_layer`, `up_of_cutDart`,
  `down_of_cutDart`, `cutDart_source_cases`, `perm_pow_apply_pow` — glue.
- `cut_mem_firstReturn_chain` — the first-return chain from a cut dart
  reaches every cut dart on its face walk (strong induction on the walk
  length; the chain enumerates the crossings in walk order).
- `exists_switch_on_descent`, `exists_minCorner_on_descent` — between a
  downward crossing and its first return the walk passes a min corner,
  located explicitly (`dartReverse c x = walk j`, `r.rotation x = walk (j+1)`,
  `j + 1 <= return time`).
- **`firstReturn_involutive`** — at genus zero with unique source and sink,
  `firstReturn r ell` is an involution of the cut darts: every straddling
  face crosses the cut exactly twice.  Proof: if `fR (fR u) != u` for an
  upward `u`, the walks from `y := fR u` and from `y2 := fR (fR (fR u))`
  occupy disjoint position ranges inside one orbit period (return times
  bounded through `Nat.find_min'` against the period, strictness from
  up/down type clashes), each contains a min corner, and the two corners are
  distinct by position injectivity (`orbitList_pow_injective`) yet equal by
  `minCorner_unique_in_faceOrbit` — contradiction.  The descending case
  follows by injectivity of `fR`.
- `neckPerm_rev_neckPerm` — `neckPerm (rev (neckPerm x)) = rev x`: the
  necklace permutation is conjugate to its inverse by dart reversal.  This is
  the up/down bridge: combined with `neckPerm_of_minCorner` /
  `neckPerm_of_maxCorner` (FaceUnimodal) it yields the arc-level adjacency
  `arcPerm (arc (rot d)) = arc d` at a min corner, i.e. contiguity of the
  source fibers, and dually for target fibers.  Next leaves: state and prove
  those two arc-level corollaries, then the grouping obligations by
  induction along the necklace orbit, and single-orbit by the upward
  induction with base = the rotation cycle at the source.

## Arc-level corner steps and the source-level orbit (user session 2026-08-16, fourth pass) — proved, reuse

Appended to `AllenderOQ3/Internal/FirstReturnChain.lean` (`sorry`-free):

- `upDart_cut_self`, `cutDartReverse_involutive`, `upOfArc_arcOfUpDart`,
  `arcOfUpDart_upOfArc` — glue and round trips between transition arcs and
  upward cut darts.
- `neckPerm_up_of_minCorner` — the min-corner identity transported to the
  ascending side through `neckPerm_rev_neckPerm`:
  `neckPerm (rot d) = d` for a min corner `(d, rot d)`.
- **`arcPerm_of_minCorner`** — `arcPerm (arc (rot d)) = arc d`: the out-fiber
  of a vertex is traversed by the arc permutation in reversed rotation order
  (needs genus zero).  `arcPerm_of_minCorner'` is the level-generalized form
  (any `ell` with `c.layer d.source = ell`, arbitrary membership proofs).
- **`arcPerm_of_maxCorner`** — `arcPerm (arc (rev d)) = arc (rev (rot d))`
  for a max corner: the in-fiber is traversed in rotation order.  Needs only
  `ProperLayered` (the identity already lives on the ascending side).
- `rotation_pow_source`, `dart_at_source_up` — rotation powers preserve the
  source; every dart at the graph source ascends.
- `arcPerm_pow_rot_chain` — chaining min-corner steps:
  `arcPerm^k (arc (rot^k d)) = arc d` for a dart `d` at the source.
- **`single_orbit_of_common_source`** — at a level where every transition arc
  leaves one vertex `s` (the graph source), any two arcs are connected by a
  power of `arcPerm`.  Via `necklaceWord_complete_of_single_orbit` this is
  the BASE CASE of the completeness obligation: the necklace of the
  bottom transition is a single cycle.

Remaining for the three `CutNecklace` obligations, in dependency order:
1. per-vertex fiber-block structure: from `switchCount_eq_one_of_internal`
   the in-darts (out-darts) of a vertex form one contiguous rotation block;
   with `arcPerm_of_maxCorner` (`arcPerm_of_minCorner`) each fiber is a
   contiguous `arcPerm` interval;
2. `necklace_groupedAlong_target`/`_source`: walk `orbitList` once, using 1
   to split the word into fiber blocks in first-visit order — this is list
   bookkeeping over `GroupedAlong`, no more geometry;
3. `necklaceWord_complete` for all levels: upward induction — the block
   rewrite carries single-orbitness from level `ell` to `ell + 1` (each
   in-fiber of level `ell + 1` is entered, and `arcPerm_of_maxCorner` walks
   it; base = `single_orbit_of_common_source` at the source layer via
   `source_alone_in_layer`).

## Interleaved transitions break the single-word assembly (user session 2026-08-16, fifth pass)

New `sorry`-free files and lemmas:

- `AllenderOQ3/Internal/DoubleGroupingObstruction.lean`
  - `groupedAlong_contiguous` — a word grouped along a key has contiguous
    key-fibres: if two letters share a key, so does every letter between them.
  - `not_doubleGrouped_crossing_four` — with the two interleaved key partitions
    `{a,b},{c,d}` and `{b,c},{a,d}` of a four-letter word, *no* pair of
    listings groups one and the same word along both keys.

  Consequence for the Hansen assembly.  A planar `K_{2,2}` transition (two
  sources, two targets, all four arcs, arc cycle `u₁v₂, u₁v₁, u₂v₁, u₂v₂`) has
  exactly these interleaved fibres, so the two grouping obligations of
  `CutNecklace` could not both hold in their original on-the-nose form: they
  asked for one word grouped along the source listing *and* along the target
  listing.  The frozen certificate field `ArcOrderCertificate.commonArcWord`
  only requires the source-major and target-major words to agree up to a
  `CyclicRotation`, and that slack is exactly what the interleaved case needs
  (rotating `a b c d` to `b c d a` groups the targets).

- `AllenderOQ3.Internal.incidenceCylinder_of_rotatedWords`
  (`IncidenceToolkit.lean`) — the rotation-tolerant packaging: one word per
  transition, grouped along each key only after a cyclic rotation of the word
  and of the corresponding layer listing.  `NecklaceAssembly.hansenArcOrder_impl`
  now goes through it, and the two grouping obligations in `CutNecklace` are
  stated in that rotated form (the original statements are kept, commented, at
  the same place with the explanation).

- `AllenderOQ3/Internal/ListContiguity.lean` — the converse direction, i.e. the
  bookkeeping half of step 2 above:
  - `KeyContiguous` — the contiguity predicate;
  - `groupedAlong_dedup_of_contiguous` — a word with contiguous fibres is
    grouped along `(w.map key).dedup`;
  - `groupedAlong_append_unused`, `groupedAlong_insert_unused` — keys carried by
    no letter may be appended to or inserted into the listing.
- `groupedAlong_listingOfPrefix_of_contiguous` (`CutNecklace.lean`) — combines
  them: contiguous fibres give the grouping along `listingOfPrefix`.
- `necklace_groupedAlong_target_of_contiguous` (`CutNecklace.lean`) — the target
  obligation now follows from the single geometric fact
  `KeyContiguous arcTarget (necklaceWord hpl r ell)`.

Remaining for the target obligation: the fibres are contiguous only *cyclically*
(a fibre may wrap around the start of the orbit list), so the general case needs
the necklace word rotated to a block boundary, together with the corresponding
rotation of `necklaceLayerOrder` — plus the geometric input of step 1 above.

- `AllenderOQ3/Internal/NonCrossing.lean` — `non_solvable_guard` proved: the
  unrestricted transition monoid is non-commutative (the two constant
  configuration maps absorb each other on opposite sides), which is the guard
  against running the Barrington--Thérien argument on `TransMonoid w` instead of
  the incidence-constrained submonoid.  The two E2-b statements in that file did
  not typecheck (`NonCrossing w` is a submonoid: no `Subgroup` and no integer
  powers); they are kept verbatim in a comment and restated over the unit group
  `(NonCrossing w)ˣ`.

## Current state of the three genus-zero necklace obligations

The obligations have been moved downstream of the geometric input they need and
now live in `AllenderOQ3/Internal/NecklaceGrouping.lean` (`CutNecklace.lean`
keeps their statements verbatim in comments as an audit trail).  Supporting
files added along the way: `DedupRotation.lean` (dedup/rotation list algebra),
`OrbitContiguity.lean` (`cyclicContiguous_orbitList`), `VertexCorner.lean`
(per-vertex corner count, `downUp_corner_unique`).

Proved, `sorry`-free:

- `necklace_arcTarget_cyclicContiguous`, `necklace_arcSource_cyclicContiguous` —
  the incoming (resp. outgoing) fibres of a necklace are contiguous blocks of
  the cyclic word.  Both come from `cyclicContiguous_orbitList` plus the
  uniqueness of the down-to-up corner at a vertex, which is the genus-zero
  input.
- `necklace_groupedAlong_target` — the whole target obligation.
- `necklace_groupedAlong_source` at `ell = 0`, where the layer listing is by
  construction the source-side listing of the same necklace word
  (`necklaceLayerOrder_zero`).
- `necklaceWord_complete` on the layer carrying the graph source, from
  `necklaceWord_complete_base`.

Open, each isolated as a single named leaf:

- `necklace_groupedAlong_source_succ` — cross-layer coherence: above the bottom
  layer the listing of layer `m + 1` is fixed by the *incoming* fibres of the
  necklace of transition `m`, while the obligation is about the *outgoing*
  fibres of the necklace of transition `m + 1`.  Note that the two listings are
  not cyclic rotations of one another in general (a vertex with no outgoing arc,
  e.g. the graph sink, is padded to the end of the source-side listing), so the
  leaf has to be stated in the grouping form, with the empty fibres free to sit
  anywhere.
- `necklaceWord_complete_off_source` — single-necklace completeness on the other
  layers.  A concrete route is recorded in the source: with `m` cut edges and
  `k` necklaces, the genus-zero Euler identity (`defect_eq_of_rotationGenus_zero`
  plus the block additivity of `BlockGenus`) gives `F = F_B + F_T + m - 2`,
  while re-gluing the cut edges gives `F = F_B + F_T + m - 2k`; hence `k = 1`.
  Only the first display uses genus zero, and correctly so: on a torus a cut can
  consist of two parallel non-separating cycles with both sides connected.

## E2 route-2 (certificate-aligned) toolkit, `sorry`-free

New, self-contained modules developed for the quantitative cylindrical `ACC`
obligation.  They are deliberately not imported by `Internal.lean` (they are not
yet consumed by the final wrapper), but each is `sorry`-free and builds.

- `AllenderOQ3/Internal/ACCFewVars.lean` —
  `exists_acc_of_factors`: a predicate factoring through `k` input coordinates is
  decided by an `ACC[m]` circuit of depth `≤ 2` and size `≤ 2k + 2^k + 1`
  (truth table + variable relabelling);
  `exists_acc_of_slotwise`: the form used for layer transitions, where each slot
  of a tuple is either a (possibly negated) input literal or a constant.  The
  `n = 0` corner case is handled separately.
- `AllenderOQ3/Internal/NonCrossingSemantics.lean` — route-2 evaluation
  semantics, which is what makes `layerTransMap` a faithful reading of the
  circuit (and avoids the route-1/route-2 literal-slot mismatch):
  `fullState` (the configuration carried by a valuation at a layer),
  `initConfig` (the layer-`0` configuration, written in terms of the input),
  `fullState_apply`, `layerTransMap_fullState` (one layer step),
  `fullState_zero`, `fullState_eq_runTrans_word` (iterating the letters) and
  `adrAccepts_iff_runTrans_word` (acceptance = the output slot of the word
  product).  All under `WellFormedADR` plus `TotalWidthAtMost c w`.
- `AllenderOQ3/Internal/ACCLayerTrans.lean` —
  `layerTransMap_slot_dichotomy`, `initConfig_slot_dichotomy`, and the resulting
  small circuits `exists_acc_layerTransMap`, `exists_acc_initConfig` (depth `≤ 2`,
  size `≤ 2w + 2^w + 1`) and `exists_acc_layerTrans_eq` (depth `≤ 3`, size
  `≤ 2^w (2w + 2^w + 1) + 1`) recognising a fixed letter of the transition
  monoid.
- `AllenderOQ3/Internal/ACCAssembleWord.lean` —
  `exists_acc_adrAccepts_of_word`: the mechanical assembly step.  Given a
  depth-`D`, size-`S` `ACC[m]` recogniser for "the product of the layer letters
  equals `g`", for every `g`, one obtains a depth-`(max D 2 + 2)`,
  size-`(K (S + 2w + 2^w + 3) + 1)` recogniser for `ADRAccepts c`, where
  `K = |Config w × TransMonoid w|` depends only on `w`.  This isolates the
  remaining E2 obligation as the word problem of the transition monoid.
- `AllenderOQ3/Internal/TransitionMonoid.lean` — `transMonoid_ext`,
  `transMonoid_ext_iff`, and the corrected Green's-relation characterisations
  `RPreorder_iff_ker_subset` and `REquiv_iff_ker_eq`: in the *opposite*
  endomorphism monoid the `R`-order is kernel refinement, **not** range
  inclusion (the range-based reading is false; it is the `L`-order).

### E2 reduced to a word problem

- `AllenderOQ3/Internal/WordProblemReduction.lean` —
  `WordProblemACC w` states the remaining mathematical content of the external
  fact: for incidence-certified circuits of total width `w`, the predicate "the
  product of the layer letters equals `g`" has, for every fixed `g` of the
  width-`w` transition monoid, an `ACC[modulus]` recogniser of constant depth
  and size `(gateCount + 1) ^ exponent`, with `modulus`, `depth`, `exponent`
  depending only on `w`.
  `quantitativeCylindricalACC_of_wordProblem` proves, `sorry`-free, that
  `∀ w, WordProblemACC w` implies the frozen
  `QuantitativeCylindricalACCPrinciple`; the width-dependent constants of the
  assembly are absorbed into the size exponent by `assemble_size_bound` and
  `const_mul_pow_le_pow` (the base `gateCount + 1` is at least `2` because a
  circuit always has an output gate).
  `wordProblemACC_zero` discharges the degenerate width `0` outright.
  Note the body of `External.quantitativeCylindricalACC` is deliberately left as
  `by sorry`: the trust audit requires each open external fact to be exactly a
  `by sorry` body, so the reduction is kept in `Internal`.
- `AllenderOQ3/Internal/MonoidWord.lean` — `RPreorder_of_le_nat` and
  `REquiv_of_no_descent`: along an `R`-non-increasing chain, `R`-classes are
  constant on descent-free intervals.  Specialised to prefix products in
  `TransitionMonoid.lean` as `prefixEnd_RPreorder_of_le` and
  `REquiv_prefixEnd_of_no_descent`; with `card_prefix_RDescents_le` this is the
  block decomposition of a word of layer letters into boundedly many
  `R`-constant blocks.

### E2: bounding the word length and the number of `R`-descents

- `AllenderOQ3/Internal/WordCompress.lean` — sparse-layer normalisation.  The
  layer index of the output gate is not bounded by the size of the circuit, so
  the raw word of layer letters can be arbitrarily long.  `zeroTrans w` (the
  constant-`false` transition) is shown to be a *right zero* of the transition
  monoid (`mul_zeroTrans`), and an empty layer contributes exactly that letter
  (`layerTrans_eq_zeroTrans`).  `exists_compression_index` produces an
  input-independent split point `k` with at most `c.gateCount` layers above it
  and a degenerate layer at `k`; `prefixEnd_layerWord_of_compression` shows the
  cut-off prefix is `1` or `zeroTrans w` for *every* input; and
  `outputWord_compress` assembles the factorisation.  The gate-counting step is
  `card_nonempty_layers_le`.
- `AllenderOQ3/Internal/ShortWordProblem.lean` — `ShortWordProblemACC w`, the
  obligation restricted to windows of layer indices of length at most
  `c.gateCount` with a constant left factor.  `wordProblemACC_of_short` proves
  `ShortWordProblemACC w → WordProblemACC w`, and
  `quantitativeCylindricalACC_of_shortWordProblem` therefore derives the frozen
  principle from the short-word obligation alone.
- `AllenderOQ3/Internal/TransRank.lean` — the *rank* of a transition (the
  cardinality of its range).  Rank is non-increasing along Green's right
  preorder (`rankTrans_le_of_RPreorder`) and strictly decreases at a strict
  `R`-descent (`rankTrans_lt_of_descent`, via the kernel characterisation of the
  `R`-order).  Consequently a word has at most `|Config W| = 2 ^ W` `R`-descents
  (`card_prefix_RDescents_le_card_config`,
  `card_prefix_RDescents_le_two_pow`) — exponentially sharper than the generic
  `|TransMonoid W|` bound of `card_prefix_RDescents_le`, and the form needed for
  a polynomial size bound.
- `AllenderOQ3/Internal/TransBlock.lean` — the structure *inside* an
  `R`-constant block.  `injOn_rangeTrans_of_REquiv` and its converse
  `REquiv_of_injOn_rangeTrans` identify "the letter `u` keeps the `R`-class of
  the prefix `a`" with "`runTrans u` is injective on the range of `runTrans a`",
  and `bijOn_rangeTrans_of_REquiv` upgrades this to a bijection of ranges.  So
  along a block the transition is carried by bijections between sets of one
  fixed cardinality (`rankTrans_eq_of_REquiv`) — the permutation picture on
  which the Barrington–Thérien analysis of the non-crossing monoid operates.

## 2026-08-16 (session 5): E2 leaf analysis — HMV source + soundness gap in the Leaf-3 sketch

The HMV paper (ECCC TR02-066) is now stored at docs/hmv-circuits-on-cylinders-TR02-066.pdf
with a full extraction of its algebra in docs/HMV_ALGEBRA_NOTES.md. Summary: HMV prove all
subgroups of N_k cyclic (Lemmas 9-12 + Prop 13; interval/antichain/cyclic-shift structure)
and then CITE Barrington-Therien for "solvable word problem in ACC0". So letterWordACC_impl
= HMV cyclicity (E2-b) + a genuine quantitative BT upper bound (E2-c); the latter is the
real remaining content and has no proof in HMV.

SOUNDNESS GAP found in the iter-11/14 assembly sketch (guess R-descent boundaries + per-block
cyclic MOD counts): (1) rank-1 collapse — constant-map letters put the entire word in a single
rank-1 R-class with no descents; the within-block problem is then the full point-trajectory
problem and the rank-1 groupoid is trivial; (2) moving basepoint — per-letter rotation amounts
depend on the input-dependent current range set, itself a prefix problem. Sound route: BT-style
cascade over the ideal structure of NonCrossing w (aperiodic shape layer + cyclic MOD layers);
new usable fact: monotone injective-on-a-set maps only ADD comparabilities, so the range-poset
shape is a monotone (aperiodic) coordinate along descent-free stretches. Before any Lean
bookkeeping, validate the chosen normal form computationally at w<=4 (see notes, section 3).

## 2026-08-17 (iteration 17): Cascade engine infrastructure + sorry reduction

### E2-c cascade building blocks

- `AllenderOQ3/Internal/CascadeAperiodic.lean` — the aperiodic (bounded-change)
  layer of a Barrington–Thérien cascade.
  - `evalGuess` — evaluate a guessed change-time/value sequence at position `i`:
    index into `vals` by the count of change-times strictly before `i`.
  - `z_eq_of_count_eq` — helper: if two positions have the same count of
    change-times before them, then `z` has the same value at both (any change
    position between them would produce a times-entry that separates the counts).
  - `exists_guess_of_changes_le` — **kernel-proved (iter 17)**: any `Fin (len+1) → Z`
    sequence with at most `K` change positions can be faithfully represented as a
    `(times : Fin K → Fin len, vals : Fin (K+1) → Z)` guess.  Construction:
    enumerate change positions via `S.toList`, pad to length `K` with a default
    element from `h_nonempty`; define `vals c` by classical choice of a
    representative position with count `c`; soundness follows from
    `z_eq_of_count_eq`.
  - `cascade_aperiodic_layer` — given letter/driver recognizers and a step function,
    construct an ACC circuit that accepts iff the iterated step-function trajectory
    hits a target value.  Uses `exists_guess_of_changes_le` to guess the
    bounded-change trajectory and `accOrAnd` to assemble.

- `AllenderOQ3/Internal/CascadeCyclic.lean` — the cyclic (MOD) layer of a cascade.
  - `cascade_cyclic_layer` — given letter/driver recognizers, a generator `g0` of
    order dividing `N | m` in a monoid `G`, and a kappa function mapping
    (letter, driver) pairs to exponents in `Fin N`, construct an ACC circuit that
    accepts iff the product `∏ᵢ g0^{kappa(letter_i(x), driver_i(x))}` equals a
    target `h`.  Delegates to `exists_acc_powWord` (the cyclic word problem
    circuit from `ACCCyclicWord`).

## Iteration 20 — top-of-tower cyclicity (E2-b, partial)

- **`RealizedOrderIso.lean` (new, 0 sorries)**: `le_of_monotone_bijOn` /
  `monotone_bijOn_le_iff` — a monotone self-bijection of a finite subset of a
  poset also *reflects* the order (the inverse is a positive iterate);
  `layerRest_subset`, `minLayer_subset`, `minLayer_subsingleton_of_chain`;
  `realizedPerm_le_iff` — realized permutations are order automorphisms;
  `realizedPerm_mem_minLayer_iff` — layer membership is an equivalence;
  `realizedSubgroup_eq_bot_of_chain` and `isCyclic_realizedSubgroup_of_chain` —
  **H1 for totally ordered `S`**; `runTrans_pow`; `isUnit_of_bijOn_univ` — an
  element acting bijectively on all configurations is a unit; `unitPerm`,
  `unitPermHom`, `realizedSubgroup_univ_eq_range` and
  **`isCyclic_realizedSubgroup_univ` — H1 for `S = univ`**, from
  `nonCrossing_units_cyclic`.
- **`RealizedFamUniv.lean` (new, 0 sorries)**: `imageOf_singleton`,
  `isUnit_of_realizedFamPerm_univ` (singletons force injectivity), `unitFamPerm`,
  `unitFamPermHom`, `realizedFamSubgroup_univ_eq_range` and
  **`Holonomy.isCyclic_realizedFamSubgroup_univ` — H2 for the family of all
  configuration sets**.
- **`RealizedTransport.lean` (new, 0 sorries)**: `bijEquiv`,
  `realizedPerm_sandwich`, `realizedPerm_beta`, `sandwich_eq_permCongr_mul`,
  `realizedPerm_permCongr`, `transportHom`, `transportHom_surjective`, and
  **`isCyclic_realizedSubgroup_of_reachEquiv`** — H1 transports along mutual
  reachability, so it only needs proving for one representative per class.
- Still open for E2-b: H1/H2 for the *proper* levels of the tower (the HMV
  interval/rotation geometry for antichain layers).

### Sorry status after iteration 17

- `CascadeAperiodic.lean:exists_guess_of_changes_le` — **CLOSED** (was `sorry`,
  now kernel-proved).
- `ShortWordProblem.lean:letterWordACC_impl` — **remains open** (the Barrington–
  Thérien upper bound for `NonCrossing w`).  This is the single remaining
  non-comment sorry in the entire codebase.
- `NonCrossing.lean:17,21` — inside a `/-  -/` comment block; not compiled.

### Cleanup

- Removed untracked scratch/test files (`ProverTask*.lean`, `scratch*.lean`) left
  by a failed Gemini stage.  These contained `axiom cheat : False` and multiple
  sorries that would pollute a trust audit.

## 2026-08-17 (iteration 17, proof stage): the aperiodic cascade coordinate

- `AllenderOQ3/Internal/CascadeCoordinate.lean` (new, `sorry`-free) — a globally
  monotone rank/shape measure and the resulting bounded-change property.
  - `card_changes_range_add_le`, `card_changes_le_of_measure` — an abstract
    counting principle: a `Nat`-valued measure that never decreases along a
    sequence and strictly increases at every change bounds the number of changes
    by its bound.  This is the shape of the `h_changes` hypothesis of
    `cascade_aperiodic_layer`.
  - `shapeCoord` — the rank/shape pair of a transition, packaged in the finite
    type `Fin (2 ^ W + 1) × Fin (2 ^ W * 2 ^ W + 1)`, with `shapeCoord_eq_iff`.
  - `shapeMeasure`, `shapeMeasure_le` — the lexicographic measure
    `(2 ^ W - rank) * (2 ^ W * 2 ^ W + 1) + shape` and its bound.
  - `rankTrans_prefixEnd_succ_le`, `REquiv_prefixEnd_succ_of_rank_eq` — the rank
    of a prefix never increases, and a stable rank forces a stable `R`-class
    (via `rankTrans_lt_of_descent`).
  - `shapeMeasure_prefixEnd_le`, `shapeMeasure_prefixEnd_lt` — the measure is
    monotone along the *whole* word (not only inside an `R`-constant block), and
    strictly increases whenever the rank/shape pair changes.
  - `card_shapeCoord_changes_le`, `card_shapeCoord_changes_le_nonCrossing` — the
    rank/shape coordinate of the prefixes of a word of monotone letters (in
    particular of `NonCrossing w` letters) changes at most
    `2 ^ w * (2 ^ w * 2 ^ w + 1) + 2 ^ w * 2 ^ w` times, however long the word.
  - `orderIso_blockEnd_of_shapeCoord_const` — on a stretch where the coordinate
    is constant the intervening product is a bijection of ranges that preserves
    *and* reflects the order, so any word of monotone letters splits into a
    bounded number of order-isomorphism stretches.

  Caveat recorded in the file header: feeding the coordinate to
  `cascade_aperiodic_layer` additionally needs a local update rule for it; only
  the change bound and the resulting block structure are established here.

- `AllenderOQ3/Internal.lean` now imports `CascadeAperiodic` and
  `CascadeCoordinate`, so both are built by the default target.

### Sorry status

- `ShortWordProblem.lean:letterWordACC_impl` — still the single remaining
  non-comment `sorry` in the codebase.

## Iteration 18 (proof stage): the generator-geometry hole

- `AllenderOQ3/Internal/ConfigInterval.lean` no longer compiled against the
  current Mathlib (the `Finset.card_bij` bookkeeping of
  `count_false_true_eq_count_true_false` had rotted).  The proof is repaired,
  and the file gained two reusable lemmas:
  - `finShift_surj_lt` — any position is reached from any other by a shift `< w`;
  - `exists_isCyclicInterval` — **every configuration with at least one `true`
    position contains a maximal cyclic block of `true`s** (walk back to the first
    rising edge, then forward to the first falling edge).

- `AllenderOQ3/Internal/GeneratorGeometry.lean:predecessor_set_is_cyclic_interval`
  is now `sorry`-free.  The statement previously recorded there is **false**: its
  conclusion asserts `0 < len` together with an edge into the target vertex from
  position `start`, which forces every layer-`(ell+1)` vertex to have a
  predecessor, whereas an edge-free circuit is incidence-cylindrical
  (`incidenceCylinder_of_edgeFree`).  The false form is kept in a comment and
  refuted by `predecessor_set_is_cyclic_interval_false` (an explicit two-gate
  edge-free counterexample).  The corrected lemma adds the missing
  non-degeneracy hypothesis "`v` has a predecessor in layer `ell`" (and drops the
  unused `h2`); it then follows from `exists_isCyclicInterval`.

- `AllenderOQ3/Internal.lean` now also imports `ConfigInterval` and
  `GeneratorGeometry`, so both are built by the default target and can no longer
  rot unnoticed.

### Sorry status after iteration 18

- `ShortWordProblem.lean:letterWordACC_impl` — the single remaining non-comment
  `sorry` in the `AllenderOQ3` library.

## Iteration 19 (proof stage): cleanup and cascade assembly analysis

- `AllenderOQ3/Internal/ShortWordProblem.lean`:
  - **Removed dead stubs**: `HMVCoordinate` (unused type alias),
    `letterWordACC_shape_layer` (`: True := by sorry`), and
    `letterWordACC_cyclic_layer` (`: True := by sorry`) — all three were
    non-functional scaffolding added by Gemini that inflated the sorry count
    from 1 to 3 without contributing any proof progress.
  - **Refreshed docstring** of `letterWordACC_impl` (T0.1): now explicitly
    documents the soundness refutation of the R-descent/MOD-counting route
    (rank-1 collapse and moving-basepoint dependence), the correct
    Barrington–Thérien cascade route, and the full inventory of proved
    infrastructure (`CascadeAperiodic`, `CascadeCyclic`, `CascadeCoordinate`,
    `LetterWordUnits`, `ConfigInterval`, `GeneratorGeometry`).

### Sorry status after iteration 19

- `ShortWordProblem.lean:letterWordACC_impl` — the single remaining non-comment
  `sorry` in the `AllenderOQ3` library (line 410).

## Iteration 20 (proof stage): block boundaries for the cascade

- `AllenderOQ3/Internal/BlockBoundaries.lean` (new, `sorry`-free) — the bridge
  from the bounded-change bound of `CascadeCoordinate` to the data a
  guess-and-verify cascade layer has to guess:
  - `changeCount` and its basic arithmetic (`changeCount_succ`,
    `changeCount_mono`, `changeCount_lt_of_ne`);
  - `exists_block_boundaries` — a sequence with at most `K` changes below `len`
    admits boundaries `0 = bs 0 ≤ bs 1 ≤ … ≤ bs (K + 1) = len`, all `≤ len`, on
    each of whose half-open blocks `[bs j, bs (j + 1))` the sequence is
    constant (pure combinatorics, any coordinate type);
  - `card_shapeCoord_changes_range_le` — the `CascadeCoordinate` change bound in
    the `Finset.range` form the extraction consumes;
  - `exists_shapeCoord_block_boundaries` and
    `exists_shapeCoord_block_boundaries_nonCrossing` — the resulting block
    decomposition for words of monotone, resp. `NonCrossing w`, letters;
  - `REquiv_prefixEnd_of_shapeCoord_const` — along a block all prefix
    transitions share one kernel (`R`-class);
  - `orderIso_blockEnd_of_mem_block` — on a block the letters read so far act as
    an order isomorphism of the reachable configurations;
  - `REquiv_mul_iff_injOn_range` — reading a letter keeps the prefix in its
    `R`-class **iff** that letter is injective on the currently reachable
    configurations, and `injOn_range_of_shapeCoord_const`, its instance along a
    block.
- `AllenderOQ3/Internal.lean` imports the new module, so it is built by the
  default target.

### Analysis recorded for the next iteration

The "moving basepoint" half of the iteration-14 refutation is an artefact of
measuring rotation amounts against the *configuration* range set.  Along a
shape-constant block the prefix transitions all share one kernel
(`REquiv_prefixEnd_of_shapeCoord_const`) and every letter is injective on the
current range (`injOn_range_of_shapeCoord_const`), so the block state can be
taken to be the prefix transition itself — an element of the fixed finite monoid
`TransMonoid w` — and the step map is post-multiplication by the letter, with no
input-dependent basepoint.  What is still missing for the cascade is the
*planarity* input: that the group generated by the block steps on such a block
is cyclic (equivalently, that the order automorphisms of the range poset of a
`NonCrossing w` element that are realised inside the monoid are rotations).
Monotonicity alone cannot give this — coordinate permutations are monotone and
realise `S_5` on an antichain of five unit vectors — so the incidence-cylinder
geometry has to be used, which is what `non_solvable_guard` warns about.

### Sorry status after iteration 20

- `ShortWordProblem.lean:letterWordACC_impl` — still the single remaining
  non-comment `sorry` in the `AllenderOQ3` library.

## 2026-08-17 (session 6, user-delegate): heart confirmed computationally; first heart bricks in Lean

- **Decisive experiments PASSED** (scripts + results: docs/experiments/,
  docs/HMV_ALGEBRA_NOTES.md section 4). At w=2,3 the full monoid NonCrossing w was
  enumerated (34 / 3844 elements): (1) for EVERY subset S of Config w the realized
  setwise-stabilizer permutation group {m|_S : m(S)=S} is cyclic (orders <= w);
  (2) the holonomy brick-family permutation groups over all reachable S are cyclic
  too. The two heart lemmas H1/H2 are therefore safe to invest in; the assembly
  must be a holonomy/wreath tower over the subset lattice (see updated
  milestone_guidance), NOT prefix R-blocks.
- **New file `LocalizedCyclicity.lean` (0 sorries, built green 8158 jobs):**
  - `exists_iterate_eq_id_on` — a self-bijection of a finite set has a positive
    iterate equal to the identity on it (via `pow_card_eq_one` on the induced
    permutation of the subtype);
  - `bijOn_sdiff` — self-bijections restrict to complements of invariant subsets;
  - `MinIn`/`minIn`/`mem_minIn`/`minIn_subset`/`minIn_nonempty`;
  - `minIn_image`, `bijOn_minIn` — **localized HMV Lemma 12**: a monotone map
    bijective on S permutes min(S) (the missing monotone inverse is replaced by
    the (k-1)-st iterate);
  - `layerRest`/`minLayer`/`bijOn_layerRest` — the antichain layering skeleton of
    HMV Proposition 13: a monotone self-bijection self-bijects every layer;
  - `bijOn_minIn_of_mem_nonCrossing` — instantiation for NonCrossing w via
    `monotone_of_mem_nonCrossing`.
- Next bricks for H1 (in order): interval structure of configurations in a layer
  (ConfigInterval continues), generator rotation lemma (HMV L10 from the
  incidence certificate — predecessor_set_is_cyclic_interval is the first half),
  betweenness (L11), then the embedding of the realized permutation group of S
  into a cyclic rotation group.

### Sorry status

- `ShortWordProblem.lean:letterWordACC_impl` — still the single remaining
  non-comment `sorry` in the AllenderOQ3 library.

### Session 6 continued: generator leaf + layering toolkit

- **Leaf restated in generator form**: new `LetterWordACCGen` (letters are single
  certified layer maps, `isNonCrossingMap`), `letterWordACCGen_of_letterWord`,
  `windowWordACC_of_letterWordGen` (instantiation witness
  `⟨n, c, cert, i, x, hN, hW, rfl⟩` — this is all the application produces), and
  the single remaining sorry is now `letterWordACCGen_impl`.  Strictly weaker
  obligation: the old closure-form leaf implies it; per-letter incidence
  certificates are now available to the leaf-prover directly.
- `LocalizedCyclicity.lean` extended (still 0 sorries): `minLayer_antichain`,
  `layerRest_card_lt`, `exists_mem_minLayer` (the min-layering exhausts S below
  index S.card) — completing the P13 layering skeleton on the order side.
- Build 8158 green; trust PASS (0 external, 1 internal sorry); audit PASS.

### Session 6 continued (2): realized-permutation subgroup + assembly design

- **`RealizedPerms.lean` (new, 0 sorries)**: `RealizedPerm S e` (a permutation of
  the subtype of S implemented by an element of NonCrossing w),
  `realizedSubgroup S : Subgroup (Equiv.Perm {x // x ∈ S})` — one/mul/inv all
  proved (inverse = (card−1)-st power, realized by the corresponding power of the
  implementing element).  **The heart H1 is now the pinned Lean statement
  `IsCyclic (realizedSubgroup S)`.**  Also `bijOn_of_realizedPerm`,
  `realizedPerm_mem_minLayer` (layers respected), and `perm_eq_of_forall_minLayer`
  (determinacy reduction: layer agreement ⇒ equality, since layers cover S).
- **`docs/ASSEMBLY_DESIGN.md` (new)**: the authoritative E2-c design — holonomy
  tower for (NonCrossing w, Config w) following Eilenberg ch. XII, mapped onto
  cascade_cyclic_layer / cascade_aperiodic_layer, with the two care spots
  (relative Zeiger coordinates; per-epoch height-drop event bound) and a
  five-file Lean decomposition (E2-c-1 … E2-c-5).  E2-b (rotation form of H1/H2)
  proceeds in parallel and enters only via cyclicity of the holonomy groups.

### Session 6 continued (3): the E2-c-1 holonomy skeleton is COMPLETE (all 0 sorries)

- **`HolonomySkeleton.lean`** (namespace `Internal.Holonomy`): `ImageOf` (+ one/mul),
  the reachability preorder `Reach` (refl/trans, card-non-increasing), `ReachEquiv`
  (card equality), `StrictReach` (irrefl/trans), the height measure `hgtMeasure`
  (bounded by `Fintype.card (Finset (Config w))`, strictly drops along strict
  descents), run images `runImage` with `reach_runImage_of_le` via `blockEnd`
  (`blockEnd_mem_nonCrossing`), the generic decreasing-measure counter
  `card_filter_le_of_decreasing`, and **`card_epoch_events_le`** — along any run,
  the reached set leaves its mutual-reachability class at most
  `Fintype.card (Finset (Config w))` times.  This is the top-level epoch bound of
  the assembly design (care spot B), fully kernel-proved.
- **`HolonomyGroups.lean`**: `RealizedFamPerm`/`realizedFamSubgroup` — realized
  permutations of a FAMILY of configuration sets form a subgroup (inverse again by
  the positive-power trick); `bijOn_of_reachEquiv` — mutual-reachability witnesses
  act bijectively (card + `Finset.injOn_of_card_image_eq`).  **H2 is now the pinned
  statement `IsCyclic (realizedFamSubgroup 𝒜)`.**
- **`ConstantMaps.lean`**: `constTrans q ∈ NonCrossing w` for EVERY constant map —
  witnessed by an explicit two-layer all-literal circuit `constCircuit` (edge-free,
  `HMVNormal`, `TotalWidthAtMost w`, certificate from
  `incidenceCylinder_of_edgeFree`; the listing-to-input index map is a bijection, so
  a suitable input realizes every constant vector).  Hence `reach_singleton_of_mem`
  (every singleton reachable from every containing set), `reachableSet_singleton`,
  and the brick structure: `bricksOf` (maximal strict reachable subsets) with
  **`exists_brick_mem`** — every point of a ≥2-element set lies in some brick
  (a maximal strict reachable subset over `{q}` is maximal among all).
- Remaining for E2-c: coordinates + update laws (E2-c-3, needs the relative Zeiger
  form of the design doc), the gadget instantiation (E2-c-4), final assembly
  (E2-c-5); H1/H2 cyclicity (E2-b geometry) enters only at the cyclic layers.

### Sorry status

- `ShortWordProblem.lean:letterWordACCGen_impl` — still the single remaining
  non-comment `sorry` in the AllenderOQ3 library.

## Iteration: the stretch leaf, circuits versus algebra

New modules (all `sorry`-free):

- **`StretchTranscript.lean`**: `runTrans_blockProd_eq_of_transcript`,
  `mul_blockProd_eq_of_transcript` — a verified transcript of restrictions
  certifies `gin * blockProd = gout`, with no promise on the block.  This is the
  soundness core that makes the stretch circuits sound on *every* input.
- **`ACCGadgets.lean`**: `exists_acc_bigAnd`, `exists_acc_orPair`,
  `exists_acc_letterPred` — assembly gadgets over `accOrAnd`.
- **`StretchHolonomy.lean`**: the algebraic hypotheses `StretchHolonomyAt` /
  `StretchHolonomy`, and the reduction `stretchPrefixACC_of_stretchHolonomy`
  (`MOD`-gate prefix sums of a per-letter exponent, position-wise verification,
  depth 15, modulus `2N`).
- **`StretchHolonomyUnits.lean`**: `stretchHolonomy_at_one` — the holonomy
  hypothesis *does* hold at the identity prefix, where a shape-constant stretch
  consists of units of `NonCrossing w` and the unit group is cyclic; plus
  `stretchHolonomyAt_of_dvd` and `stretchHolonomy_of_forall` (per-prefix moduli
  merge into one, the transition monoid being finite).
- **`StretchHolonomyObstruction.lean`**: `not_stretchHolonomy_of_pos` — the
  holonomy hypothesis is **false** for every `0 < w`.  A sum of per-letter
  exponents cannot distinguish `g * h` from `h * g`; out of a rank-one prefix
  every word is shape-constant, and all constant maps lie in `NonCrossing w`
  (`constTrans_mem_nonCrossing`), so two distinct constant letters refute it.
  A correct algebraic leaf must let the compressed state record the reached
  `L`-class as well as the holonomy group element.

### Sorry status

- `LetterWordAssembly.lean:epochWordACC_pos` — the single remaining
  non-comment `sorry` in the AllenderOQ3 library.  Iteration 25 refactored
  the old monolithic `letterWordACCGen_pos` sorry into the strictly smaller
  `epochWordACC_pos` obligation via the proved reduction
  `letterWordACCGen_of_epochWordACC` (from `EpochReduction.lean`).  The
  obligation asks for a constant-depth polynomial-size ACC recognizer for
  a single *epoch block* — a window of `NonCrossing w` letters where the
  rank/shape coordinate of the prefix products is constant up to the last
  letter.  This is where the holonomy cascade cyclic/aperiodic layers
  (H1/H2 + `cascade_cyclic_layer` and `cascade_aperiodic_layer`) must be
  instantiated.

## Manual session 8 (2026-08-17, branch manual-close)

* `IntervalPieces.lean`, `IntervalStart.lean` — interval-piece infrastructure
  (decomposition into maximal cyclic blocks, pointwise reconstruction by an explicit
  walk, canonical start/length); sorry-free.
* `IntervalReduction.lean`, `LayerRestriction.lean`, `IntervalCoreStatements.lean` —
  the HMV-P13 interval route to the heart lemma H1, machine-checked as implications
  and **recorded as obstructed**: core A (interval-wise action of stabilizers) and
  layer rigidity are FALSE for `NonCrossing w` from `w = 4` on (exact-model
  counterexamples in the headers; four-letter witness `rot 3 ; dup 0→1 ; dup 1→2 ;
  set pos 1 := 0` swaps `0001 ↔ 1010`).
* `LayerProduct.lean` — the surviving reduction: layer restrictions embed
  `realizedSubgroup S` into the product over antichain layers; **antichain
  commutativity (a fortiori antichain cyclicity) implies commutativity of every
  realized permutation group** (`realizedSubgroup_comm_of_antichains_cyclic`);
  sorry-free.
* `docs/EXACT_MODEL_NOTES.md` + `docs/experiments/exact_layers_w4.py` — the exact
  certified-layer model at w = 4 (21,360 layers, monoid 3,551,466; bijectives =
  exactly the 4 rotations, matching `unit_isShiftMap`): **every realized permutation
  group over all subsets of sizes 2–5 is cyclic** (orders 2, 3, 4) — H1 holds on the
  exact monoid; the iter-15 Python enumeration is UNSOUND and must not be used.

Sorry count unchanged (2: `monoidWordACC_nonCrossing`, `isCyclic_realizedSubgroup`);
build green (8183 jobs), trust PASS, dependency PASS.

## Manual session 9 (2026-08-18): route change to local divisors

The Barrington–Thérien obligation is restructured onto the local-divisor route
(`docs/LOCAL_DIVISOR_PLAN.md`; verified paper proofs in `docs/localdivisor/`).
The two former sorries (`monoidWordACC_nonCrossing` stub, H1
`isCyclic_realizedSubgroup`) are RETIRED; `monoidWordACC_nonCrossing` is now
DERIVED sorry-free in `LocalDivisorRoute.lean` from five sharper leaves:

* S1 `localUnitsCommute_of_surjective` (LocalUnitsCommute.lean) — groups lift
  through surjections of finite monoids;
* S2 `monoidWordACCGen_compression` (LocalDivisorCompression.lean) — the
  marked block-local compression lemma;
* S3 `monoidWordACCGen_of_genOn` (ibid.) — representation expansion;
* S4 `monoidWordACCGen_of_localUnitsCommute` (LocalDivisorInduction.lean) —
  the strong induction;
* S5 `localUnitsCommute_nonCrossing` (LocalDivisorRoute.lean) — abelianness of
  the local groups of the certified monoid (decomposition 6a–6e in the plan).

New sorry-free infrastructure: `MonoidWordACCGen.lean` (generalized interface,
`monoidWordACC_of_gen`, `monoidWordACCGen_of_comm`, submonoid/quotient/divisor
closures — committed from the iteration-30 draft), `LocalUnitsCommute.lean`
(first-order all-subgroups-abelian predicate, submonoid transport, units base
case, finite one-sided-inverse lemma), `LocalDivisor.lean` (the local divisor
monoid, `mul_val`/`mul_val'`, strict cardinality decrease, the canonical
surjection from `localDivisorDom`).  H2 corollary removed from
`ConstantMaps.lean` (dead); `HMVInterval.lean` (trivial stub) deleted.

Build green (8191 jobs), trust PASS (0 external / 5 internal sorries),
dependency PASS.

## Manual session 10 (2026-08-18): T0 reroute + T5 glue, five sharp leaves

Following the iteration-31 strategy: the mis-shaped general antichain leaf is
retired; new sorry-free glue lands in `IntervalRouteCF.lean` (stratification
argument of paper section 5: pieces of `Fix e` are `e`-fixed, local units
permute the piece family and its `minLayer` strata, reconstruction from
pieces, `e`-collapse), `ComponentLemma.lean` (word-level component lemma via
`componentSubmonoid`), and `ConstantElimination.lean` (the clamp/fill
conjugation `Phi f = A * f * B`: multiplicativity, transport of the thirteen
local-unit equations, no-constant-outputs via surjectivity on `Fix e`,
injectivity via `J`-coordinate recovery, degenerate case).  Remaining sorries
= five single-purpose leaves: per-layer component inequality and equality case
(`ComponentLemma`), interval-antichain rotation geometry (`IntervalRouteCF`),
clamp/fill construction and constant propagation (`ConstantElimination`).
Build green (8198 jobs), trust PASS (0 external / 5 internal), dependency
PASS.  Plan updated: `docs/LOCAL_DIVISOR_PLAN.md` section 9.
