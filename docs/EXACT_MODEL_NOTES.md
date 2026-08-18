# Exact computational model of `NonCrossing w` and the fate of the interval route

*Session 2026-08-17 (manual, branch `manual-close` in `~/oq3-manual`).  Experiments in
`~/oq3-experiments/{exact_layers_w4.py, conservative_w4.py, cons_fanout_w4.py, sampled_w4.py,
rotation_structure.py}`.*

## 1. The Python model used since iter-15 is UNSOUND at w ≥ 4

The enumeration convention of `hmv_explore.py` / `localized_cyclicity.py` (outputs read
arbitrary cyclic-interval windows, any window size, plus arbitrary non-crossing singleton
matchings) does **not** match the frozen Lean definition of a certified layer
(`IncidenceCylinder` + `HMVNormal` + `TotalWidthAtMost`).  Verified discrepancies at w = 4
(spot-checked against the arc-word rotation condition with standard listings, which is
WLOG — listing freedom only renames vertices and rotates whole words):

* fan-in is bounded by 2 (`HMVNormal`), so width-3/4 windows are not single layers
  (they may or may not be recoverable as products — wire budget is the obstacle);
* a gate reading a NON-adjacent pair (e.g. `AND(0,2)` with all other wires preserved) is
  **not** certifiable, and plausibly not in the monoid at all (bringing wires 0 and 2
  together while preserving 1 and 3 exceeds the width budget);
* far fan-out (duplicating a wire into a non-adjacent position in one step) is not a
  certified layer;
* wire transposition is not certifiable — consistent with the kernel-proved
  `nonCrossing_units_cyclic`/`unit_isShiftMap` (units are rotations).

Certified in the exact sense and safe to use as generators: all constant maps
(`constTrans_mem_nonCrossing`, kernel-proved), adjacent-pair `AND`/`OR`, rotations,
adjacent fan-out (duplicate wire i into positions i, i+1), literals = per-gate free
constant bits, and everything with ≤ 2 fan-in passing the arc-word check
(21,360 full-width tables at w = 4, enumerated exactly in `exact_layers_w4.py`).

**Consequence.**  The w = 4 "refutations" obtained on the old model (interval-count
preservation broken, interval-wise action broken, minimal-layer rigidity broken — see
`sampled_w4.log`) are artifacts of unsound generators unless they reproduce on the exact
model.  Conversely, the w ≤ 3 cyclicity confirmations DO carry over to the true monoid
(the old model is a supermonoid there; a subgroup of a cyclic group is cyclic).

## 2. Verified structure results (exact/conservative models)

* Conservative monoid ⟨constants, adjacent AND/OR, shifts, adjacent fan-out⟩ at w = 4:
  697–699k elements, full closure.  Over ALL subsets of size 2–5: every realized
  permutation group is **cyclic** (orders 1,2,3,4); interval-count preservation and
  interval-wise action of stabilizers hold without exception.
* w = 3 (old model, hence a fortiori exact): all 255 subsets — cyclic, orders ≤ 3.
  Note w ≤ 3 is DEGENERATE for the interval theory (every proper config is a single
  cyclic arc), so w ≤ 3 evidence says nothing about the interval mechanism itself.
* **Exact model at w = 4 — the decisive data set** (`exact_fast.log`,
  `exact_tests.log`): 21,360 certified full-width layers; closure = **3,551,466
  elements** (built by iterative generator growth; the family the conservative set was
  missing is the *partial constants* — a literal at one position, wires kept elsewhere).
  Validation: the bijective elements of the exact monoid are **exactly the 4
  rotations**, matching the kernel-proved `nonCrossing_units_cyclic`/`unit_isShiftMap`.
  Over ALL subsets of sizes 2–5 (693 nontrivial groups):
  - **NON-CYCLIC groups: 0.  H1 holds on the exact monoid; order spectrum {2, 3, 4}.**
  - Interval-count preservation FAILS (6 witnesses, e.g. the swap `0001 ↔ 1010`,
    realized by the four-letter word `rot 3 ; dup 0→1 ; dup 1→2 ; set pos 1 := 0`:
    a discarded coordinate frees a wire, and duplications carry a block across the
    cut).  Hence core A (`StabIntervalAction`) is FALSE for the true monoid.
  - Minimal-layer rigidity FAILS (6 witnesses: bottom-fixing three-cycles on families
    of interval configurations, e.g. `{0001, 0111, 1011, 1101}`); the groups there are
    still cyclic (`Z₃`).  Hence `LayerRigid` is not universally available.
  - Refined positive: among *count-preserving* stabilizer permutations the
    interval-wise action held without exception — a possible repaired core
    ("count-preserving stabilizers act interval-wise") if the interval route is ever
    revisited for the count-preserving subgroup.
  (Narrow/padded layers are excluded; they only add elements, so the failures are
  genuine members; the all-cyclic verdict still needs the padded variants checked
  before being treated as exhaustive.)

## 3. State of the Lean development (branch `manual-close`)

New sorry-free files, all building green against the frozen statements:

* `IntervalPieces.lean` — maximal cyclic blocks of a configuration as configurations
  (`intervalsOf`), pointwise reconstruction (`mem_intervalsOf_true_iff`, walk proof),
  pieces are interval configs.
* `IntervalStart.lean` — canonical start (unique rising edge) and length; interval
  configs with equal starts are comparable; incomparable ones have distinct starts.
* `IntervalReduction.lean` — H1 reduced to core A (`StabIntervalAction`) + core B
  (`IntervalSetsCyclic`).  **Core A is refuted on the exact monoid** (obstruction
  header records the four-letter witness); the file is kept as the precise record of
  where the HMV interval route fails.
* `LayerRestriction.lean` — core B reduced per `T` to minimal-layer H1 + `LayerRigid T`.
  **Rigidity is refuted on the exact monoid** (obstruction header records the
  bottom-fixed three-cycles).
* `IntervalCoreStatements.lean` — the three-core assembly, kept as the statement of
  what the HMV route would have needed (cores A and B2 false; B1 — antichain
  cyclicity — has no counterexample).
* `LayerProduct.lean` — **the live reduction that survives all refutations**: the
  min-layering partitions `S`, restriction to each antichain layer is a group
  homomorphism `resHomAt`, and the joint map is injective
  (`eq_one_of_forall_resHomAt`).  Consequences (sorry-free):
  `realizedSubgroup_comm_of_antichains` — if realized groups of *antichains* are
  commutative, then every realized group is commutative; and
  `realizedSubgroup_comm_of_antichains_cyclic` — antichain *cyclicity* already gives
  commutativity everywhere.  Commutative holonomy groups are all the cascade needs
  (`monoidWordACC_of_comm`), so the programme after the interval obstructions is:
  **prove `AntichainsCyclic w` (or just `AntichainsCommute w`)** — the heart lemma's
  remaining genuinely geometric content — and, if full cyclicity of H1 is wanted,
  find the cross-layer synchronization mechanism (empirically the groups are cyclic,
  not just abelian; element orders ≤ w in all data).

H1 itself stays pinned as the single sorry `isCyclic_realizedSubgroup`
(`RealizedPerms.lean`), now with strong exact-model support and a clear route map.

## 4. HMV vs. our monoid

HMV's L9 ("f(x) has at most as many intervals as x") is FALSE for our monoid as a
per-element statement: literal gates inject constants, splitting intervals (example:
layer `[AND1, const0, AND3, AND4]` maps 1110 to 1010).  Any interval analysis must be
run along *stabilized* trajectories (bijectivity on S), which is exactly what core A
formalizes.  HMV's P13 rigidity argument survives only in the per-T form of
`LayerRigid`; its truth for the true monoid is part of the exact-model test.
