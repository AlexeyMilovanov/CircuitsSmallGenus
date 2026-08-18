# Closing the two remaining external facts

Project: `/home/lesha/allender-oq3-lean-28`.

## Global objective and status

The audited Allender OQ3 proof is kernel-checked modulo exactly two theorem
bodies in `AllenderOQ3/ExternalFacts.lean`:

1. `External.hansenArcOrder : HansenArcOrderPrinciple`;
2. `External.quantitativeCylindricalACC : QuantitativeCylindricalACCPrinciple`.

The objective of every ordinary conveyor iteration is to reduce and eventually
eliminate these two `sorry`s, together with every temporary supporting `sorry`
introduced on the way.  The priorities below are a rolling map, not an
iteration schedule.  Agents must inspect the actual tree, skip completed work,
continue past items finished early, and choose a sound alternative whenever a
suggested route stalls.  No iteration should be empty merely because an older
plan item is already complete.

The exact three principle propositions live in checksum-frozen
`AllenderOQ3/Principles.lean`.  Proof bodies in `ExternalFacts.lean` are
actionable.  `Model.lean`, `Incidence.lean`, `Principles.lean`, and
`Statement.lean` must not change.

## Audit of the proposed mathematics

Both remaining statements are credible and match the interfaces consumed by
the completed internal proof.  They should remain separate: E1 is applied to
the st-core before binarization, while E2 is applied after the kernel-proved
incidence refinement, when many input sources may be present.

The necklace route proposed for E1 is sound in outline, but its implementation
must work with oriented face incidences/darts.  Statements such as “each edge
borders two distinct faces” and “the other transition arc of a face” are false
for bridges.  A one-edge path has one face orbit and two face-side occurrences
of the same directed transition arc.  The construction below explicitly
handles that case.

The earlier direct E2 plan based only on prefix-rank drops is not valid and must
not be treated as a theorem.  Two certified width-two counterexamples are:

* `R(x1,x2) = (x2,x1)`.  As a permutation of the four Boolean states it fixes
  `00` and `11` and swaps `01` and `10`; it is not a nontrivial rotation of one
  cyclic order on all four states.
* `A(x1,x2) = (x1,x1 OR x2)`, followed by alternating `R`.  Prefix rank stays
  three while the image alternates between `{00,01,11}` and `{00,10,11}`.

Thus constant rank does not stabilize the image, and at most `K-1` rank-drop
positions do not determine a run.  Any replacement for Barrington--Therien
must control Green/J-class dynamics or supply an equally strong proved
factorization theorem.  Small-width computation is useful for falsification,
not as evidence that the rejected rank-only lemma is true.

## E1: Hansen common arc-incidence order

### Recommended route

Prove the exact expanded signature internally (or import the frozen principle
type from `Principles.lean`) and wrap it in `ExternalFacts.lean` only after it
builds.  Avoid importing `ExternalFacts.lean` from the closing modules.

1. **Proper-layered st preliminaries.**  Develop variants of the needed path
   lemmas assuming `ProperLayered`, not `WellFormedADR`.  Use a decreasing
   measure such as `maxLayer - layer v` or finite acyclicity for paths to the
   sink.  Prove that every vertex lies on an s-to-t path, occupied layers form
   an interval, the underlying graph is connected, directed edge count agrees
   with `underlyingEdgeCount`, and nontrivial connected cases have no isolated
   vertices.  Dispatch the one-vertex/edge-free case with the existing empty
   certificate constructor.

2. **Euler--Morse corner count.**  For a zero-genus rotation, classify darts as
   up/down and count up-to-down cyclic switches at vertices.  Prefer finite
   dart sets and the existing quotient-orbit count over prematurely building
   explicit orbit lists.  Establish the Euler sandwich forcing one up-block
   and one down-block at each relevant vertex and exactly one minimum and one
   maximum corner occurrence in each face orbit.

3. **Bridge-safe face sides.**  Define transition crossings as oriented
   face-side incidences.  For an up-dart `d`, use the face orbit containing
   that particular dart occurrence; locate the unique opposite crossing
   occurrence on the same transition and project its reverse to a
   `TransitionArc`.  Define predecessor from `dartReverse d` and prove the two
   maps inverse.  On a bridge, successor may map the sole arc to itself.

4. **Necklace.**  Prove monotonicity of the two face sides, consecutive input
   and output fibres, the source-layer base cycle, and the simultaneous
   block-rewrite step.  Include the cases where both persistent sides belong
   to the same face orbit and where a rotation cycle has one element
   (`Perm.toList` needs an explicit singleton treatment).

5. **Certificate assembly.**  Materialize cyclic layer listings and the common
   arc word, then use the proved `arcOrderCertificate_of_rotatedDoubleGrouped`
   interface to construct `IncidenceCylinder`.

### Early executable milestones

Before committing to the full corner library, build a bridge-safe
`neckSucc/neckPred` prototype and test its definitions on a one-edge graph, a
path, a diamond, and two diamonds joined by a bridge.  These tests are not the
proof but catch the most dangerous convention errors.

Expected scale: roughly 7--14k Lean lines, with 12--20k possible if dependent
orbit transport dominates.  The former 4--8k estimate was an optimistic floor.

## E2: quantitative fixed-width incidence-cylinder simulation

### Mandatory normalization layer

Before algebra, handle the exact interface:

* output-literal and width-zero cases;
* unused/output-irrelevant gates and arbitrary sparse numeric layer labels;
* restriction or reconstruction of the incidence certificate;
* a certificate-aligned indexing of **all** vertices in a layer, not the
  existing computation-only `LayerIndexing`;
* a finite structural transition type depending only on width, separated from
  hardwired references to arbitrary `Fin n` input variables;
* modulus at least two (use a factor `2` explicitly);
* polynomial size in `gateCount`, not in the number of input variables.

Enumerating occupied layers can avoid dependence on huge sparse layer labels:
proper layering ensures that a numeric gap carries no edges.  Alternatively,
prune to the output cone and prove certificate restriction plus layer
compression.

### Recommended faithful route

1. Define the exact finite geometric/incidence transition monoid
   `Nhat W` used by a certificate-aligned circuit and prove word extraction and
   evaluation correctness.
2. Port the substantive HMV finite-algebra argument rather than the false
   rank-only shortcut: constant removal/normalization, interval-antichain
   invariants, and the analogues of Proposition 8 and Lemmas 9--13 showing that
   every subgroup is cyclic (hence solvable).
3. Isolate a precise generic theorem for word problems of fixed finite
   solvable monoids in `ACC^0`, with the quantitative order of parameters needed
   here.  Prove E2 from that theorem plus the monoid extraction.
4. Close the generic theorem by a faithful Barrington--Therien proof, a
   factorization-forest/local-divisor route with a fully stated quantitative
   induction, or a reusable existing formal library if a compatible one is
   found.  Do not replace it by an informal profile argument.

This decomposition may temporarily create smaller supporting `sorry`s in
internal modules.  That is acceptable only when their statements are strictly
more standard or more local than E2 and the total trust boundary is recorded;
the final completion criterion remains zero `sorry` everywhere.

### Research pivot rule

If a proposed direct ACC evaluator is substantially shorter than the standard
monoid route, first state its key finite-semigroup normal-form theorem exactly
and adversarially test it against same-rank moving-image examples.  Do not build
large circuit bookkeeping on top of an unproved or false normal form.  If that
theorem fails, return to the faithful HMV plus Barrington--Therien route rather
than stopping the conveyor.

The full E2 cost is uncertain and likely dominates E1.  A realistic baseline
is tens of thousands of Lean lines; earlier 3--6 month estimates assume that a
usable algebraic decomposition becomes available quickly.

## Adaptive conveyor policy

Strategic rounds reassess the current dependency graph and provide a rolling
priority map.  They never assign immutable work to iteration numbers.  Ordinary
Gemini and Opus rounds must repair the latest failed build first and then keep
advancing the global objective.  Aristotle receives the best exact leaves
available after Opus.  Failed audits preserve the worktree for the next repair
round; a waiting remote task is polled rather than resubmitted; process failure
is supervised and resumes the same run.

Completion means:

* no `sorry` or `sorryAx` in project source;
* both exact frozen principle signatures unchanged;
* full Lean build and trust/dependency audits pass;
* `turing_candidate_000003`, not only its conditional form, is free of
  `sorryAx` in `#print axioms`.

## STATUS UPDATE 2026-08-16 (user sessions, kernel-checked)

Section 1 (E1) is largely DONE ahead of the written plan, along a combinatorially
different but equivalent route (necklace via first-return of the face
permutation instead of explicit neckSucc; see COVERAGE.md for the precise
lemma inventory):

- 1.1 Step A (st-structure): DONE (StGraph.lean).
- 1.2 Step B/C (Euler-Morse sandwich): DONE both halves - bimodality
  (switchCount_eq_one_of_internal, MinCorner.lean) AND per-face unimodality,
  min and max side (FaceUnimodal.lean: existsUnique_min/maxCorner_in_faceOrbit).
- 1.3 Step D (monotone sides / two crossings): DONE in the stronger form
  firstReturn_involutive (FirstReturnChain.lean).
- 1.4 Step E/F (necklace): definitions and machinery DONE (CutNecklace.lean:
  neckPerm, arcPerm, orbit words, alternation both directions); corner-step
  adjacencies DONE (arcPerm_of_minCorner/_maxCorner); base-case single orbit
  DONE (single_orbit_of_common_source).
- 1.5 Step G (assembly): wired (NecklaceAssembly.lean reduces hansenArcOrder
  to the three named obligations in CutNecklace.lean).

Remaining for E1: the three CutNecklace sorries - fiber-block structure per
vertex, the two GroupedAlong obligations (list bookkeeping), completeness by
upward induction. Section 2 (E2) unchanged; note the added guards: the
rank-drop-only shortcut for F3c is refuted (width-two counterexample), and
solvability must be argued on the incidence-constrained submonoid, never the
full transformation monoid.

