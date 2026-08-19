# Formalization architecture

The Lean development is complete: the project library contains no `sorry`, and
the headline theorem uses only Lean's standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.  This file records the proof architecture
rather than an unfinished work plan.

## Trusted interface

The exact circuit model and theorem statement are concentrated in:

- `AllenderOQ3/Model.lean`;
- `AllenderOQ3/Incidence.lean`;
- `AllenderOQ3/Principles.lean`;
- `AllenderOQ3/Statement.lean`.

Their checksums are recorded in `proof_loop/frozen_api.sha256`.  The three
principle signatures remain visible in the API, but all three implementations
in `AllenderOQ3/ExternalFacts.lean` are now proved inside the project.

## Proof layers

1. **Circuit semantics and normalization.**  The development formalizes ADR
   valuation, ancestor pruning, occupied-layer compression, output restriction,
   and total-width bookkeeping.
2. **Genus and planarization.**  Rotation systems, orbit counts, edge-deletion
   surgery, the Euler defect, interval piercing, and the layer planarizer turn
   the genus bound into a bounded collection of planar blocks and exceptional
   transitions.
3. **Planar blocks.**  A bridge-safe necklace construction proves the Hansen
   arc-incidence-order principle for properly layered planar st-circuits.
4. **Cylindrical normalization.**  The N4 refinement, fan-in reduction, port
   circuits, and exact substitution lemmas preserve semantics, incidence
   certificates, depth, width, and polynomial size.
5. **Finite-monoid evaluation.**  Rather than formalizing the full
   Barrington--Therien theorem, the Lean proof establishes the needed special
   case directly.  Certified layer maps have abelian local groups, and a
   local-divisor induction constructs the required `ACC^0` word evaluator.
6. **Composition and family assembly.**  Constant-depth relation composition,
   modulus lifting, the large-input cutoff, and the finitely many small input
   lengths yield the final nonuniform family.

The public theorem `turing_candidate_000003_of_principles` exposes the three
principle inputs.  The wrapper `turing_candidate_000003` supplies their proved
implementations.

## Verification

Run the complete local release audit with:

```bash
lake build
bash scripts/audit_release.sh
```

`Challenge.lean` intentionally contains one placeholder theorem: it is the
standalone statement consumed by `leanprover/comparator`, not a dependency of
the project proof.  `Solution.lean` closes that exact statement, and the
Comparator workflow checks the exported proof against the permitted axiom
set.
