# Formalization plan

The frozen API consists of `Model.lean`, `Incidence.lean`,
`ExternalFacts.lean`, and `Statement.lean`.  If an inconsistency is found there, stop with
`INTERFACE_PROBLEM`; do not silently weaken it.

The main proof is conditional on `QuantitativeCylindricalACCPrinciple`.  Finish
that proof first.  The optional transfer from the Barrington--Therien
solvable-monoid word theorem to this geometric/incidence-order principle is a
separate post-main project and must not block or redirect the main pipeline.

Suggested dependency order:

1. deterministic ADR valuation and ancestor pruning;
2. translate the pruned occupied layer interval to start at zero and prove
   that its span is at most the gate count (never iterate up to a sparse raw
   `Nat` layer label);
3. finite permutation/orbit lemmas for rotations and faces;
4. edge-deletion surgery, component defect sums, and the genus budget;
5. greedy packing/piercing for integer intervals;
6. the layer-planarizer theorem;
7. fixed-width slot states and one-step relations;
8. exact half-open cut decomposition;
9. restriction of incidence certificates and the N4 refinement construction,
   encoding every paper COPY as unary OR and every Boolean constant as a
   nullary AND/OR in the actual `ADRCircuit` syntax;
10. planar-width induction and predecessor-closed external ancestor circuits,
    with the explicit size/depth recurrence from the mathematical proof;
11. beta circuits plus an exact fresh-input substitution lemma: finite-sum
    input reindexing, separate positive-copy/negative-NOT occurrences, layer
    shifting, semantics, depth, and polynomial size;
12. common-modulus lifting with distinct shared unary copies;
13. polylogarithmic finite-state relation composition, including the explicit
    large-`n` cutoff for the `k+1` blocking rounds;
14. small input lengths and final family assembly.

The final internal theorem must be:

```lean
theorem turing_candidate_000003_of_principles :
    AllenderOQ3ConditionalStatement := by
  intro hRotation hHansen hCylinderACC
  ...
```

It should have no project-specific axioms when checked by `#print axioms`;
the proved attainment principle and the two permanent obligations enter only in the final wrapper.
