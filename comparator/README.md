# Comparator certificate for Allender OQ3

This repository uses
[`leanprover/comparator`](https://github.com/leanprover/comparator) to separate
the statement a reviewer must read from the AI-assisted proof.

- [`../Challenge.lean`](../Challenge.lean) imports only Mathlib and contains
  the complete trusted statement, including every custom definition used by
  its type.
- [`../Solution.lean`](../Solution.lean) connects that statement directly to
  `turing_candidate_000003`.
- [`config.json`](config.json) asks Comparator to check the bridge while
  permitting only standard axioms like `propext`, `Quot.sound`, and `Classical.choice`.

Comparator checks that the solution proves exactly the challenge statement,
uses no other axioms, and is accepted by the Lean kernel.
