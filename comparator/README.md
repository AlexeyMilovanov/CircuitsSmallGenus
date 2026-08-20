# Comparator certificate for Allender OQ3

This repository uses
[`leanprover/comparator`](https://github.com/leanprover/comparator) to separate
the statement a reviewer must read from the AI-assisted proof.

- [`../Challenge.lean`](../Challenge.lean) imports only Mathlib modules (the
  same explicit header as `AllenderOQ3/Model.lean`) and contains
  the complete trusted statement, including every custom definition used by
  its type.
- [`../Solution.lean`](../Solution.lean) connects that statement directly to
  `turing_candidate_000003`.
- [`config.json`](config.json) asks Comparator to check the bridge while
  permitting only standard axioms like `propext`, `Quot.sound`, and `Classical.choice`.

Comparator checks that the solution proves exactly the challenge statement,
uses no other axioms, and is accepted by the Lean kernel.

`scripts/check_challenge_matches_model.py` additionally checks that the
definitions in `Challenge.lean` are still character-identical to the project
interface in `AllenderOQ3/Model.lean`, so that the trusted statement cannot
drift away from the definitions the proof actually uses.

The `Comparator` GitHub Actions workflow performs the check in a fresh Linux
runner.  It does not restore a project build cache or compile `Solution.lean`
before Comparator, and it uses the upstream `systemd-run` sandbox hardening.

For a manual Linux run, obtain the `v4.28.0` tags of Comparator and
lean4export, install the pinned/current landrun described by the upstream
Comparator documentation, prepare only the trusted dependency cache, and run:

```bash
scripts/verify_with_comparator.sh \
  /path/to/leanprover-comparator-v4.28.0 \
  /path/to/lean4export-v4.28.0
```

Use a fresh checkout: compiling `Solution.lean` before Comparator invalidates
the adversarial-checking assumption.

A human must still read `Challenge.lean` and decide that it expresses the
intended mathematics.  The one `sorry` in that file is the intentional
challenge hole; the proved formalization itself contains none.
