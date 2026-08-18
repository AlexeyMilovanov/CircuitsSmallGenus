# Allender OQ3 in Lean 4.28

This project formalizes the corrected version of Allender's Open Question 3:
constant-computation-width layered circuits of polylogarithmic orientable genus
have nonuniform `ACC^0` simulations.

The exact audited circuit model is in `AllenderOQ3/Model.lean`.  The target is
`turing_candidate_000003` in `AllenderOQ3/Target.lean`.

## Trust boundary

The frozen interface contains three principle signatures: zero minimum
rotation genus is attained by a zero-genus rotation; Hansen's finite
arc-incidence order principle for properly layered st-graphs; and the
quantitative fixed-width cylindrical-circuit simulation in `ACC^0`.  All three
are now kernel-proved inside the project (`AllenderOQ3/ExternalFacts.lean`);
the signatures are kept so that the conditional theorem
`turing_candidate_000003_of_principles` still exposes exactly which
assumptions the final wrapper supplies.

The project sources contain no `sorry` (the remaining textual occurrences are
retired or refuted statements preserved inside comment blocks), and the
headline theorem is axiom-clean:

```
'turing_candidate_000003' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Main.lean` reproduces this report, `scripts/check_no_sorry.py` enforces the
`sorry` scan, and the `Lean` workflow runs both on every push.

## Comparator certificate

`Challenge.lean` (imports only Mathlib) carries the complete trusted statement
with every definition it depends on, copied verbatim from
`AllenderOQ3/Model.lean`; `scripts/check_challenge_matches_model.py` enforces
that this copy stays exact.  `Solution.lean` closes that statement with
`turing_candidate_000003`.  The `Comparator` workflow, and
`scripts/verify_with_comparator.sh` for manual runs, check with
[`leanprover/comparator`](https://github.com/leanprover/comparator) that the
solution proves exactly the challenge statement using only `propext`,
`Quot.sound`, and `Classical.choice`.  See `comparator/README.md`.

Read, in order:

- `docs/MATHEMATICAL_PROOF.md`;
- `docs/EXTERNAL_FACTS.md`;
- `docs/INCIDENCE_REFINEMENT.md`;
- `FORMALIZATION_PLAN.md`.

## Build and audit

```bash
lake build
bash scripts/audit.sh
```

The proof pipeline is deliberately not started by default:

```bash
python3 scripts/run_proof_pipeline.py --list-sections
python3 scripts/run_proof_pipeline.py \
  --section oq3 --iterations 1 --start-iteration 1 --dry-run
```

The production conveyor is Gemini 3.1 Pro High, then a separate Claude CLI
pinned to `claude-opus-4-8`, then Aristotle.  Iterations `1, 6, 11, ...` are
strategy-only and plan the following four proof iterations.

After explicit approval, start it with `scripts/launch_pipeline.sh`.  If the
process is interrupted, `scripts/resume_pipeline.sh` reuses `ACTIVE_RUN`,
polls any already-submitted Aristotle project instead of resubmitting it, and
continues with the original global iteration numbers.
