# Allender OQ3 in Lean 4.28

This project formalizes the corrected version of Allender's Open Question 3:
constant-computation-width layered circuits of polylogarithmic orientable genus
have nonuniform `ACC^0` simulations.

The exact audited circuit model is in `AllenderOQ3/Model.lean`.  The target is
`turing_candidate_000003` in `AllenderOQ3/Target.lean`.

## Trust boundary

The frozen interface contains three principle signatures.  The first -- that
zero minimum rotation genus is attained by a zero-genus rotation -- is now
kernel-proved from the finite rotation system developed in this project.
Exactly two permanent external proof obligations remain in
`AllenderOQ3/ExternalFacts.lean`:

1. realization of a zero-genus rotation together with Hansen's finite
   arc-incidence order principle for properly layered st-graphs;
2. the quantitative fixed-width cylindrical-circuit simulation in `ACC^0`.

The conditional theorem `turing_candidate_000003_of_principles` and all
project-specific proof modules are sorry-free.  The final wrapper supplies the
proved attainment principle and the two remaining external facts.

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
