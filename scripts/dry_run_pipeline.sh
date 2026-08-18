#!/usr/bin/env bash
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo"

python3 scripts/test_pipeline_safety.py

python3 scripts/run_proof_pipeline.py \
  --section external_facts \
  --iterations 7 \
  --start-iteration 1 \
  --strategy-first 1 \
  --strategy-every 5 \
  --dry-run
