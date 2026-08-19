#!/usr/bin/env bash
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo"

python3 scripts/check_challenge_matches_model.py
python3 scripts/check_trust.py --release --require-no-external
bash scripts/audit.sh

python3 - <<'PY'
from pathlib import Path
import re

text = Path("proof_loop/axiom_report.txt").read_text(encoding="utf-8", errors="replace")

def axioms(name: str) -> set[str]:
    pattern = rf"'{re.escape(name)}' depends on axioms:\s*\[(.*?)\]"
    match = re.search(pattern, text, flags=re.DOTALL)
    if match is None:
        raise SystemExit(f"missing #print axioms report for {name}")
    return {part.strip() for part in match.group(1).split(",") if part.strip()}

standard = {"propext", "Classical.choice", "Quot.sound"}
conditional = axioms("turing_candidate_000003_of_principles")
final = axioms("turing_candidate_000003")
attainment = axioms("AllenderOQ3.External.rotationZeroPlanarity")
unexpected_conditional = conditional - standard
unexpected_final = final - (standard | {"sorryAx"})
unexpected_attainment = attainment - standard
if "sorryAx" in attainment:
    raise SystemExit("rotationZeroPlanarity still depends on sorryAx")
if unexpected_attainment:
    raise SystemExit(f"unexpected rotationZeroPlanarity axioms: {sorted(unexpected_attainment)}")
if "sorryAx" in conditional:
    raise SystemExit("conditional theorem still depends on sorryAx")
if unexpected_conditional:
    raise SystemExit(f"unexpected conditional axioms: {sorted(unexpected_conditional)}")
if "sorryAx" in final:
    raise SystemExit("final theorem still depends on sorryAx")
if unexpected_final:
    raise SystemExit(f"unexpected final axioms: {sorted(unexpected_final)}")
PY

if grep -Fq 'No internal milestone has yet been formalized' COVERAGE.md; then
  echo "COVERAGE.md still contains the initial placeholder; release rejected." >&2
  exit 1
fi

echo "release audit: PASS"
