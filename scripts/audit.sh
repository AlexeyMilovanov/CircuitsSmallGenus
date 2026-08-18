#!/usr/bin/env bash
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo"

python3 scripts/check_trust.py
python3 scripts/check_dependencies.py --root "$repo"

axiom_tmp="$(mktemp proof_loop/.axiom_report.XXXXXX)"
trap 'rm -f "$axiom_tmp"' EXIT

# Warnings are informational.  Only an actual Lean build failure blocks the
# proof loop; style and linter warnings must not stop productive iterations.
/home/lesha/.elan/bin/lake build

/home/lesha/.elan/bin/lake env lean Main.lean >"$axiom_tmp" 2>&1
if [[ -L proof_loop/axiom_report.txt || (-e proof_loop/axiom_report.txt && ! -f proof_loop/axiom_report.txt) ]]; then
  echo "Unsafe axiom report destination" >&2
  exit 1
fi
chmod 0644 "$axiom_tmp"
mv -fT -- "$axiom_tmp" proof_loop/axiom_report.txt

python3 scripts/check_dependencies.py --root "$repo"

echo "audit: PASS"
