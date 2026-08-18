#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd -- "$SCRIPT_DIR/.." && pwd)"

COMPARATOR_COMMIT="7a0cae3df7a0200ff330c82420b8d88a51c9cac7"
LEAN4EXPORT_COMMIT="d065b0009aed0520e9e99752847a33b337661690"
COMPARATOR_MANIFEST_LEAN4EXPORT="048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d"

usage() {
  cat >&2 <<'EOF'
Usage: scripts/verify_with_comparator.sh COMPARATOR_DIR LEAN4EXPORT_DIR

COMPARATOR_DIR and LEAN4EXPORT_DIR must be clean checkouts of, respectively,
leanprover/comparator and leanprover/lean4export at tag v4.28.0.  A current
landrun binary must be on PATH.  Run this only in a fresh checkout in which
Solution.lean has never been compiled.
EOF
}

COMPARATOR_DIR="${1:-}"
LEAN4EXPORT_DIR="${2:-}"
if [[ -z "$COMPARATOR_DIR" || -z "$LEAN4EXPORT_DIR" ]]; then
  usage
  exit 2
fi

COMPARATOR_DIR="$(cd -- "$COMPARATOR_DIR" && pwd)"
LEAN4EXPORT_DIR="$(cd -- "$LEAN4EXPORT_DIR" && pwd)"

check_revision() {
  local directory="$1"
  local expected="$2"
  local label="$3"
  local actual
  actual="$(git -C "$directory" rev-parse HEAD)"
  if [[ "$actual" != "$expected" ]]; then
    echo "error: $label is at $actual, expected $expected" >&2
    exit 1
  fi
  if [[ -n "$(git -C "$directory" status --porcelain --untracked-files=no)" ]]; then
    echo "error: $label checkout has tracked modifications" >&2
    exit 1
  fi
}

check_revision "$COMPARATOR_DIR" "$COMPARATOR_COMMIT" "Comparator"
check_revision "$LEAN4EXPORT_DIR" "$LEAN4EXPORT_COMMIT" "lean4export"

PROJECT_TOOLCHAIN="$(< "$REPO_ROOT/lean-toolchain")"
for tool in "$COMPARATOR_DIR" "$LEAN4EXPORT_DIR"; do
  TOOLCHAIN="$(< "$tool/lean-toolchain")"
  if [[ "$PROJECT_TOOLCHAIN" != "$TOOLCHAIN" ]]; then
    echo "error: $tool uses $TOOLCHAIN, project uses $PROJECT_TOOLCHAIN" >&2
    exit 1
  fi
done

if ! command -v landrun >/dev/null 2>&1; then
  echo "error: a current landrun binary is required on PATH" >&2
  exit 1
fi

if [[ -e "$REPO_ROOT/.lake/build/lib/lean/Solution.olean" ||
      -e "$REPO_ROOT/.lake/build/lib/lean/Solution.ilean" ]]; then
  echo "error: Solution has already been compiled; use a fresh checkout" >&2
  exit 1
fi

# Build the checker from clean, exact source snapshots.  Comparator v4.28.0's
# manifest predates the final lean4export v4.28.0 tag, so update that one lock
# entry in the temporary copy.  This makes the parser library and executable
# come from the same final v4.28.0 commit.
CHECKER_TMP="$(mktemp -d "${TMPDIR:-/tmp}/allender-comparator.XXXXXX")"
cleanup() {
  rm -rf -- "$CHECKER_TMP"
}
trap cleanup EXIT

CHECKER_DIR="$CHECKER_TMP/Comparator"
git clone --quiet --no-local "$COMPARATOR_DIR" "$CHECKER_DIR"
mkdir -p "$CHECKER_DIR/.lake/packages"
git clone --quiet --no-local "$LEAN4EXPORT_DIR" \
  "$CHECKER_DIR/.lake/packages/lean4export"

grep -Fq "$COMPARATOR_MANIFEST_LEAN4EXPORT" \
  "$CHECKER_DIR/lake-manifest.json"
sed -i "s/$COMPARATOR_MANIFEST_LEAN4EXPORT/$LEAN4EXPORT_COMMIT/" \
  "$CHECKER_DIR/lake-manifest.json"
grep -Fq "\"rev\": \"$LEAN4EXPORT_COMMIT\"" \
  "$CHECKER_DIR/lake-manifest.json"

(
  cd "$CHECKER_DIR"
  lake build comparator lean4export
)

test "$(git -C "$CHECKER_DIR/.lake/packages/lean4export" rev-parse HEAD)" = \
  "$LEAN4EXPORT_COMMIT"
export PATH="$CHECKER_DIR/.lake/packages/lean4export/.lake/build/bin:$PATH"

cd "$REPO_ROOT"
lake env "$CHECKER_DIR/.lake/build/bin/comparator" \
  "$REPO_ROOT/comparator/config.json"
