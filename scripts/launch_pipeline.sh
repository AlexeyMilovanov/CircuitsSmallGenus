#!/usr/bin/env bash
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
runs_root="${ALLENDER_OQ3_RUNS_ROOT:-/home/lesha/allender-oq3-lean-runs}"
control="$repo/proof_loop"
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
run_dir="$runs_root/${stamp}-external-facts-loop"
pid_file="$control/RUNNER_PID"
active_file="$control/ACTIVE_RUN"

for control_file in "$pid_file" "$active_file"; do
  if [[ -L "$control_file" || (-e "$control_file" && ! -f "$control_file") ]]; then
    echo "Unsafe control path: $control_file" >&2
    exit 1
  fi
done

write_control_file() {
  local destination="$1" value="$2" temporary
  temporary="$(mktemp "$control/.control.XXXXXX")"
  printf '%s\n' "$value" >"$temporary"
  chmod 0600 "$temporary"
  mv -fT -- "$temporary" "$destination"
}

if [[ -s "$pid_file" ]] && kill -0 "$(cat "$pid_file")" 2>/dev/null; then
  echo "OQ3 proof runner is already active as PID $(cat "$pid_file")" >&2
  exit 1
fi

mkdir -p "$run_dir" "$control"
cd "$repo"

python3 -m py_compile scripts/run_proof_pipeline.py
python3 scripts/test_pipeline_safety.py
python3 -m json.tool proof_loop/sections.json >/dev/null
bash scripts/audit.sh

nohup setsid nice -n 5 bash scripts/supervise_pipeline.sh "$run_dir" \
  >"$run_dir/runner.log" 2>&1 </dev/null &

pid=$!
write_control_file "$pid_file" "$pid"
write_control_file "$active_file" "$run_dir"
echo "PID=$pid"
echo "RUN=$run_dir"
