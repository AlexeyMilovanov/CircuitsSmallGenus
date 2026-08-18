#!/usr/bin/env bash
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
control="$repo/proof_loop"
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
if [[ ! -s "$active_file" ]]; then
  echo "No ACTIVE_RUN is recorded; use scripts/launch_pipeline.sh first." >&2
  exit 1
fi

run_dir="$(cat "$active_file")"
if [[ ! -d "$run_dir" ]]; then
  echo "Recorded run directory does not exist: $run_dir" >&2
  exit 1
fi

cd "$repo"
python3 -m py_compile scripts/run_proof_pipeline.py
python3 scripts/test_pipeline_safety.py
python3 -m json.tool proof_loop/sections.json >/dev/null
bash scripts/audit.sh

nohup setsid nice -n 5 bash scripts/supervise_pipeline.sh "$run_dir" \
  >>"$run_dir/runner.log" 2>&1 </dev/null &

pid=$!
write_control_file "$pid_file" "$pid"
echo "PID=$pid"
echo "RESUMED_RUN=$run_dir"
