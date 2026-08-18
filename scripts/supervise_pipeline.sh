#!/usr/bin/env bash
set -u

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
run_dir="${1:?usage: supervise_pipeline.sh RUN_DIR}"
pause_file="$repo/proof_loop/PAUSE"
complete_file="$repo/proof_loop/COMPLETE.external_facts"

cd "$repo"

while true; do
  if [[ -e "$pause_file" ]]; then
    echo "[$(date -u +%FT%TZ)] soft pause present; supervisor exiting"
    exit 0
  fi

  if bash scripts/audit_release.sh >/tmp/oq3-external-release-check.log 2>&1; then
    if [[ ! -e "$complete_file" ]]; then
      printf 'completed %s\n' "$(date -u +%FT%TZ)" >"$complete_file"
    fi
    echo "[$(date -u +%FT%TZ)] all proof obligations are closed"
    exit 0
  fi

  echo "[$(date -u +%FT%TZ)] starting/resuming external-facts runner"
  python3 scripts/run_proof_pipeline.py \
    --section external_facts \
    --iterations 100000 \
    --until-zero-sorries \
    --start-iteration 1 \
    --strategy-first 1 \
    --strategy-every 5 \
    --timeout-seconds 3900 \
    --aristotle-timeout-seconds 86400 \
    --audit-timeout-seconds 2700 \
    --max-sorry-increase-per-merge 16 \
    --submit-aristotle \
    --run-dir "$run_dir"
  rc=$?

  if [[ -e "$pause_file" ]]; then
    echo "[$(date -u +%FT%TZ)] runner stopped on soft pause"
    exit 0
  fi
  if bash scripts/audit_release.sh >/tmp/oq3-external-release-check.log 2>&1; then
    if [[ ! -e "$complete_file" ]]; then
      printf 'completed %s\n' "$(date -u +%FT%TZ)" >"$complete_file"
    fi
    echo "[$(date -u +%FT%TZ)] release audit passed after runner exit"
    exit 0
  fi

  echo "[$(date -u +%FT%TZ)] runner exited rc=$rc; retrying same run in 60 seconds"
  sleep 60
done
