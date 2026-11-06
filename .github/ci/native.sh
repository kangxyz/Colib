#!/usr/bin/env bash
# Aglib's native resource policy, with an explicit quiescence gate before saving.
set -euo pipefail
scope_dir="$RUNNER_TEMP/lean-ci-scopes/$GITHUB_RUN_ID-$GITHUB_RUN_ATTEMPT-$GITHUB_JOB"
stop_unit() {
  local unit=$1 state
  sudo systemctl stop --no-block "$unit" >/dev/null 2>&1 || true
  for _ in {1..100}; do
    state=$(systemctl show -p ActiveState --value "$unit" 2>/dev/null || true)
    case "$state" in inactive|failed) return 0;; esac
    sleep 0.1
  done
  sudo systemctl kill --kill-whom=all --signal=KILL "$unit" >/dev/null 2>&1 || true
  for _ in {1..50}; do
    state=$(systemctl show -p ActiveState --value "$unit" 2>/dev/null || true)
    case "$state" in inactive|failed) return 0;; esac
    sleep 0.1
  done
  echo "::error::Native scope did not stop: $unit" >&2
  return 1
}
if [[ $1 == --stop ]]; then
  for path in "$scope_dir"/*.scope; do
    [[ -f "$path" ]] || continue
    stop_unit "$(cat "$path")"
  done
  exit 0
fi
phase=$1
shift
memory=${CI_NATIVE_MEMORY_MIB:-13824}
threads=${CI_LAKE_THREADS:-1}
workers=${CI_LINT_WORKERS:-2}
for value in "$memory" "$threads" "$workers"; do
  [[ "$value" =~ ^[1-9][0-9]*$ ]] || { echo 'Invalid native resource limit' >&2; exit 2; }
done
available=$(( $(getconf _PHYS_PAGES) * $(getconf PAGE_SIZE) / 1048576 - 2048 ))
(( available > 0 )) || exit 2
if (( memory > available )); then memory=$available; fi
unit="lean-ci-$GITHUB_RUN_ID-$GITHUB_RUN_ATTEMPT-$GITHUB_JOB-$phase-$$.scope"
mkdir -p "$scope_dir"
printf '%s\n' "$unit" > "$scope_dir/$unit"
trap 'stop_unit "$unit" || exit 86' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
printf 'Native scope: %s; memory=%s MiB; threads=%s; lint workers=%s\n' "$phase" "$memory" "$threads" "$workers"
result_code=0
sudo --preserve-env systemd-run --scope --quiet --collect --unit="$unit" \
  --uid="$(id -u)" --gid="$(id -g)" \
  --property="MemoryMax=${memory}M" --property=MemorySwapMax=0 \
  /usr/bin/env "PATH=$PATH" "LEAN_NUM_THREADS=$threads" "CI_LINT_WORKERS=$workers" "$@" \
  || result_code=$?
exit "$result_code"
