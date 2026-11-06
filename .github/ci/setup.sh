#!/usr/bin/env bash
set -euo pipefail
python3 .github/ci/cache.py "$GITHUB_OUTPUT"
if [[ ${CI_LOCAL_HANDOFF:-false} == true ]]; then
  handoff="$PWD/.lake/ci-host-handoff"
  expected=$(printf '%s\n' "$GITHUB_REPOSITORY" "$GITHUB_SHA" "$GITHUB_RUN_ID" "$GITHUB_RUN_ATTEMPT" "$RUNNER_NAME")
  test "$(cat "$handoff/identity")" = "$expected"
  test "$(git rev-parse HEAD)" = "$GITHUB_SHA"
  cat "$handoff/lean-bin" >> "$GITHUB_PATH"
  printf 'LAKE_CACHE_DIR=%s\n' "$handoff/native-cache" >> "$GITHUB_ENV"
else
  installer="$RUNNER_TEMP/elan-init.sh"
  curl --fail --silent --show-error --location --retry 2 --retry-all-errors \
    --connect-timeout 20 --max-time 120 https://elan.lean-lang.org/elan-init.sh --output "$installer"
  bash "$installer" -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
  echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
  for attempt in 1 2 3; do
    if elan which lake >/dev/null; then break; fi
    test "$attempt" -lt 3 || exit 1
    sleep "$((attempt * 5))"
  done
  lean --version
  # Materialize Git sources before restoring selected generated tool directories.
  bash .github/ci/native.sh sources lake --log-level=error env true
  echo "LAKE_CACHE_DIR=$RUNNER_TEMP/lake-native-cache" >> "$GITHUB_ENV"
fi
