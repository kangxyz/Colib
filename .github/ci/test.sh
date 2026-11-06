#!/usr/bin/env bash
set -euo pipefail
finish() {
  if bash .github/ci/native.sh --stop; then
    echo 'quiescent=true' >> "$GITHUB_OUTPUT"
  else
    echo 'quiescent=false' >> "$GITHUB_OUTPUT"
    exit 86
  fi
}
trap finish EXIT
read -r -a roots <<< "$BUILD_TARGETS"
test "${#roots[@]}" -gt 0
artifacts="$RUNNER_TEMP/ci-build"
if [[ ${CI_LOCAL_HANDOFF:-false} == true ]]; then artifacts="$PWD/.lake/ci-host-handoff"; fi
printf 'artifacts=%s\n' "$artifacts" >> "$GITHUB_OUTPUT"
printf '%s  %s\n%s  %s\n' "$CI_ROOT_SHA" "$artifacts/colib.tar" "$CI_STACKS_SHA" "$artifacts/stacks.tar.zst" | sha256sum -c -
stack_archive="$RUNNER_TEMP/layered-cache/stacks.tar.zst"
mkdir -p "$(dirname "$stack_archive")"
rm -f "$stack_archive"
ln "$artifacts/stacks.tar.zst" "$stack_archive" || cp "$artifacts/stacks.tar.zst" "$stack_archive"
if [[ ${CI_LOCAL_HANDOFF:-false} == true ]]; then
  bash .github/ci/native.sh verify bash .github/ci-cache/verify-root.sh "$artifacts/colib.tar" "${roots[@]}"
else
  bash .github/ci/native.sh mathlib lake --log-level=error exe cache get
  python3 .github/ci-cache/checkpoint.py supported --root . --materialized
  python3 .github/ci-cache/checkpoint.py restore --root . --layer stacks \
    --input "$artifacts/stacks.tar.zst" --native-cache "$LAKE_CACHE_DIR"
  mkdir -p "$RUNNER_TEMP/current-root"
  tar -xf "$artifacts/colib.tar" -C "$RUNNER_TEMP/current-root"
  lake cache unstage "$RUNNER_TEMP/current-root" --force-overwrite
  find .lake/build .lake/packages -type f -name '*.ltar.hash' ! -writable -delete 2>/dev/null || true
  LAKE_RESTORE_ARTIFACTS=true bash .github/ci/native.sh verify \
    lake --log-level=error build --no-build --rehash "${roots[@]}"
fi
bash .github/ci/native.sh tools lake --log-level=error build \
  batteries/runLinter mathlib/lint-style mathlib/mk_all
result_code=0
bash .github/ci/native.sh checks bash scripts/check.sh --compiled || result_code=$?
bash .github/ci/native.sh --stop
# Keep extra test compilation in the separate Stacks cache, without scanning Mathlib.
if python3 .github/ci-cache/checkpoint.py pack --root . --layer stacks \
    --output "$stack_archive" --native-cache "$LAKE_CACHE_DIR" \
    --github-output "$GITHUB_OUTPUT"; then
  echo 'stacks-saved=true' >> "$GITHUB_OUTPUT"
else
  echo '::warning::Could not save test-only Stacks outputs.'
fi
if [[ ! "$stack_archive" -ef "$artifacts/stacks.tar.zst" ]]; then
  ln -f "$stack_archive" "$artifacts/stacks.tar.zst" || cp "$stack_archive" "$artifacts/stacks.tar.zst"
fi
if (( result_code == 0 )); then echo 'library=true' >> "$GITHUB_OUTPUT"; fi
python3 - "$artifacts/stacks.tar.zst" <<'PY'
import hashlib, os, sys
from pathlib import Path
with Path(sys.argv[1]).open('rb') as stream: value = hashlib.file_digest(stream, 'sha256').hexdigest()
with Path(os.environ['GITHUB_OUTPUT']).open('a') as stream: stream.write('stacks-sha=' + value + '\n')
PY
exit "$result_code"
