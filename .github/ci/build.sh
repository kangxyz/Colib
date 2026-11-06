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
test "$BUILD_TARGETS" = Colib
test "${#roots[@]}" -gt 0
test "$(git rev-parse HEAD)" = "$GITHUB_SHA"
handoff=false
artifacts="$RUNNER_TEMP/ci-build"
if [[ ${CI_REUSE_HOST:-false} == true ]]; then
  test "$(cat /etc/colib-ci-runner-mode)" = colib-ci-runner-v1
  test ! -L .lake
  sudo systemctl restart colib-ci-expiry.timer
  handoff=true
  artifacts="$PWD/.lake/ci-host-handoff"
  export LAKE_CACHE_DIR="$artifacts/native-cache"
fi
mkdir -p "$artifacts"
printf 'local-handoff=%s\nartifacts=%s\n' "$handoff" "$artifacts" >> "$GITHUB_OUTPUT"
# One-time migration of the old root checkpoint; no dependency/tool layer is imported.
if [[ ${CI_MIGRATE_ROOT:-false} == true && -f "$RUNNER_TEMP/layered-cache/root.tar.zst" ]]; then
  python3 .github/ci-cache/checkpoint.py restore --root . --layer root \
    --input "$RUNNER_TEMP/layered-cache/root.tar.zst" --native-cache "$LAKE_CACHE_DIR"
fi
bash .github/ci/native.sh mathlib lake --log-level=error exe cache get
python3 .github/ci-cache/checkpoint.py supported --root . --materialized
stack_archive="$RUNNER_TEMP/layered-cache/stacks.tar.zst"
mkdir -p "$(dirname "$stack_archive")"
if [[ -f "$stack_archive" ]]; then
  python3 .github/ci-cache/checkpoint.py restore --root . --layer stacks \
    --input "$stack_archive" --native-cache "$LAKE_CACHE_DIR"
fi
# Remove only derived read-only LTAR hash sidecars, retaining compiled outputs.
find .lake/build .lake/packages -type f -name '*.ltar.hash' ! -writable -delete 2>/dev/null || true
compiler_minutes=${CI_COMPILER_MINUTES:-0}
if [[ "$compiler_minutes" == 0 ]]; then compiler_minutes=$(( ${CI_BUILD_JOB_MINUTES:-360} - 15 )); fi
[[ "$compiler_minutes" =~ ^[1-9][0-9]*$ ]] || exit 2
result_code=0
timeout --signal=INT --kill-after=30s "${compiler_minutes}m" \
  bash .github/ci/native.sh build lake --log-level=error build --rehash "${roots[@]}" \
    -o "$RUNNER_TEMP/outputs.jsonl" || result_code=$?
bash .github/ci/native.sh --stop
# The scope has stopped. Retain completed Stacks work even after a compiler failure.
if python3 .github/ci-cache/checkpoint.py pack --root . --layer stacks \
    --output "$stack_archive" --native-cache "$LAKE_CACHE_DIR" \
    --metadata "$PWD/.lake/ci-cache/stacks.json" --github-output "$GITHUB_OUTPUT"; then
  echo 'stacks-saved=true' >> "$GITHUB_OUTPUT"
else
  echo '::warning::Could not save the Stacks checkpoint.'
fi
if [[ -f "$stack_archive" ]]; then
  if [[ ! "$stack_archive" -ef "$artifacts/stacks.tar.zst" ]]; then
    ln -f "$stack_archive" "$artifacts/stacks.tar.zst" || cp "$stack_archive" "$artifacts/stacks.tar.zst"
  fi
fi
if (( result_code != 0 )); then exit "$result_code"; fi
arguments=()
for root in "${roots[@]}"; do arguments+=(--build-target "$root"); done
bash .github/ci/native.sh stage python3 .github/ci-cache/stage.py prepare --root . \
  --mapping "$RUNNER_TEMP/outputs.jsonl" --staging "$RUNNER_TEMP/cache-staging" \
  --native-cache "$LAKE_CACHE_DIR" "${arguments[@]}" --report "$RUNNER_TEMP/stage-report.json"
bash .github/ci/native.sh --stop
python3 - <<'PY'
import hashlib, json, os, subprocess
from pathlib import Path
root = Path(os.environ['RUNNER_TEMP']) / 'cache-staging'
producer = {'repository': os.environ['GITHUB_REPOSITORY'], 'revision': os.environ['GITHUB_SHA'],
            'package': 'Colib', 'compiler': subprocess.check_output(['lean', '--version'], text=True).strip(),
            'domain': os.environ['RUNNER_OS'] + '-' + os.environ['RUNNER_ARCH'] + '-' + hashlib.sha256(Path('lean-toolchain').read_bytes()).hexdigest()[:16]}
(root / 'producer.json').write_text(json.dumps(producer) + '\n')
PY
tar -cf "$artifacts/colib.tar" -C "$RUNNER_TEMP/cache-staging" .
test -f "$artifacts/stacks.tar.zst"
python3 - "$artifacts" "$handoff" <<'PY'
import hashlib, json, os
from pathlib import Path
import sys
root = Path(sys.argv[1])
def digest(path):
    with path.open('rb') as stream: return hashlib.file_digest(stream, 'sha256').hexdigest()
with Path(os.environ['GITHUB_OUTPUT']).open('a') as stream:
    stream.write('root-sha=' + digest(root / 'colib.tar') + '\n')
    stream.write('stacks-sha=' + digest(root / 'stacks.tar.zst') + '\n')
if sys.argv[2] == 'true':
    path = Path('.lake/ci-cache/stacks.json')
    data = json.loads(path.read_text()); data['archive_sha256'] = digest(root / 'stacks.tar.zst')
    path.write_text(json.dumps(data) + '\n')
PY
if "$handoff"; then
  printf '%s\n' "$GITHUB_REPOSITORY" "$GITHUB_SHA" "$GITHUB_RUN_ID" "$GITHUB_RUN_ATTEMPT" "$RUNNER_NAME" > "$artifacts/identity"
  dirname "$(command -v lake)" > "$artifacts/lean-bin"
fi
