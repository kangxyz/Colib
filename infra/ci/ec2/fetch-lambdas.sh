#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p lambdas
for name in webhook runners runner-binaries-syncer; do
  curl --fail --silent --show-error --location --retry 2 --max-time 180 \
    "https://github.com/github-aws-runners/terraform-aws-github-runner/releases/download/v8.0.0/$name.zip" \
    --output "lambdas/$name.zip"
done
python3 - <<'PY'
import hashlib
from pathlib import Path
for line in Path('lambdas.sha256').read_text().splitlines():
    expected, name = line.split()
    if hashlib.sha256(Path('lambdas', name).read_bytes()).hexdigest() != expected:
        raise SystemExit(f'Lambda archive digest mismatch: {name}')
print('Verified the three pinned v8.0.0 Lambda archives.')
PY
