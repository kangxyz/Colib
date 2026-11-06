#!/usr/bin/env bash
set -euo pipefail
repository=$GITHUB_REPOSITORY
revision=$GITHUB_SHA
# A successful native Test job gates this job. Verify the producer identity as well.
tar -xOf colib.tar ./producer.json | jq -e --arg repo "$repository" --arg rev "$revision" \
  'select(.repository == $repo and .revision == $rev)' >/dev/null
publish() {
  local tag=$1 asset=$2 title=$3
  if gh release view "$tag" --repo "$repository" >/dev/null 2>&1; then
    gh release upload "$tag" "$asset" --repo "$repository"
  else
    gh release create "$tag" "$asset" --repo "$repository" --target "$revision" \
      --latest=false --title "$title" --notes 'Native compiled artifacts from successful Colib checks.'
  fi
}
domain=$(tar -xOf colib.tar ./producer.json | jq -er .domain)
asset="lake-native-cache-$domain-$GITHUB_RUN_ID-$GITHUB_RUN_ATTEMPT.tar"
mv colib.tar "$asset"
publish "lean-native-$revision" "$asset" 'Colib compilation cache'
tag=$(python3 - <<'PY'
import json, sys
from pathlib import Path
sys.path.insert(0, '.github/ci-cache')
import checkpoint
root = Path.cwd()
package = next(p for p in json.loads((root / 'lake-manifest.json').read_text())['packages'] if p['name'] == 'Stacks')
print('stacks-checkpoint-' + package['rev'] + '-' + checkpoint.contexts(root)['stacks_context'][:16])
PY
)
asset="stacks-checkpoint-$GITHUB_RUN_ID-$GITHUB_RUN_ATTEMPT.tar.zst"
mv stacks.tar.zst "$asset"
publish "$tag" "$asset" 'Stacks compilation checkpoint'
