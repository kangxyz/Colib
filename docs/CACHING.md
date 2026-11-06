# Compilation caches

The [Lean CI guide](../.github/LEAN_CI.md) owns the three-job execution flow.
The cache design follows the actual dependency boundary: Mathlib has its official
cache and Stacks is stored independently.

| Object | Contents |
|---|---|
| Colib Actions cache | Colib build/configuration, private lint/auditor builds and small checker-tool output directories |
| Mathlib upstream cache | Mathlib and its ordinary dependency compilation, acquired through the pinned native cache tool |
| Independent Stacks checkpoint | Only the pinned Stacks generated build/configuration |
| Native publication archive | Verified Colib production outputs with producer identity |

The Colib cache excludes the complete Mathlib build tree, the entire Stacks tree,
and the mixed native artifact store. Its restore prefixes bind compiler, platform,
manifest/configuration and the checker implementation. Changed proof sources retain
compatible incremental output; native `--rehash` decides applicability.

GitHub-hosted Build and Test acquire the official Mathlib cache directly. They do
not repack a multi-gigabyte Mathlib checkpoint for the next job. Test must consume
this Build's Colib native archive and independent Stacks archive, verify the
producer/digests, and pass native `--no-build --rehash` before package checks.
EC2 retains the same working trees/native store across both jobs and validates the
handoff identity instead of transferring them. Scope quiescence gates cache saves.

Stacks uses its own immutable context/content key and versioned `.tar.zst` integrity
manifest. A matching compressed checkpoint is reused instead of recompressed.
Test-only Stacks compilation is saved in the same separate cache. Successful main
runs publish `stacks-checkpoint-<Stacks revision>-<context>` releases separately
from `lean-native-<Colib revision>`.

To import a Stacks checkpoint, materialize the pinned dependency sources first:

```bash
python3 .github/ci-cache/checkpoint.py restore --root . --layer stacks \
  --input /path/to/stacks-checkpoint.tar.zst
```

A native build/verification still checks applicability. A future upstream Stacks
provider only needs to replace this acquisition boundary. The existing
`scripts/stacks_cache.py pack/restore` retains its initial standalone `.tar.gz`
format for earlier consumers/releases; it is separate from checkpoint archives.

The former root checkpoint can seed the first compact run. Former full dependency
and tools checkpoints are no longer part of the normal pipeline. Their migration
regression and measured costs are recorded under [performance](PERFORMANCE.md).
