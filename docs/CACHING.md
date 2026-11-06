# Compilation caches

The [current Lean CI](../.github/LEAN_CI.md) uses Aglib's optimized checkpoint and
native staging flow, adapted to Colib's fixed compiler/dependencies and an
independent Stacks layer.

## Storage boundaries

| Object | Stored content |
|---|---|
| Root checkpoint | `.lake/build` and `.lake/config` for Colib |
| Dependency checkpoint | Working build/configuration outputs of resolved non-Stacks dependencies |
| Stacks checkpoint | Working build/configuration outputs of the pinned Stacks package only |
| Tools checkpoint | Lint/auditor generated outputs and changed non-Stacks dependency outputs |
| Native publication archive | The verified production stage, with producer repository/revision identity |

Each layer has its own immutable Actions cache key and content generation. Keys
bind toolchain, platform, resolved manifest and configuration; tool keys also bind
tool source/pins. Checkpoint archives do not contain dependency sources or Git
metadata. A mixed `LAKE_CACHE_DIR` content store is never saved as a working
checkpoint. Native archive validity is checked by Lake against the actual inputs.

The Stacks checkpoint is excluded from both dependencies and tools. Build saves
it separately, including useful partial compilation. Cross-runner Test receives
this run's `build-stacks` independently of `build-dependencies`, then saves any
additional Stacks outputs in the same independent layer. The Stacks
acquisition boundary can later fetch an upstream Stacks cache before native
compilation without changing Colib's root/tool/dependency caches.

## Reuse and transfer

Production sources do not invalidate compatible checkpoint prefixes. Lake's
native `--rehash` decides applicability. Root and tools restores prefer a
compatible ref. Dependency and Stacks generations use their content identity.
The packer checks integrity and coverage, preserves regular generated files,
and reuses an already validated compressed archive when its content is unchanged.

GitHub-hosted Test must consume the current Build's complete dependency, Stacks
and root archive overlays, even if optional checkpoint caches hit. EC2 handoff
retains the working trees/native store and verifies its runner/repository/run
identity. Both paths verify production outputs before preparing checker tools.
Checkpoint integrity is a transport check, not a new mathematical proof audit.

The earlier `colib-v2` environment cache contains explicitly selected root and
non-Stacks package paths. The earlier `stacks-<context>` cache contains only the
Stacks package. These independent caches can seed the first layered run; the
optimized workflow does not normally save those source-tree caches.

## Publication and manual exports

After all checks pass, main pushes publish the normal `lean-native-<Colib revision>`
production archive and a separate `stacks-checkpoint-<Stacks revision>-<context>`
release. Its `.tar.zst` asset uses the versioned checkpoint manifest and can be
restored through:

```bash
python3 .github/ci-cache/checkpoint.py restore --root . --layer stacks \
  --input /path/to/stacks-checkpoint.tar.zst
```

Materialize the pinned dependency sources first. A later native build/verification
checks applicability; a matching archive alone is not a successful compilation.

`scripts/stacks_cache.py pack/restore` retains the initial standalone `.tar.gz`
format for existing consumers and earlier `stacks-native` releases. It verifies
exact Stacks source revision, dependency/compiler context and artifact digests.
Those archives are separate from the new checkpoint format. The script's `layout`
command also owns the independent migration-seed paths and identity.
