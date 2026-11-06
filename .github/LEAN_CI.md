# Lean CI

Colib adapts the complete current main CI from
[kangxyz/aglib at 1943d6eee4976a2d3a01b55e76d6d5890130ee63](https://github.com/kangxyz/aglib/tree/1943d6eee4976a2d3a01b55e76d6d5890130ee63/.github),
including the resource scopes, layered checkpoints, native staging validation,
parallel declaration linter, and runner-local Build-to-Test handoff. This replaces
Colib's original portable workflow. The code and operating limits are shared by
both runner profiles; the mathematical dependency pins are unchanged.

## Profiles and routing

| Setting | GitHub-hosted | EC2 |
|---|---|---|
| Labels | `ubuntu-24.04` | `self-hosted,linux,x64,colib-ec2` |
| Native scope memory request | 13,824 MiB | 57,344 MiB |
| Lake threads / declaration lint workers | 1 / 2 | 8 / 8 |
| Build job / compiler cap | 360 minutes / remaining safe window | 240 / 180 minutes |
| Test job limit | 360 minutes | 90 minutes |
| Build-to-Test transfer | Same-run dependency and root archives | Same checkout and native store |

The native scope clamps its request to physical RAM minus a 2,048 MiB runner
reserve and disables swap. Compiler and staging scopes stop before checkpoints
are read. A job deadline reserves time for staging and saving completed work after
compiler failure. Resource samples are retained as workflow artifacts.

`COLIB_SELF_HOSTED_ENABLED=false` keeps every ordinary run on GitHub-hosted
runners. The manual profile defaults to `hosted`. Once explicitly enabled, only
main-branch pushes and main-branch manual `ec2` dispatches use EC2. PRs and other
revisions use GitHub-hosted runners. `COLIB_EC2_SHARED_HOST=true` prepares the
optimized EC2 handoff; it cannot enable EC2 without the independent admission gate.
The main workflow and manual EC2 probe share `Colib CI-<ref>` with ordered queuing.

The [EC2 operating guide](../infra/ci/ec2/README.md) owns the deployed fleet,
webhook, GitHub App authorization and future activation. No EC2 trial is performed
while disabled. The root-owned marker is `colib-ci-runner-v1` in
`/etc/colib-ci-runner-mode`; Build restarts `colib-ci-expiry.timer`.

## Checkpoints and transport

The adapted schema has four independently stored generated-output layers:

| Layer | Contents |
|---|---|
| Root | Colib build/configuration outputs, including in-package tests |
| Dependencies | Generated outputs for resolved dependencies other than Stacks |
| Stacks | Only `.lake/packages/Stacks/.lake/build` and `.lake/config` |
| Tools | Private lint/auditor builds and non-Stacks dependency changes since Build |

The context binds compiler, platform, resolved pins and package configuration.
Tools also bind the lint adapter and auditor pin. Archives carry file integrity
and coverage manifests; immutable cache generations are derived from content.
Source checkouts, Git data and the mixed native artifact store are not checkpointed.
The packer reuses a validated compressed archive when content has not changed.
An earlier compatible `colib-v2` cache and the earlier separate Stacks cache can
seed the first run of this schema. They are not the normal save path.

Build overlays optional checkpoints and uses native `lake build --rehash` for
production roots. Available completed work is checkpointed after a compiler
failure. On GitHub-hosted runners, Test must overlay this Build's complete
`build-dependencies`, separate `build-stacks`, and native `cache-staging`, even
when optional caches hit. Native `--no-build --rehash` verifies the current inputs
before checks. Stacks is excluded from the dependency and tools layers, including
test-only dependency compilation.

On EC2, Build seals runner, repository, revision, run and attempt identity in the
preserved checkout. Test checks that identity, `HEAD` and archive digest. It uses
the same native store and dependency trees. The upstream `verify-root.sh` native
archive check remains in place. The compressed Stacks checkpoint also survives
per-job temporary-directory cleanup and is reused if Test adds no Stacks outputs.

Successful main pushes publish Colib's native archive and the independently named
`stacks-checkpoint-<Stacks revision>-<context>` release. A later upstream Stacks
cache provider can replace Stacks acquisition while retaining this storage
boundary and the native applicability checks. See [cache operations](../docs/CACHING.md).

## Native checks and Library

Test prepares the native Mathlib/Batteries tools and runs generated-entry checks,
all Colib/ColibTest text-style inputs, in-package tests, full declaration lint,
and the pinned production axiom auditor. The declaration adapter batches the same
selected upstream checks over declarations defined in Colib modules. It retains
native fallback for unknown linter implementations; successful lint results are
never cached. Local `scripts/check.sh` uses the same adapter.

Both builtin lint replay and the declaration driver select by defining module,
not declaration namespace. Stacks is outside the report scope. Lake's cached
build warning logs are suppressed with `--log-level=error`; native lint reports
remain visible and Colib retains `warningAsError=true`.

The structured Library export and website are additional Colib checks. The final
Verification table requires every outcome, including that export, to succeed.
Pages consumes the resulting `colib-site` artifact from a trusted main push.

## Pin-specific adaptations

The upstream implementation targets Lean 4.34.1. Colib also admits its fixed
4.34.0-rc2 toolchain and exact Mathlib/ProofWidgets configuration byte hashes.
The lint adapter binds the exact Batteries 7e23602 sources and matching compiler.
Unknown layouts fail before compilation instead of silently choosing the old
combined-cache path. Aglib's historical, repository-specific `first-ci-cache`
promotion seed is rejected; its recorded producer and cache do not belong to Colib.

Cache integrity tests live in `ci-cache/test_*.py`. `actionlint.yaml` records the
custom runner label. Actionlint 1.7.12 needs a narrow ignore for its unrecognized
`concurrency.queue` field, which is present in the working upstream workflow:

```bash
actionlint -shellcheck= -ignore 'unexpected key "queue" for "concurrency" section'
python3 -m unittest discover -s .github/ci-cache -p 'test_*.py'
```
