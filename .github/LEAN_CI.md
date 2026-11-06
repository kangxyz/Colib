# Lean CI

Colib uses Aglib's current native resource scopes, staging/repair helper, complete
batched declaration linter and runner-local handoff from
[1943d6e](https://github.com/kangxyz/aglib/tree/1943d6eee4976a2d3a01b55e76d6d5890130ee63/.github).
Its dependency transport is specialized to this library's actual dependencies:
Mathlib already has an official cache; Stacks has its own independent checkpoint.

## Main path

The workflow has three jobs: Build, native checks, and publication. Build and Test
use the same compiler and mathematical pins. Build compiles production with
`--rehash`, stages the native outputs and preserves completed work even if a later
check fails. Test verifies this run's outputs before calling the normal local
entry `scripts/check.sh --compiled`. The option skips the production build that
CI has just verified; it keeps tests, all native lint/style/generated-entry checks,
the pinned production axiom audit, metadata tests and Library export.

GitHub-hosted Test downloads only the current Colib and separate Stacks archives.
It obtains Mathlib directly from its official cache. It does not transport,
repack or scan the entire Mathlib working build as a dependency/tools checkpoint.
The Colib Actions cache contains the root build, private checker tools and small
Mathlib/Batteries tool-output directories. The cache boundary regression test
rejects the full Mathlib tree, Stacks tree and mixed native artifact store.

On EC2, Test retains Build's checkout, dependency trees and native store. It checks
runner/repository/revision/run/attempt identity and archive digests. The upstream
same-checkout cold-root native archive check remains in place. A compressed Stacks
checkpoint is reused when its content has not changed.

## Resources and routing

| Setting | GitHub-hosted | EC2 |
|---|---|---|
| Labels | `ubuntu-24.04` | `self-hosted,linux,x64,colib-ec2` |
| Native scope memory request | 13,824 MiB | 57,344 MiB |
| Lake threads / lint workers | 1 / 2 | 8 / 8 |
| Build job / compiler cap | 360 / 345 minutes | 240 / 180 minutes |
| Test job limit | 360 minutes | 90 minutes |

Each native scope clamps memory to physical RAM minus the 2,048 MiB runner
reserve and disables swap. Scope termination is an explicit gate before saving
working outputs. Native commands and cache transport run in the owning scripts
under `ci/`; moving the orchestration out of YAML does not remove native checks.

`COLIB_SELF_HOSTED_ENABLED=false` keeps both workflows and the reusable runner
selector on GitHub-hosted Ubuntu. The manual profile defaults to `hosted`. Once
explicitly enabled, only trusted main pushes/manual EC2 dispatches use EC2.
`COLIB_EC2_SHARED_HOST=true` prepares handoff but cannot enable admission itself.
The main CI and manual probe share the ordered `Colib CI-<ref>` queue.
[EC2 operations](../infra/ci/ec2/README.md) owns the deployed dormant fleet and
pending GitHub App authorization. No EC2 trial has been performed while disabled.

## Cache and check integrity

Stacks is independently packed, restored, cached and published. Its checkpoint
binds compiler, platform, resolved pins and configuration, contains regular
generated files with integrity metadata, and never enters the Colib cache.
Build validates the clean pinned Stacks source. A future upstream provider can
replace its acquisition without changing the Colib cache or native checks.
The first compact run can migrate an existing root checkpoint without importing
the former full dependency/tools checkpoints. See [cache operations](../docs/CACHING.md).

The declaration adapter binds Batteries 7e23602 and the exact source bytes. It runs
all selected checks on declarations defined in Colib modules; an unknown linter
implementation retains native full-lint fallback. Successful lint is never cached.
Text style discovers every Colib/ColibTest file. Cached upstream build warnings are
suppressed while native lint findings and Colib's `warningAsError=true` remain.

A successful main push publishes the verified production archive and independent
Stacks checkpoint. Pages consumes the same run's `colib-site` artifact. The compiler,
Meta tools and upstream dependencies remain pinned; transport checks are not
additional mathematical proof audits or kernel replay.

`actionlint.yaml` declares the custom label. Actionlint 1.7.12 needs the following
narrow exception for the upstream workflow's supported ordered-queue field:

```bash
actionlint -shellcheck= -ignore 'unexpected key "queue" for "concurrency" section'
```
