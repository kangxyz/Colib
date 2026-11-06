# Full Mathlib checkpoints in Colib CI

## Conditions and observed regression

The first complete Aglib-style adaptation was Colib `e29879e`, based on Aglib
`1943d6e`, with Lean 4.34.0-rc2, Mathlib `16edf57`, and Stacks `f8e70c5`.
It ran all checks successfully on hosted Ubuntu with 13,824 MiB native scopes,
one Lake thread and two declaration-lint workers. The linter actually reported
`backend=batched`, 7,045 Colib declarations, 15 linters, and two workers.

| Run | Build | Test | Source/measurement limit |
|---|---:|---:|---|
| [42153596620](https://github.com/kangxyz/colib/actions/runs/42153596620) | 492 s | 276 s | Last successful portable workflow, source `439de50` |
| [42159181569](https://github.com/kangxyz/colib/actions/runs/42159181569) | 507 s | 449 s | First full layered run, source `e29879e` |
| [42159959033](https://github.com/kangxyz/colib/actions/runs/42159959033) | 525 s | 580 s | Next main run, source `2bccd32`; additional mathematics prevents a controlled compile-time comparison |

The first layered dependency archive contained 132,983 generated files and
2,234,762,974 compressed bytes. Dependency packing cost 140 seconds. Test spent
71 seconds downloading it, 97 seconds restoring it, and 72 seconds scanning/packing
the tools layer. Stacks was a separate 5,535-file, 115,325,096-byte checkpoint.
The whole-run observations do not establish a universal speed ratio, but the
step timings directly identify substantial dependency-transport work.

## Repair

Retain the verified Aglib workflow and independent functional steps. Compiler
progress and success logs stay visible. No checks are grouped to hide their status.

The repair excludes official Mathlib production outputs from dependency and tools
checkpoint scopes, and acquires the pinned official cache in both hosted jobs.
Only Mathlib's small checker-tool output directories enter the tools checkpoint.
The dependency/tools context binds the changed scope policy; root and Stacks
contexts remain compatible. Stacks remains independently stored.

Resource limits, scope quiescence, staging repair, same-run production verification,
complete package checks and the pinned axiom audit remain. The same-host path
retains Build's Mathlib tree and skips the cross-runner acquisition/transport.

The earlier combined-check wrapper change was reverted. It obscured stage status
without reducing verification work. A regression test now checks the substantive
boundary: the dependency archive contains no Mathlib production outputs, while the
tools archive retains the required checker executable.

## Live validation

`ci-timings.json` records the original observations. Repaired-path timings will be
appended after the independent native stages complete. No EC2 trial is performed
while its admission gate remains false.

## Idle-build diagnosis

Run 42167622185 performed no Lean compilation during its 187-second production
Build step (05:20:15–05:23:22 UTC). Thirteen process samples recorded zero Lean
frontends, about 0.99 native CPU cores on average, and under 1 GiB aggregate native
memory. The log contains no compiled-module action and ends with 5,702 Lake jobs.
This separates Lake graph/hash/cache work from theorem elaboration.

Remove Build's forced `--rehash`; retain the native `--no-build --rehash` validity
check in Test. The production build remains incremental. The pinned Lake
`BuildConfig.showProgress` and `reportResult` control progress/completion separately
from per-job log severity, so `--log-level=error` suppresses replayed upstream logs
without replacing the native completion result. Explicit builtin lint continues
to target `Colib`, using its defining-module filter.
