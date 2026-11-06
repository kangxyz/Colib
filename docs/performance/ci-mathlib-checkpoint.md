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

Colib depends on Mathlib and Stacks, rather than Aglib's general collection of
project-produced dependencies. The compact path acquires the existing official
Mathlib cache in both hosted jobs and removes full Mathlib dependency/tools
checkpoint production, transport and scanning. Colib and small development tools
use a bounded Actions cache. Stacks retains its independent integrity-checked
checkpoint. EC2 retains the same source/dependency/native-store workspace.

Native resource limits, scope quiescence, staging repair, same-run production
verification, complete native package checks and the pinned axiom audit remain.
The normal local check script is also the CI check entry. A cache boundary test
rejects the full Mathlib tree, Stacks tree and mixed native store in the Colib cache.

The first compact run can import the previous root checkpoint once; it never
imports the former full dependency/tools checkpoints. Initial setup still fetches
pinned source checkouts before restoring generated tool directories. This is
required because a partial `.lake/packages/<name>` directory must not replace a
materialized Git dependency.

## Evidence and remaining measurement

`ci-timings.json` records the complete measured steps from the original runs.
Compact-path job timings will be appended after live native CI validation. No
speedup is claimed before that measurement, and no EC2 machine is started for it.
