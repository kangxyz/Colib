# Performance

For slow CI, compare named step durations before changing compiler limits. Record
compiler, manifest, workflow source and whether the run reused a compatible cache.
Separate production compilation, acquisition, hashing/packing, transfer and checks.
A new cache schema's first run is not a steady-state measurement. Code changes also
prevent treating whole-run differences as a controlled compiler benchmark.

Colib's ordinary dependencies are supplied by Mathlib's official cache. Do not
repack the entire Mathlib build into a project dependency or tools checkpoint.
Exclude official Mathlib production outputs from project checkpoints, retain small
checker outputs, preserve the independent Stacks boundary,
and retain native input verification and axiom/lint predicates.

The [CI checkpoint case](performance/ci-mathlib-checkpoint.md) records the regression,
original measurements, exact runs, and the compact-path validation. Its
[step timings](performance/ci-timings.json) preserve the complete measured phases.

When an elaboration timeout is attributed to a nested `obtain` in a large
proposition, profile the command and try `Exists.elim` with explicit conjunction
projections at the same heartbeat budget. See the
[finite mixed generation case](performance/finite-mixed-exists-elim.md).

If profiling points to `CoeT` while elaborating an equality of K-group
homomorphisms, provide the equality's native homomorphism type explicitly.
See the [fine K-product case](performance/fine-k-product-equality-type.md).
