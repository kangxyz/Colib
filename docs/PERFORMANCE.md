# Performance

For slow CI, compare named step durations before changing compiler limits. Record
compiler, manifest, workflow source and whether the run reused a compatible cache.
Separate production compilation, acquisition, hashing/packing, transfer and checks.
A new cache schema's first run is not a steady-state measurement. Code changes also
prevent treating whole-run differences as a controlled compiler benchmark.

Colib's ordinary dependencies are supplied by Mathlib's official cache. Do not
repack the entire Mathlib build into a project dependency or tools checkpoint.
Keep the Colib/tool outputs compact, preserve the independent Stacks boundary,
and retain native input verification and axiom/lint predicates.

The [CI checkpoint case](performance/ci-mathlib-checkpoint.md) records the regression,
original measurements, exact runs, and the compact-path validation. Its
[step timings](performance/ci-timings.json) preserve the complete measured phases.
