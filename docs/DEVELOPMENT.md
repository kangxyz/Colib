# Development and CI

Use the committed toolchain and manifest. The initial dependency basis matches Stacks commit
f8e70c5dd04bfabcb423d5e325461f527c85a5d6 and Mathlib commit
16edf57de7933555826307a3d81b4391a3657a09. Lean is 4.34.0-rc2.

During proof work build the changed leaf and its required dependencies. Existing completed
artifacts survive subsequent repairs. Run the final native checks through scripts/check.sh.

The final check covers production compilation, in-package tests, declaration lint,
Mathlib text style, the generated production entry, the pinned upstream production axiom
auditor, catalog metadata tests and a catalog export from the built environment.
The approved axioms are propext, Classical.choice and Quot.sound.

CI adapts Aglib's portable Build, Test and Publish-cache workflow from commit
2c34f185fa859e862661f939cd216b07bcccfb26. Build saves partial native compilation independently
of later checks. Test consumes the matching build artifacts and runs native checks.
Publish cache runs after successful default-branch checks and creates a release asset in
this repository. GitHub repository visibility governs these cache releases and catalog
artifacts. The hosted runner uses the standard repository Actions environment.

The first pilot uses a small selected Stacks import closure. scripts/cache.sh retrieves the
corresponding Mathlib roots. Stacks artifacts are produced by the native build and retained
in the workflow caches. Toolchain or mathematical pin changes form one intentional
compatibility task.

The native auditor is a development executable pinned to
leanprover-community/axiom-audit commit 46024e005996495c65ef609368e11ab39c4222e3.
Its toolchain is selected to match the library. It is outside the production dependency graph.

Maintained text and names use English. Preserve exact source references and contributor
notices. New public mathematical endpoints enter the owning source family and catalog
together, with precise hypotheses and map normalizations.

## Encyclopedia publication

The native Test job generates both the Markdown catalog and the static site from the same
declaration export. The Pages workflow consumes the successful main-branch native run's
`colib-site` artifact. A manual dispatch selects the latest successful main-branch run.
The deployed address is https://kangxyz.github.io/colib/.

[Independent Stacks caching](CACHING.md) owns the separate dependency-artifact boundary.
