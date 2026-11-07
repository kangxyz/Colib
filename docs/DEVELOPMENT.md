# Development and CI

Use the committed toolchain and manifest. Colib uses Lean 4.35.0 and Mathlib
4.35.0 at commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Stacks commit
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7` pins the same compiler, Mathlib release, and
transitive dependencies.

During proof work build the changed leaf and its required dependencies. Existing completed
artifacts survive subsequent repairs. Run the final native checks through scripts/check.sh.

The final check covers production compilation, in-package tests, full declaration lint,
Mathlib text style, the generated production entry, the pinned upstream production axiom
auditor, catalog metadata tests and a catalog export from the built environment.
The approved axioms are propext, Classical.choice and Quot.sound.

CI adapts the complete optimized Aglib workflow and tools from commit
1943d6eee4976a2d3a01b55e76d6d5890130ee63. It uses resource-bounded native scopes,
separate root/dependency/Stacks/tools checkpoints, complete same-run overlays on
GitHub-hosted runners and identity-checked same-host handoff on EC2. Both profiles
run the native package checks. The current self-hosted admission gate is false.
The [Lean CI guide](../.github/LEAN_CI.md) owns routing, resources, staging,
publication and the exact adaptations to Colib's 4.35.0 dependency basis.

The native auditor is a development executable pinned to
leanprover-community/axiom-audit commit 46024e005996495c65ef609368e11ab39c4222e3.
Its toolchain is selected to match the library. It is outside the production dependency graph.

Maintained text and names use English. Preserve exact source references and contributor
notices. New public mathematical endpoints enter the owning source family and catalog
together, with precise hypotheses and map normalizations.

## Library publication

The native Test job generates both the Markdown catalog and the static site from the same
declaration export. The Pages workflow consumes the successful main-branch native run's
`colib-site` artifact. A manual dispatch selects the latest successful main-branch run.
The deployed address is https://kangxyz.github.io/colib/.

[Independent Stacks caching](CACHING.md) owns the separate dependency-artifact boundary.

## Library checks

`python3 scripts/catalog.py check` validates chapters, sections and permanent mathematical items. Defining modules and their
imports come from the native Lean export. The native exporter reads compiled `@[colib_tag]`, `@[stacks]`
and `@[colib_ref]` metadata and rejects unresolved bindings or unknown bibliographic keys.
`python3 scripts/catalog.py build` produces build/library/library.json, declarations.json
and a chapter-ordered Markdown rendering. Original build/catalog output paths remain available
for consumers of the first release.

The website generator consumes that exact native export and checks its source hashes. It
writes independent contents, chapter, section, permanent-item, bibliography and search pages.
Search loads its compact index on the search page. Ordinary reading pages contain their text
and links in static HTML.

## Lint scope

`bash .github/lint/run.sh Colib` uses the optimized full declaration adapter; the
ordinary `lake --no-build --log-level=error lint Colib` command remains available.
Both retain the builtin lint report and
Batteries' declaration linters. Both select declarations or saved diagnostics by their
**defining module** under `Colib`, including Colib declarations in native namespaces such
as `CategoryTheory`. Imported Mathlib and Stacks declarations are outside that scope.
The [pinned Lean builtin collector](https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/CLI/BuiltinLint.lean)
filters `LintEntry` defining modules by the `Colib` prefix;
it does not use the full imported environment as its report scope.

Lake also replays cached **build logs** while preparing build targets, tests and tools.
Those logs can contain Stacks linter warnings even when the lint report itself is limited
to Colib. The check script and CI use `--log-level=error` for these builds to suppress
that duplicate warning output. Build errors still fail, Colib keeps `warningAsError = true`,
and native lint findings remain visible. Required dependencies still load and compile.

`python3 scripts/lint_style.py` passes source-only import hubs to Mathlib's unchanged
`lint-style` executable. It enumerates every `Colib` and `ColibTest` source file,
including leaf tests and the production root, without traversing `.lake/packages`.
New tests need no handwritten CI module list. Prepare the executable with
`lake build mathlib/lint-style` when running this command separately.

## Self-hosted CI

The [EC2 operating guide](../infra/ci/ec2/README.md) owns the Colib-specific infrastructure,
its disabled deployment, and future activation. `COLIB_SELF_HOSTED_ENABLED=false` keeps
normal CI on GitHub-hosted runners. The infrastructure independently disables scale-up.
