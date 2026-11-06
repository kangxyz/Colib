# Quillen migration inventory

This directory records the historical source denominator for the Quillen migration.
It is **not** evidence that these results have been migrated, that their types match
Colib, or that the historical source compiles. Every generated module row starts
`untriaged`; no mathematical result is closed by this inventory.

## Pinned source and provenance

- [Quillen c561118b](https://github.com/kangxyz/quillen-k-theory/tree/c561118b7795eb9780be9ed391c3251d6a4d0afd)

Quillen declares Apache-2.0. Its original `LICENSE` file hash, source URL, full
revision, and Lean toolchain are recorded in `summary.json`. Each tracked Quillen
blob has its SHA-256 in `files.jsonl`. Preserve original authorship and license
notices when migrating source. No mathematical citation or literature
correspondence is inferred from file names.

The historical external Aglib repository is excluded: there are no Aglib-source
file or module rows, and regeneration never reads that repository. Quillen's own
`Quillen/Aglib/` modules remain in scope. The source manifest in `summary.json`
retains its historical Aglib pin and URL as provenance only; Quillen's imports of
`Aglib.*` are recorded as unverified external dependencies. These references are
not Colib dependencies, an Aglib census, or permission to revive its old model.

## Reproduce

Run from the Colib repository root with Python 3.10+ and Git. The Quillen repository
must contain the full commit above, including its blobs. Checkout state does
not matter: the script reads Git objects and ignores uncommitted working files.
For a fresh checkout, clone Quillen at the URL above and fetch the recorded
revision if it is not already present. No Aglib checkout is needed.

```sh
python3 scripts/quillen_inventory.py \
  --quillen /path/to/quillen-k-theory \
  --package mathlib=/path/to/mathlib4 \
  --package batteries=/path/to/batteries
python3 -m unittest discover -s scripts -p 'test_quillen_inventory.py'
```

The optional `--package NAME=REPO` arguments check imported module file existence
at **Quillen's source manifest pins**, not the package checkout HEAD or Colib's
different destination pins. Omit them only when those Git objects are unavailable;
the resulting summary explicitly counts unverified external imports. A missing
pinned Git object fails the command rather than silently substituting another
revision. Supplying `--package Aglib=...` is rejected before any repository is
read; the old `--aglib` option no longer exists. In a partial clone Git may fetch
missing objects through its normal configured remote.

Outputs are sorted, omit timestamps and machine-local paths, and are byte-for-byte
reproducible for the same revisions and supplied package repositories. Regeneration
replaces generated inventories. Keep subsequent assignments, mathematical mappings,
and acceptance evidence in separate maintained records rather than editing these
baseline rows and losing the edits on regeneration.

## Artifacts and exact counting rules

- `files.jsonl`: every tracked blob in the Quillen repository, exactly once
  per path. Categories are disjoint: production `.lean` below the
  library root, the root entry itself, in-package test `.lean`, downstream fixtures,
  tooling, documentation, and other files. Non-Lean files are retained too.
- `modules.jsonl`: every Quillen production module and the `Quillen.lean` entry.
  Imports retain source line numbers; each row includes its hash, immediate consumers, SCC, dependency
  tier, transitive source-module import count and pending migration fields.
- `external-imports.jsonl`: import edges leaving the Quillen source graph,
  with source-package existence evidence when supplied. This is not a recursive
  census of external dependencies, nor a claim of successful elaboration.
  Historical `Aglib.*` references always remain unverified.
- `unresolved-imports.jsonl`: edges to missing Quillen modules. An empty file means
  none are missing within this lexical Quillen graph; it says nothing about
  whether external Aglib modules exist.
- `summary.json`: schema version 2 counts, historical source-manifest packages, pins
  and explicit evidence boundaries. The graph now excludes external Aglib nodes,
  so SCC indices, consumers, dependency tiers and transitive counts are recomputed.

The 5,833 reported production files are 5,832 files below `Quillen/` and the
`Quillen.lean` entry. The 836 local Aglib candidates are precisely the `.lean`
files below `Quillen/Aglib/`; adding `Quillen/Aglib.lean` yields 837 prefix-matching
modules. Family counts include each family's aggregate `.lean` file; for example,
`Quillen/Algebra.lean` adds one to the count below `Quillen/Algebra/`.
Generated aggregate imports remain in the graph because they affect reachability.
The `generated_import_aggregator` flag recognizes the source generator's explicit
marker; it is not a universal claim that all generated code carries that marker.

Transitive source imports are reconstructible by following each row's `imports`
within the module ledger. Their counts exclude the starting module. The dependency
tier is the longest source dependency path in the SCC condensation, with leaves at
zero; it ignores all external package internals (including Aglib) and is not a
mathematical work estimate.
The sorted SCC index is stable for this frozen graph, not a permanent Library ID.
Tests and downstream fixtures are counted without executing them. Their imports
are not added as production seeds; they require a separate interface review.

## Evidence boundaries and remaining gates

Import scanning handles nested comments, quoted strings, import visibility/meta
prefixes, multiline import lists, and `import all`. It is a lexical scanner, not a
Lean parser or compiled environment export. Tests cover these distinctions and
Git-object isolation from dirty working files. Unusual future source syntax must
be reviewed rather than assumed supported.

**No complete declaration/result ledger exists yet.** A compiled source environment
census is still needed to enumerate declarations, generated names, instances,
private helpers, aliases and reexports, and obtain exact types and universes.
Creating a text-based list of theorem keywords would not discharge that gate.
The historical Lean 4.34.1 source build is distinct from Colib's 4.34.0-rc2 build.
The module graph alone also does not prove transitive axiom acceptability.

For each future migration slice, record exact source declarations and types,
canonical target declarations, comparison obligations and literature locators.
Search the pinned StacksCore and StacksFrontier implementations and Mathlib first,
including equivalent formulations and dependencies. Dispositions are verified
upstream reuse, proved comparison, or a justified minimal Colib prerequisite.
An untriaged row, renamed module or reexport is not an accepted migration result.
In particular, selected exact-category conflations cannot be replaced by all
short exact sequences without the required relation comparison proof.

M0 remains open until the compiled declaration census, intended result endpoints,
Stacks-first audits, destination baseline/toolchain checks, and outstanding review
obligations are reconciled. This directory delivers its reproducible module/import
inventory component only.
