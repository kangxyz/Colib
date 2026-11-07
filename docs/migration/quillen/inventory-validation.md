# Module inventory validation

Scope: the reproducible historical Quillen module/import inventory after excluding
external Aglib source data. Destination baseline before cleanup:
`5c0a7ab9c060b7482a3c49056bb9b3284fc47829`.
This record does not accept M0 or any mathematical migration slice.

## Executed checks

The README's generation command was executed with the pinned Quillen Git
repository and Mathlib/Batteries source Git repositories. No Aglib repository was
supplied or read. It exited 0. Repeating the command produced identical SHA-256
hashes for all five generated artifacts:

- `files.jsonl`
- `modules.jsonl`
- `external-imports.jsonl`
- `unresolved-imports.jsonl`
- `summary.json`

`python3 -m unittest discover -s scripts -p 'test_quillen_inventory.py'`:
10 tests passed, exit 0. Tests cover lexical scanning, graph components,
Git-object isolation, Quillen-only generation without an Aglib manifest pin,
external Aglib reference classification, refusal to inspect an Aglib package
repository, and retained inventory counts.

Comparison with the pre-cleanup baseline confirmed that all 8,053 Quillen file
rows were preserved exactly. All 5,833 Quillen module source identities, hashes,
imports, categories, sizes and local-candidate/aggregator flags were preserved.
Graph-derived fields were regenerated over Quillen alone. All external-edge
consumers belong to the retained Quillen graph. No `source=aglib` rows remain.

## Observed source graph

- 5,832 Quillen directory modules and one top-level entry: 5,833 ledger rows.
- 836 local `Quillen/Aglib/` candidates and their separate aggregate entry remain.
- 24,490 unique internal source import edges; 3,993 external import occurrences.
- 2,632 external Aglib import occurrences remain unverified references only.
- All 1,361 other external import occurrences have source-file existence evidence
  against the recorded Mathlib/Batteries pins.
- Zero missing Quillen source module edges. This does not resolve external Aglib
  imports or establish that the historical Quillen environment compiles.
- No cyclic components; longest source dependency tier is 254.
- 1,281 in-package tests and 202 downstream Lean fixtures counted, not run.

Counts and exact source pins are generated in `summary.json`, which is authoritative
if this prose is being reconciled after regeneration. The original Quillen source
manifest remains provenance, including its historical external dependency pins;
it is not a list of current Colib dependencies. All migration rows remain
untriaged. No independent mathematical review is claimed.

## Not established

Historical source compilation and a compiled declaration census were not performed.
Target Lean compilation, axiom closure, in-package Lean regression execution,
source-to-target mathematical correspondence and literature correspondence are
outside this inventory validation. No separate downstream/client check or kernel
replay was performed. Future slice evidence must not inherit those claims from
these tooling checks. No commit or push was performed by the inventory worker.
