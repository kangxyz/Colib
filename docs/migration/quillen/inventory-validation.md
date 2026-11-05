# Module inventory validation

Date: 2026-11-05. Scope: the reproducible historical module/import inventory only.
Destination baseline: `7603d2dba0e5c67646277ca269b76ec341bf3078`.
This record does not accept M0 or any mathematical migration slice.

## Executed checks

The README's generation command was executed with the pinned Quillen and Aglib
Git repositories and both Mathlib/Batteries source Git repositories. It exited 0.
The command was then repeated into a separate output directory. Byte comparisons
with `cmp` for all five generated artifacts exited 0:

- `files.jsonl`
- `modules.jsonl`
- `external-imports.jsonl`
- `unresolved-imports.jsonl`
- `summary.json`

`python3 -m unittest discover -s scripts -p 'test_quillen_inventory.py'`:
7 tests passed, exit 0.

`python3 -m unittest discover -s scripts -p 'test_*.py'`:
24 tests passed, exit 0, with the contemporaneous existing Colib tests.

`python3 scripts/catalog.py check`:
2 chapters, 3 sections, 12 permanent items checked, exit 0.

`python3 -m py_compile scripts/quillen_inventory.py scripts/test_quillen_inventory.py`:
exit 0.

## Observed source graph

- 5,832 Quillen directory modules and one top-level entry.
- 836 local `Quillen/Aglib/` candidates and their separate aggregate entry.
- 606 reachable external Aglib modules; 6,439 module ledger rows in total.
- 28,153 unique source import edges; 2,010 external import occurrences.
- Zero missing Quillen/Aglib source module edges.
- Zero unverified external module files against the source Mathlib/Batteries pins.
- No cyclic components; longest source dependency tier is 254.
- 1,281 in-package tests and 202 downstream Lean fixtures counted, not run.

Counts and exact source pins are generated in `summary.json`, which is authoritative
if this prose is being reconciled after regeneration. All migration rows remain
untriaged. The scanner and this validation were reviewed by their implementation
author only; no independent mathematical review is claimed.

## Not established

Historical source compilation and a compiled declaration census were not performed.
Target Lean compilation, axiom closure, in-package Lean regression execution,
source-to-target mathematical correspondence and literature correspondence are
outside this inventory validation. No separate downstream/client check or kernel
replay was performed. Future slice evidence must not inherit those claims from
these tooling checks. No commit or push was performed by the inventory worker.
