# Library tools

- `cache.sh` retrieves the Mathlib artifacts required by the pilot's focused imports.
- `check.sh` runs the library's native final checks, pinned axiom audit and catalog export.
- `catalog.py check` validates chapter/section structure, permanent items and production imports.
- `catalog.py show COL-0004` locates an item and its compatible native declaration information;
  retired IDs resolve to their preserved source record and retirement reason.
- `catalog.py build` exports the actual declaration signatures and renders the Library.
- `export_catalog.lean` reads permanent tags, literature citations, declaration types and native
  module imports from built Colib.
- `test_catalog.py` checks permanent IDs, retirement pages, and rejection of duplicate or reused
  retired IDs and missing sources.

- `site.py` renders the static, searchable Library from compatible native declarations.
- `stacks_cache.py` selects independent cache paths and exports/imports pinned Stacks artifacts.
- `test_stacks_cache.py` checks the cache identity, path boundary and round-trip behavior.

- `lint_style.py` discovers all Colib and ColibTest sources and invokes the native Mathlib
  text linter through temporary source-only import hubs.
- `test_lint_style.py` checks inclusion of leaf tests, exclusion of dependencies, and propagation
  of the native linter's exit status.
