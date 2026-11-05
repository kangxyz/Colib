# Library tools

- `cache.sh` retrieves the Mathlib artifacts required by the pilot's focused imports.
- `check.sh` runs the library's native final checks, pinned axiom audit and catalog export.
- `catalog.py check` checks the maintained catalog, bibliography keys and production imports.
- `catalog.py build` exports the actual declaration signatures and renders the encyclopedia.
- `export_catalog.lean` reads declaration names, types and defining modules from built Colib.
- `test_catalog.py` checks permanent pilot IDs and rejection of duplicate IDs and missing sources.
