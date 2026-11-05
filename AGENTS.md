# Colib project guidance

- Develop cohomology and homotopy theory in algebraic geometry. Organize source by mathematical
  objects, exact hypotheses and dependency direction.
- Use the pinned Mathlib and Stacks objects. Choose one canonical realization of each object or
  map. A comparison identifies its actual generators, maps, coefficients and signs.
- Keep precise lower imports. Production imports Colib, Mathlib, StacksCore or StacksFrontier.
  Development tools and tests have separate owners.
- Maintained text, identifiers and comments use English. Preserve source attribution and licenses.
- New public mathematical endpoints have a permanent catalog ID, exact source locator and explicit
  correspondence scope. Keep bibliography data in docs/references.toml and entries in docs/catalog.
  Internal supporting lemmas belong to the same mathematical owner.
- Compile changed leaves incrementally and repair them. Use scripts/check.sh for applicable final
  checks, reusing valid outputs. CI uses the same native checks. Kernel replay and separate client
  checks require an explicit user request.
- Lean compilation, source correspondence and independent mathematical review are distinct facts.
  Catalog author_checked records the author's source comparison. Independent review and any
  established-status claim need their actual review evidence.
- Preserve other contributors' work, inspect HEAD and status before writes and commits, and stage
  only owned paths. Push requires authorization in the current task.
