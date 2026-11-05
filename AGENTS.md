# Colib project guidance

- Develop cohomology and homotopy theory in algebraic geometry. Organize source by mathematical
  objects, exact hypotheses and dependency direction.
- Use the pinned Mathlib and Stacks objects. Choose one canonical realization of each object or
  map. A comparison identifies its actual generators, maps, coefficients and signs.
- Keep precise lower imports. Production imports Colib, Mathlib, StacksCore or StacksFrontier.
  Development tools and tests have separate owners.
- Maintained text, identifiers and comments use English. Preserve source attribution and licenses.
- Begin new mathematical work at docs/LIBRARY.md and CONTRIBUTING.md. The Library owns chapters,
  sections, mathematical items, reading order and references. Lean modules own source placement
  and imports.
- Public mathematical items have permanent IDs in docs/library/entries and compiled @[colib_tag]
  bindings. Supporting declarations use ordinary Lean names and imports.
  Use native @[stacks] for Stacks tags and @[colib_ref] for precise book/paper locators. Bibliography
  identity belongs in docs/references.toml. Internal helpers keep their mathematical owner.
- Follow Mathlib naming/style and the pinned Stacks conventions. Use native namespaces and precise
  lower imports. Coordinate ID reservations and shared chapter/bibliography edits across agents.
- Compile changed leaves incrementally and repair them. Use scripts/check.sh for applicable final
  checks, reusing valid outputs. CI uses the same native checks. Kernel replay and separate client
  checks require an explicit user request.
- Lean compilation, source correspondence and independent mathematical review are distinct facts.
  Catalog author_checked records the author's source comparison. Independent review and any
  established-status claim need their actual review evidence.
- Preserve other contributors' work, inspect HEAD and status before writes and commits, and stage
  only owned paths. Push requires authorization in the current task.
