# Colib encyclopedia

The [published encyclopedia](https://kangxyz.github.io/colib/) is generated from successful
native CI runs and deployed through GitHub Pages.

The hand-maintained [pilot catalog](catalog/pilot.toml) contains twelve entries in three
subjects. [Bibliographic records](references.toml) pin the textual and software sources.

| Subject | Permanent IDs |
| --- | --- |
| Grothendieck groups and the dimension computation | COL-0001 through COL-0004 |
| Milnor K-theory and the ordered-pair comparison | COL-0005 through COL-0009 |
| Finite-scheme length and degree coefficients | COL-0010 through COL-0012 |

Run the following after building Colib.

```sh
python3 scripts/catalog.py build
```

The generated `build/catalog/index.md` gives mathematical statements, complete scope notes,
exact references, checked declaration signatures, defining modules and versioned source links.
`build/catalog/declarations.json` retains the machine-readable export. CI supplies both in
the `colib-encyclopedia` artifact.

## Reference contract

- An ID remains attached to its mathematical result through source moves and Lean renames.
  Released IDs are never reassigned.
- Record the inspected source version and an exact tag, theorem, clause or equation locator.
- Distinguish a source clause, specialization, generalization, proof ingredient, adaptation,
  and comparison. State added assumptions and the actual maps supplied.
- A single source item may require several entries. Several Lean declarations may implement
  one entry. An entry can reuse an upstream implementation.
- Code provenance identifies an earlier implementation independently of the mathematical
  reference.
- `author_checked` records the author's comparison of source and formal statement.
  Independent review has its own evidence and scope.
- Compilation and the production axiom audit belong to CI's native checks. Catalog generation
  reads that environment and verifies every registered declaration.
- An unchecked bibliographic attribution is marked `citation needed` in its owning
  mathematical draft. A missing mathematical premise remains an explicit obligation.
  Published catalog entries retain their actual proved scope.

The numbering follows the stable-reference principle of the
[Stacks Project tag system](https://stacks.math.columbia.edu/tags). The initial source
crosswalk is selective. Subsequent cohomology, homotopy, Quillen and Motivic migrations add
their own entries with the same contract.
