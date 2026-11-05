# Colib Library

The [Library](https://kangxyz.github.io/colib/) is Colib's mathematical organization centre.
It owns the chapter and section sequence, permanent mathematical items, chosen-model
explanations, stated scope and literature crosswalk. Lean files own the checked definitions and proofs.
The chapter structure and source dependency graph express their respective mathematical roles.

## Maintained owners

| Information | Owner |
| --- | --- |
| Chapters, sections and reading introductions | docs/library/chapters/*.toml |
| Mathematical statements, kinds, conditions and correspondence review state | docs/library/entries/<chapter>/<ID>.toml |
| Declaration membership in a mathematical item | The compiled `@[colib_tag "COL-0004"]` attribute |
| Stacks correspondence | Mathlib's existing `@[stacks TAG "scope"]` attribute |
| Book and paper correspondence | `@[colib_ref "key" "locator" "relation" "scope"]` |
| Bibliographic identity, edition, document and version | docs/references.toml |
| Declaration types, defining modules and implementation references | Native Lean export |
| Reading pages, reverse references, search and links | Generated Library website |

One item can have several implementing declarations and several literature references.
An implementation can serve several explicitly registered items. Upstream declarations are
registered in Colib/Library/Upstream.lean. The upstream object and theorem keep their native owner.

## Structure and permanent links

Chapters contain sections. Each section has an introduction and an ordered sequence of typed
items such as definitions, lemmas, theorems and comparisons. The homepage presents the table of
contents. Chapter and section pages provide local reading routes. The Modules view reads
actual defining modules and imports from Lean. Each item has its own page at
`tag/COL-0004/`, with exact citations, Lean declarations and automatically exported code
references. Existing
`#COL-0004` bookmarks redirect to the permanent item page.

IDs start with COL- and at least four decimal digits. They are independent of chapter numbers,
Lean names and file paths. Moving an item preserves its ID. Released IDs are never reused.
A substantive replacement records the relation to the earlier item explicitly. Reading positions
can change without changing permanent links.

Only occupied mathematical chapters and source families are created. The migration programme
in docs/MIGRATION.md identifies upcoming cohomological and homotopical work. A new chapter is
introduced with its first concrete mathematical contribution and source owner.

## References in Lean

Use existing Stacks syntax for a Stacks statement and Colib's general reference attribute for
a book or paper. Each bibliographic key resolves through docs/references.toml.

```lean
@[colib_tag "COL-0004", stacks 00JE "finite-module dimension equivalence",
  colib_ref "WeibelKBook" "II, section 2, field computation" "adaptation"
    "The categorical Grothendieck group of finite modules over a field"]
def fgModuleRankEquiv ... := ...
```

A citation records the particular clause, hypothesis range and mathematical construction being
used. A definition, an input theorem, its proof and a later comparison have their actual reference
roles and scope. Several references can be attached to the same declaration. The exporter reads
these compiled attributes and checks all keys and locators against the maintained bibliography.

Retain native EGA and SGA attributes when an applicable upstream declaration already has them.
The supported website export currently indexes Stacks and the general Colib bibliography
attribute. Extend the exporter with an actual indexed consumer when adding another database.

Code provenance identifies an earlier implementation independently of the cited mathematics.
A result proved in Colib can state its original contribution and cite background accurately.
An unchecked attribution is marked `citation needed` in its mathematical draft. An unresolved
mathematical premise is stated as an obligation in the owning source family.

## Dependencies and status

Lean's module system owns code organization and imports. The native exporter reads defining
modules and their direct imports, and records constants used in registered declaration types
and bodies. Item pages link the registered results occurring among those direct references.
The section sequence provides the reading order.

`@[colib_tag]` has the single purpose of attaching a permanent webpage identifier to a public
mathematical item. Helpers use ordinary Lean names. An agent adds a tag when a result needs a
stable, independently citable Library page. The tag preserves its link through a declaration
rename or source move. An ordinary supporting declaration can carry a literature citation
without a permanent tag; its references appear on its module page. Books and papers use `@[colib_ref]`, and Stacks uses its native tag.

The native exporter determines which registered declarations exist in the built environment.
A successful production build and axiom audit retain their checked source and scope.
`author_checked` records the author's literature correspondence check. Independent mathematical
review has its own evidence and checked span. CI validates metadata integrity and native
compilation; maintainers assess mathematical correspondence and source applicability.

## Contribution transaction

A mathematical contribution updates its Lean source, item and chapter ownership, references and
applicable tests together. The Library is the first route for finding an existing result and the
place where its new public mathematical surface is registered. Internal supporting lemmas belong
to that same owner. CONTRIBUTING.md defines assignments, style and incremental validation.

## Item schema and agent lookup

Each file contains one `[entry]` table. A contribution uses an allocated identifier and an
existing section owner, as in docs/library/entries/k-theory/COL-0004.toml.

```toml
[entry]
id = "COL-0004"
title = "K₀ of finite-dimensional vector spaces"
kind = "theorem"
section = "grothendieck-groups"
order = 40
statement = "Dimension identifies the Grothendieck group with the integers."
scope = "Finite-dimensional vector spaces over a field, with the specified object classes."
review = "author_checked"
```

Use `python3 scripts/catalog.py show COL-0004` to locate the item and chapter. A compatible
native export also supplies its actual Lean declarations and defining modules. Use
`rg 'colib_tag "COL-0004"' Colib` to find its compiled bindings. The website's reference
index finds all items attached to a book, paper or Stacks locator.

Place a new mathematical file under its native Mathlib-style subject. New chapters and sections
need an introduction and an actual first item. Code ownership and imports are read from Lean.
Native tag bindings must resolve to maintained item IDs. Every published item has a
compiled precise reference, and every citation key has one bibliographic record.

The first literature records include Weibel's online chapters II and III of *The K-book* and
Milnor's 1970 paper *Algebraic K-theory and quadratic forms*. The inspected documents and hashes
are recorded beside their bibliographic identity. Reference annotations retain exact clauses
and the scope of any adaptation or comparison.

Bibliographic keys use letters, digits, underscores and hyphens, beginning with a letter.
Chapter, section and item orders are nonnegative integers.
