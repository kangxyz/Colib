# Quillen and Motivic migration

The initial pilot selects three boundaries from the proposed integration.

| Boundary | Current Colib surface | Subsequent work |
| --- | --- | --- |
| Finite-module K₀ | Categorical dimension equivalence over a field | Compare the original Quillen degree-zero map and its exact-category presentation |
| Milnor K₂ | Equality of the two Steinberg relation spans and the symbol-preserving tensor comparison | All-degree tuple symbols, norms, residue maps and Quillen field comparisons |
| Finite-flat coefficients | Affine finite-algebra length-degree sum | Construct the original finite-flat spans and prove their faithful cycle and composition equations |

The initial release is a source-indexed reference-indexed pilot. The Quillen and Motivic libraries
remain migration sources at the recorded commits below.

- Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
- Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.

Extend the closed pilot one mathematical chain at a time. Exact categories and shared module
foundations precede scheme K/G-theory and perfect-complex localization. Finite correspondence
geometry precedes transfers, ordinary Nisnevich hypercohomology and strict invariance.
Record cohomological degrees, coefficient universes, signs, canonical maps and actual
conditions at each endpoint.

Use the pinned Mathlib and Stacks objects and interfaces directly. Add missing mathematics
at its native owner; do not maintain legacy models or compatibility layers. Genuine comparisons
between distinct mathematical constructions retain their precise hypotheses and actual maps.
Historical implementation attribution is preserved without retaining an Aglib source inventory
or making Aglib a dependency. Actual consumers determine the incremental validation scope.
Source correspondence and mathematical review retain their own status.

The first Library release demonstrates this process on twelve entries. The amount of
further migration is measured by the actual proof and interface repairs for subsequent slices.


## Waldhausen additivity milestone

The actual unnormalized S-construction now supports the complete original
canonical K-map additivity formula, including degree zero. The ordinary
unreversed subdivision endpoint is a proved realization homotopy equivalence;
compact-source lifting for the actual realization-product comparison gives the
original product K-map equivalence. Coproduct is the existing group law, which
is proved commutative also in K-zero. Exactness, cofiber squares, relative
cofibrations, target binary coproducts and the source universe bounds are retained.
See [the chosen-model and source crosswalk](migration/waldhausen/README.md).
A strict chosen-zero S-model comparison and broader Quillen-Waldhausen comparison
remain separate work.

## Objectwise-finite Quillen Resolution

The resolving-subcategory theorem now uses actual finite admissible towers,
length-one comma contractions and the actual countable nerve union. Resolution
lengths need not have a common bound. The resulting Q-space equivalence and
all-degree K-equivalence retain the original inclusion maps. See the
[precise native-model and source scope](migration/resolution/README.md).
General filtered realization and Quillen-Waldhausen comparisons remain
separate work; this milestone does not close the entire Quillen migration.

## Canonical Grothendieck–Quillen K-zero comparison

The original Grothendieck-to-Quillen K-zero map is now proved injective and
bijective on the existing realized Q-category and its original zero basepoint.
The proof establishes faithfulness of the original groupoid-completion functor
using actual finite-skeleton decoders and compact relative homotopies. See the
[native proof and source scope](migration/quillen/kzero-comparison.md). This does
not claim a higher K-group comparison or completion of the Quillen inventory.

## Classical Quillen devissage

Actual finite filtrations now contract the inclusion comma categories through
the layer poset. The resulting classifying-space and all-degree K-equivalences
retain the actual inclusion maps and canonical zero basepoint. The full
subcategory is intrinsically abelian: no extension-closure or uniform-length
hypothesis is added. See the [native proof and source crosswalk](migration/devissage/README.md).
This does not assert a Q/S comparison or finish the historical Quillen inventory.
