# Dense Waldhausen cofinality

## Original statement and map

`DenseCofiberData W P` specifies zero membership, invariance under original weak
arrows, extension and quotient closure for actual cofiber squares, and an actual
coproduct complement for every object. With binary coproducts, genuine fine
joint-cylinder data and its separate second-endpoint section, the unchanged
full inclusion has:

- injective canonical KMap in every nonnegative degree;
- bijective canonical KMap in positive degrees, with that exact forward map;
- image equal to the kernel of change of weak equivalences in every degree;
- an injective, exact K-zero tail surjective onto actual coarse K-zero;
- the actual coarse value equivalence with common-complement classes, preserving
  every object class and the original matching-universe class map.

Object and morphism universes are independent. No K-zero inclusion surjectivity,
strict chosen-zero model comparison or nonconnective statement is asserted.

## Proof and native ownership

Categorical grading, complement classes, actual quotient rows and finite grade
realizability live in `CategoryTheory.Waldhausen.Cofinality`. Original weak maps
are contained in equality-of-grade maps. Gluing, two-out-of-three and extension
for this coarse structure are proved, not additional endpoint assumptions.

The realized comparisons live in `KTheory.Waldhausen.Cofinality`. Actual zero
natural transformations contract equal-grade row categories. Finite replacement
and cofiber completion realize the necessary finite differences. The resulting
group nerve uses exactly the subgroup of actual object grades. The comparison
preserves each original first-row interval grade.

The original fibration and groupoid asphericity give coarse positive-degree
vanishing. Existing based `AsSmall` homeomorphisms transport that calculation;
all final statements remain on the original categories and KMaps. The dense
subcategory and zero-grade category differ only in their proved membership
predicates. Their comparison changes no underlying object or morphism.

## Sources and correspondence

The implementation adapts `Quillen/Waldhausen/Cofinality` and three categorical
helpers at pin `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Each source file records
its exact original path. Mathlib categories, full and wide subcategories,
simplicial sets, group nerves, realizations and homotopy groups remain native.

Thomason-Trobaugh, *Higher algebraic K-theory of schemes and of derived
categories*, The Grothendieck Festschrift III, Progress in Mathematics 88 (1990),
247-435, Theorem 1.10.1 (pages 275-277) and Exercise 1.10.2 (page 277), give the
classical graded and dense formulations. This is an adaptation: the formal
input is an additive object grading rather than a prescribed epimorphism from
homotopical K-zero. The actual coarse K-zero endpoint is identified with the complement group by
its original value map. The general map agrees with the matching-universe
construction. No complete spectrum fiber sequence is claimed here.
Waldhausen's distinct strict-cofinality result is not substituted for this scope.

`COL-0267` owns the actual group-grade comparison; `COL-0268` owns dense
cofinality for the original inclusion. Author source correspondence, native
compilation and independent mathematical review are separate checks. Internal
validation records are kept outside the repository.

## Verification scope

The initial 18 production modules and the in-package original-map regressions pass
strict native compilation. Native declaration lint and the independent axiom
auditor pass on the endpoint's actual imported production closure; only
`propext`, `Classical.choice` and `Quot.sound` occur. Native text lint checks the
new production and test sources. Metadata checks, generated-root verification
and the Python suite remain unchanged. These focused checks do not replace the
original whole-library checks required before this candidate is merged.

The [general Grothendieck K-zero comparison](waldhausen-grothendieck-kzero.md)
records the canonical object presentation and image-quotient obstruction used
to identify the final class groups.
