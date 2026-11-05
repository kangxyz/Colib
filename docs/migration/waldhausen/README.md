# Waldhausen realization and weak-transformation chain

## Chosen model and public scope

The S-construction used here is the existing unnormalized interval-grid model.
Its diagonal objects satisfy `IsZero`; they are not required to be equal to the
specified zero object. The category of rows is the full subcategory of interval
diagrams satisfying the original zero, horizontal cofibration and quotient
pushout conditions. Its weak-arrow category retains precisely pointwise weak
natural transformations. The grid/nerve equivalence identifies every object,
ordinary arrow, mixed arrow and ordinal restriction. It does not establish a
comparison with a strict chosen-zero S-construction.

`delooping` is literally Mathlib geometric realization of this diagonal S-set.
The chosen basepoint is the realization of the constant-zero degree-zero simplex.
`groups n` and `Structure.K n` are the existing homotopy groups in degree `n + 1`.
Only positive K-degrees receive their automatic commutative-group instance; the
additivity theorem needed for K-zero commutativity is not asserted here.

## Maps and homotopies

1. Exact functors act by actual postcomposition on S-grids and weak rows.
2. `groupsMap` targets the image-zero basepoint. `groupsMapOfZeroEq` uses an
   explicit equality to a specified target zero; it does not choose an arbitrary
   path between basepoints.
3. A pointwise weak natural transformation gives a genuine nerve-direction
   cylinder. Each row stays an endpoint row, and crossing arrows use the actual
   transformation component. Reindexing coherence is proved.
4. Realization gives a free homotopy with endpoints precisely `deloopingMap hF`
   and `deloopingMap hG`. No strict-zero hypothesis is needed for that result.
5. Explicit equalities of both image zeros with the same target zero make the
   homotopy fixed at the basepoint. This identifies the actual equality-rebased
   homotopy-group maps.
6. Canonical pointed K-maps rebase the functor along the unique
   zero-object isomorphism. This changes the functor by an actual natural
   isomorphism, not the S-model. Weak-transformation invariance and composition
   apply to those specified maps, rather than to arbitrary basepoint paths.

The exact-functor homotopy chain retains the source's common object universe and
common hom universe for C and D. The packaged K-functor is on the stated small
Waldhausen categories. No arbitrary cross-universe extension is claimed.

The constant chosen-zero functor is exact, and its actual simplicial map,
realization map and K-map are the stated constant maps. This unit degeneration
is not additivity or a K-zero commutativity theorem.

## Dependency boundaries

Rows' pointwise weak multiplicativity, weak preservation by reindexing and
postcomposition, and grid/nerve comparison do not need the derived row
Waldhausen structure. The source's row structure assigns its weak field literally
to this same pointwise predicate. The Reedy cofibration and row-pushout theorems
are not imported or replaced by assumptions.

Generic bisimplicial diagonal operations live under AlgebraicTopology.
Simplicial S-grid cylinders live under CategoryTheory.Waldhausen. Realization,
based homotopies and homotopy-group maps live under KTheory.Waldhausen.

## Literature and source correspondence

Implementation provenance is the Quillen source snapshot
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, with original author and license headers
preserved. The source families are Waldhausen/KTheory and Functor,
SConstruction/Bisimplicial, SConstruction/Rows, the nerve-cylinder and weak
natural-transformation leaves, and the pointed-functor/functoriality leaves.

Waldhausen, *Algebraic K-theory of spaces* (1985), section 1.3, pp. 328-330, is
background for the S-construction, exact-functor maps and weak-transformation
homotopies. The native citation annotations deliberately do not assert that the
unnormalized IsZero implementation has already been compared to a strict
chosen-zero presentation. The realized cylinder and homotopy-group lemmas have
their existing independent lower ownership and references.

COL-0146 retains the lower S-set construction. COL-0154 records the actual
weak-row nerve presentation. COL-0155 records realization and image-zero maps.
COL-0156 and COL-0157 distinguish free from based weak-transformation homotopies.
Canonical K-map functoriality and its actual zero-functor degeneration are COL-0158. IDs COL-0150 through COL-0153
are not allocated here; the latest upstream and separate K-zero integration
reserve their own IDs. All new IDs require another conflict check before publication.

## Validation boundaries

The integration preparation is based on commit
`e8e94fd934d4ba446cfc51c9191a9667900427a8` in an independent output tree with a
reflink-capable copy of its build cache. Every new production leaf is recompiled
with strict project flags and the shared serial Lean lock. New actual-map
regressions and the existing Waldhausen regressions are compiled separately.
Input, dependency artifact, output and log hashes are recorded in the release
evidence. No isolated success is accepted solely because a target file exists.

Compilation, source correspondence, independent mathematical review and the
production axiom audit are distinct evidence. No kernel replay, downstream
client assurance, strict-model normalization, additivity, approximation,
localization, or Quillen/Waldhausen comparison is implied by compilation.
