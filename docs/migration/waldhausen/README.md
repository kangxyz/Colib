# Waldhausen realization, functoriality and additivity

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
The original group operations are retained. `Additivity.K_mul_comm` proves
commutativity in every degree, including K-zero; `Additivity.KCommGroup` explicitly
extends the existing group structure without replacing it.

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
supplies the two unit restrictions used by the later coproduct multiplication proof.

## Dependency boundaries

Rows' pointwise weak multiplicativity, weak preservation by reindexing and
postcomposition, and grid/nerve comparison do not need the derived row
Waldhausen structure. The source's row structure assigns its weak field literally
to this same pointwise predicate. The separate Reedy cofibration and row-pushout theorems are not replaced by
assumptions. Additivity below is proved directly on the actual interval grids.

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

## Earlier validation boundary

The integration preparation is based on commit
`e8e94fd934d4ba446cfc51c9191a9667900427a8` in an independent output tree with a
reflink-capable copy of its build cache. Every new production leaf is recompiled
with strict project flags and the shared serial Lean lock. New actual-map
regressions and the existing Waldhausen regressions are compiled separately.
Input, dependency artifact, output and log hashes are recorded in the release
evidence. No isolated success is accepted solely because a target file exists.

Compilation, source correspondence, independent mathematical review and the
production axiom audit are distinct evidence. No kernel replay, downstream
client assurance, strict-model normalization, approximation, localization, or
Quillen/Waldhausen comparison is implied by compilation.


## Complete additivity and the existing group law

The additional chain is integrated on main `8d4b81261a9408e3550833e80fd6059f608b3e3d`.
The module-level source crosswalk is in `additivity.json`, with fixed source
identities in `additivity-sources.json`. It adds 117 production modules, generalizes the existing canonical functor-rebasing
interface to independent universes, and adds ten
in-package regression files; earlier main changes are preserved.

For a genuine cofibration sequence of exact functors `F -> G -> H`, the final
`CategoryTheory.Waldhausen.Additivity.KMap_additivity_mul` states
`KMap G n x = KMap F n x * KMap H n x` in every nonnegative K-degree. The actual
exactness witnesses parameterize these maps. The common object and morphism
universe bounds for source and target, target binary coproducts, objectwise
cofiber pushout squares, and relative comparison cofibrations are retained.
No realization-equivalence, product-equivalence, surjectivity, or commutativity
hypothesis is added. In particular the statement includes K-zero.

The proof retains the actual maps at each boundary:

1. The ordinary subdivision is the unreversed ordinal join `[n] * [n]`, with
   the same simplex map on both halves. Its first-half endpoint is realized
   literally. It is not Mathlib's subdivision or reversed Segal subdivision.
2. Subdivided representables contract by the actual two-stage ordinary
   construction. The explicit boundary-cylinder retraction gives realized
   monomorphism HEP, using the pinned relative simplicial cell complex.
   Actual pushout and coherent sequential homotopy invariance propagate the
   endpoint equivalence to every simplicial set, including infinite dimension.
3. A generic unbased homotopy equivalence induces a bijective actual `piMap`.
   Only the forward basepoint equation is required; no based inverse is assumed.
   Degree one uses the genuine pointed-set tail of the homotopy-fiber sequence.
4. The three-stage mixed-ordinal deformation has constant chosen-zero tracks.
   The actual horizontal endpoint is surjective on based homotopy groups, so
   cancellation gives equality of the original K-map with the actual sum-functor
   K-map, initially in quotient-before-subobject order.
5. The canonical realization-product map is injective and admits exact lifts
   from compact Type 0 sources. Finite right support suffices for the actual
   homotopy-group isomorphism. A homeomorphism is proved for locally compact
   right realization, not for arbitrary ordinary topological products.
6. The product K-equivalence has precisely the pair of the original projection
   K-maps as its forward map. The coproduct functor therefore gives a group
   homomorphism whose two unit restrictions are identity. This identifies it
   with the existing multiplication and proves commutativity, also in K-zero.
   Commutativity yields the final subobject-then-quotient order.

COL-0213 through COL-0219 record realized HEP, pushout and sequential homotopy
invariance, ordinary subdivision, unbased homotopy groups, the based deformation,
and original K-map additivity. COL-0220 records the exact realization-product
comparison; COL-0212 records the original commutative K-group law. The intervening
IDs belong to independent work and are not allocated by this change.

Hatcher's cellular HEP, cobase-change and homotopy-group exercises are cited with
precise locators. Weibel IV 3.1 supplies realization background, explicitly with
its compactly generated topology caveat for products. Weibel V Definition 1.1(b)
and Theorem 1.2 supply the cofiber-sequence and additivity correspondence. Source
adaptation and original comparison constructions are distinguished in the
compiled reference annotations. A strict chosen-zero S-model comparison and
broader Quillen-Waldhausen structural comparison remain separate obligations.

The integration uses the normal native `scripts/check.sh` categories: strict
production build, all in-package tests, Batteries declaration lint, Mathlib text
style and generated-entry check, the pinned production axiom auditor, and native
Library export/site validation. Only the three standard axioms are allowed.
A successful build, literature correspondence and independent mathematical
review remain separate claims; no kernel replay or extra downstream test is
implied.
