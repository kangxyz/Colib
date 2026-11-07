# Quillen and Motivic migration

The initial pilot selected three boundaries from the proposed integration. The table
records that starting scope; the sections below describe subsequent results.

| Boundary | Initial pilot surface | Work identified at the pilot |
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
General filtered realization is now available as part of the later Serre
localization proof below. This Resolution result does not close the entire
Quillen migration.

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

## Canonical connective Serre localization

The original normalized quotient fiber comparison is now a weak homotopy
equivalence on every component and at every source basepoint. Its actual group
comparison gives the connective localization long exact sequence, including
the K-one to K-zero boundary and terminal surjection, under only the original
small abelian-category and Serre-class hypotheses. Inclusion and quotient are
the original K-maps; the boundary retains its native path-space convention.

The supporting complete Theorem B retains both actual comma comparisons under
transition homotopy equivalences. Arbitrary filtered simplicial realization
invariance requires neither monicity nor countability. These are complete
mathematical results, not replacements for the original objects or conditional
localization adapters. See the [precise proof and evidence scope](migration/serre/completion.md)
and [Library integration record](migration/serre/integration.md). Negative
K-theory and the more general weak-transition form of Theorem B are not claimed by that Serre item.

## Original-map Waldhausen fibration and approximation

The fibration theorem now proves weak equivalence of the original canonical
acyclic-to-homotopy-fiber map, including its full reversed nullhomotopy and
independent object and morphism universes. Coarse two-out-of-three, extension,
exact base-category joint-cylinder data and its second-endpoint section are
retained. Actual relative rows and proved weak-cartesian bar assembly discharge
the global fiber comparison. See the [native scope and review boundary](migration/quillen/waldhausen-fibration.md).

Approximation proves weak equivalence of the unchanged delooping map from
App1/App2, exactness, target two-out-of-three and genuine source joint-cylinder
data. Its group equivalence has the original canonical KMap as its forward
map in every nonnegative degree, including K-zero. It assumes no row-equivalence
or homotopy-inverse premise. These results do not supply a strict S-model
comparison, a Quillen-Waldhausen comparison or nonconnective K-theory.

## Matsumoto's theorem for K₂ in characteristic zero

The completed source chain gives characteristic-zero additive equivalences from
the native Milnor K₂ group to actual right-projective Quillen K₂ and the literal
upper finite-module `SmallK.{u+1} 2`. Their forward homomorphisms are the original
Milnor-to-kernel-to-Quillen composites. Fiber perfectness, kernel generation and
the detector are proved inputs, not additional endpoint hypotheses. Both
directions commute with the original field-extension maps; the negative
normalization is minus the positive inverse.

The positive ordered scalar-unit-product marking holds over every field,
with a `ZMod 5` regression. Bijectivity retains `[CharZero F]`.
Finite realization geometry now uses native `Convexity.StdSimplex` coordinates directly.
Earlier candidate endpoints and regressions passed focused strict compilation
and native QA within their recorded scopes. The Lean 4.35 integration is published
at `0fd43f0253d6ff441fbc3e82420a0573ad694310`, whose original whole-library
[CI run](https://github.com/kangxyz/colib/actions/runs/42373233801) passed build,
tests, native lint, axiom audit and Library checks. This exact-commit result does
not certify later descendants. See the
[exact comparison and verification scope](migration/quillen/field-k2-comparison.md),
[algebraic map](migration/quillen/field-k2-native-kernel.md), and
[stable-fiber proof](migration/quillen/field-k2-stable-fiber.md).

## Original-map Gillet-Waldhausen

The native bounded-complex proof retains the actual abelian ambient, term bounds,
cofibrations, quasi-isomorphisms and canonical degree-zero single KMap. Its group
equivalence includes K-zero and the original object/hom universe bounds. Exact
filtrations, finite Euler decomposition, filtered-union coverage and the actual
identity-cone cylinder supply the proof, without a theorem-shaped input.
See [the exact scope and dependency ownership](migration/gillet-waldhausen.md).

## Dense Waldhausen cofinality

The actual dense full inclusion now has its original positive K-equivalence,
all-degree injectivity and degree-zero exact tail. A genuine complement grading,
finite replacement, actual row-grade nerve comparison and the proved original
fibration supply the proof. Coarse K-zero remains the true homotopical endpoint. The actual value map now
identifies it with complement classes, retaining object generators and the
original matching-universe map.
See [the precise native scope](migration/quillen/waldhausen-cofinality.md).

## General Waldhausen Grothendieck K-zero

The original object-loop comparison is an equivalence from the actual free
abelian presentation by weak arrows and cofibration pushouts to homotopical
Waldhausen K-zero, including independent object and morphism universes. No
cylinder or factorization hypothesis is added to this comparison. Actual
edge-path generation supplies surjectivity, and the realized universal grading
is its inverse. Original exact-functor KMaps commute with the comparison.

With genuine target factorization, the actual coarse value map identifies
K-zero with the quotient by the original exact-functor image. Its composite
with the unchanged changeWeak KMap is the literal quotient, and its kernel
and surjectivity give the exact original K-zero tail. No higher-degree
image-quotient or spectrum conclusion is inferred. See the
[canonical maps and verification scope](migration/quillen/waldhausen-grothendieck-kzero.md).

## Original S-construction composition triangles

The actual two-transformation simplicial triangle retains the original cylinders
on all three faces, including the genuine composite. Its full zero-vertex family
is constant under the three explicit chosen-zero equalities. The sole zero-simplex
definition has its lower simplicial owner, with existing K-theory clients unchanged.
See the [exact source and scope](migration/quillen/waldhausen-composition-triangle.md).
This does not establish iterated-S or spectrum compatibility.

## Coherent Waldhausen endotransformation tracks

The actual finite S-prespectrum, whole structure-compatible weak-transformation
homotopies and relative composition retain the original KMap, basepoints and
independent parameters. The genuine zero endotransformation contracts the
original normalized self-track in a grading-coarse target; the null-loop
endpoint retains both supplied null legs. Native category and path objects
have one owner. COL-0276--COL-0278 record the complete contribution and its
precise coherent-track scope. See the
[source and verification boundary](migration/quillen/waldhausen-coherent-endotransformations.md).

## Genuine connective Waldhausen Omega-spectra

Every actual iterated S-construction loop structure map is a complete weak
homotopy equivalence, including path components and every finite based
homotopy set. The proof uses the genuine added-initial-row contraction,
higher first/tail additivity and the full actual path-fiber comparison.
COL-0282 packages the same prespectrum and exact-functor maps as an
Omega-spectrum without new structural hypotheses. Original KMaps and
independent category universes are retained. See the
[actual maps and verification scope](migration/quillen/waldhausen-omega-spectrum.md).

## Bounded-complex resolution bridge

An actual bounded native complex quasi-isomorphic to a single object now yields
a finite admissible resolution in any replete kernel-closed class containing
zero. Lifting the resulting tower into an exact full subcategory retains all
ambient maps and its length. Arbitrary small-model functoriality also retains
the canonical K-maps. See the [G-localization and resolution scope](migration/scheme-kg/README.md).
The scheme-specific comparison is developed in the separate
[native scheme K/G slice](migration/scheme-kg/native-scheme-comparison.md); it is not
a conclusion of the bounded-resolution foundation alone.

## Actual-target and finite-module G-localization

The canonical connective Serre sequence now transports to the actual specified
target and to the original small-model K-map. For a commutative Noetherian ring,
the literal native finite-module functor at any multiplicative set gives the
full connective sequence, including the homotopical G-zero tail. Support is
annihilation by one denominator; for powers of an element this is one uniform
natural power. The existing fraction-field K-map is retained definitionally.
See the [exact scope and source crosswalk](migration/scheme-kg/fraction-localization.md).
This arbitrary-set result by itself does not identify principal supported
G-theory with G of the quotient ring or prove general scheme-open localization.

## Principal closed/open G-localization

Actual finite-module restriction along R to R/(r) is fully faithful with essential
image the r-annihilated modules. Inside the existing supported small category,
multiplication by r constructs finite image filtrations with such factors.
Classical dévissage therefore gives G(R/(r)) equivalent to principal supported
G-theory, with forward map compatible with the original quotient-restriction
smallKMap. The transported original boundary gives the full connective
closed/open sequence, including G-zero. No regularity or nontriviality hypothesis
is added. See the [precise native scope](migration/scheme-kg/principal-closed-localization.md).

## Native scheme K/G-theory and regular comparison

Native vector bundles and coherent module sheaves now carry the original upper
small-model connective K-groups. The literal inclusion gives the canonical K-to-G
map, and actual open restriction obeys strict identity and composition laws and
commutes with that comparison. On a quasi-compact regular scheme with the
resolution property, native Stacks perfectness and bounded replacement discharge
actual finite-resolution hypotheses, proving the canonical comparison is an
equivalence in every nonnegative degree. No separatedness, uniform dimension or
global projectivity assumption is added. See the
[precise geometric scope and literature](migration/scheme-kg/native-scheme-comparison.md).
This does not assert general scheme-open K-localization or nonconnective K-theory.
