# Native G-localization and resolution foundations

This batch combines actual-target and small-model Serre localization, arbitrary-set
finite-module G-localization, the principal closed/open sequence, and the bounded
finite-resolution bridge. The bridge is part of this full batch and supports the
scheme comparison at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This document records the COL-0271–0274 foundation batch. The later
[native scheme comparison](native-scheme-comparison.md) has its own geometric
assumptions and verification scope.

## Closed results

`Colib/CategoryTheory/ExactCategory/Resolution/BoundedComplex.lean` starts with
Mathlib's actual bounded cochain complex, an actual quasi-isomorphism to a single
object, and term membership in a replete, kernel-closed class containing zero.
Its result is the existing `ExactStructure.FiniteResolution`, not a replacement
resolution model or an assumed resolution hypothesis.

The positive exact tail proves that degree-zero cycles belong to the resolving
class. The negative tail resolves the degree-minus-one cycles. The actual
boundary kernel supplies the two short exact rows connecting these cycles to
zero-th homology. The given quasi-isomorphism then transports the terminal
augmentation to the requested object. Negative and overlapping bounds, including
empty support intervals, are allowed. No common bound, global projectivity, or
extension closure of the resolving class is used.

`Resolution/LiftSubcategory.lean` lifts such a tower into an exact full
subcategory when its terms belong there and kernel closure applies. It retains
all ambient maps and proves equality of the tower lengths. These endpoints form
COL-0271. Weibel, *The K-book*, V.3.1 is cited for the resolution-theorem context;
the extraction and lift are proved in these modules. The elementary cycle row
follows the native Stacks helper credited in the source.

The two `SmallModel/Functoriality.lean` leaves retain the original chosen
Mathlib small-model equivalences at arbitrary small universe. Identity,
composition, and natural-isomorphism comparisons yield strict equations for the
existing canonical `smallKMap`, including degree zero.

## Native scheme continuation

The original target is `Quillen/AlgebraicGeometry/Scheme/Regular/GlobalComparison.lean`:
the canonical K-to-G map on a regular quasi-compact scheme with the ordinary
resolution property is an equivalence. No finite Krull-dimension hypothesis is
to be introduced.

The geometric continuation uses the existing native `Scheme.Vect` and
`AlgebraicGeometry.SheafOfModules.CoherentModules`, their ambient short exact
sequences, and literal `Scheme.Modules.restrictFunctor`. Native regular
coherent-perfectness and Stacks Tag 0F8E provide the bounded finite-locally-free
complex and actual map to the coherent single object. The separate
[native scheme slice](native-scheme-comparison.md) records the geometric instances,
canonical comparison, restriction functoriality and regular all-degree equivalence.

## Validation scope

The complete batch comprises twenty-two production modules and five regression
modules with forty-three examples. It passed strict native Lean 4.35 compilation
with its actual dependency closure. The focused final checks use all fifteen
native declaration linters and the official standard-three-axiom auditor at four
endpoint roots covering every new production module. Compiled checks verify all
public tags, citations and defining modules. All five regression modules were
re-elaborated. The unchanged native Mathlib TextBased functions checked every
Colib and ColibTest source; this is not a claim that the original text-lint CLI
was run locally. Python tests, catalog validation and source whitespace checks
also passed.

An independent source-level mathematical review covered the complete new proof
chain, original maps, connective indices, hypotheses, universes and pinned-source
correspondence. Source, compiler, actual imported artifacts and successful output
families are bound in private local records, not repository deliverables. These
focused checks do not constitute a local whole-repository `scripts/check.sh`
pass or an independent kernel replay. The unchanged original CI is the
whole-repository gate before publication to main. These earlier checks do not
cover the later scheme slice.

## Closed affine G-theory specialization

The [native finite-module localization slice](fraction-localization.md) is
independent of the larger regular-scheme dependency closure. It closes the
actual-target and small-model Serre sequence and the finite-module application
for any multiplicative set in a commutative Noetherian ring. It includes the
uniform-annihilator and principal-power support characterizations and the
homotopical G-zero tail. The original fraction-field map remains a literal
specialization. This is not a general scheme-open localization theorem.

The further [principal closed/open slice](principal-closed-localization.md)
identifies the actual quotient-ring G-theory with this principal supported term
by constructed finite image filtrations. Its closed pushforward remains the
original quotient-restriction smallKMap. This affine finite-module theorem does
not require the larger regular-scheme closure.
