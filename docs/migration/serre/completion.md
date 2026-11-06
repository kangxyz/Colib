# Complete canonical connective Serre localization

## Proven statement and actual hypotheses

Let `C : Type u` have `Category.{u} C` and `Abelian C`, and let
`P : ObjectProperty C` satisfy `P.IsSerreClass`. These are the original common
object/hom universe and Serre-class hypotheses. No Noetherian, finite-length,
filtration, comparison-equivalence, quotient-comparison or cartesian-square
hypothesis is added.

The original based continuous map `basedLocalizationFiberComparison P` into
the concrete fiber of the actual normalized quotient map is proved to be a
weak homotopy equivalence. Its native property explicitly includes surjectivity
on path components and bijectivity at every source basepoint in every finite
homotopy degree, including zero. At the original constant-path basepoint,
`basedLocalizationFiberComparison_bijective P n` is the original induced
`HomotopyGroup.map`, for every `n : ℕ`.

`localizationFiberEquiv P n` is `MulEquiv.ofBijective` of the existing
`localizationFiberComparisonHom P n`; its forward homomorphism is definitionally
unchanged. No global continuous homotopy inverse is asserted or required.

## Canonical boundary and full sequence

The boundary `connectingHom P n` is the native path-space connecting
homomorphism followed by the inverse of that proved group isomorphism. The
identity `comparison_comp_connectingHom` fixes this interpretation at every
degree, including `K₁(C/P) → K₀(P)`. The theorem `connecting_unique` shows that
this equation uniquely determines the boundary.

The original maps `Abelian.Devissage.KMap P n` and `quotientKMap P n` satisfy:

- Inclusion image equals quotient kernel at `Kₙ(C)` for every `n ≥ 0`.
- Quotient image equals boundary kernel at `Kₙ₊₁(C/P)` for every `n ≥ 0`.
- Boundary image equals inclusion kernel at `Kₙ(P)` for every `n ≥ 0`.
- The canonical map to `K₀(C/P)` is surjective.

`localizationSequence`, `localization_longExact` and `localization_KZero_tail`
state the complete canonical connective theorem. The sequence bundle fixes
inclusion and quotient to these original maps; it is not a second K-theory
model or a conditional comparison interface.

The last surjection reuses the previously proved unconditional
`quotientKZero_surjective`, whose proof uses the natural Grothendieck-to-Quillen
comparison. This does not supply or replace any higher homotopy assertion:
the actual fiber comparison is independently proved by native Theorem B.
The source's alternative geometric proof of the same terminal surjection is
not duplicated.

## Direct proof chain

1. Actual ordinary quotient lifts, kernel/base-change functors and their
   Theorem A equivalences construct the genuine auxiliary diagram.
2. Whole-arrow lifting, equality refinement and faithful cocone legs prove
   its actual filtered nerve colimit.
3. Arbitrary filtered realization, with no monicity or countability assumption,
   constructs the exact cocone-leg homotopy equivalences.
4. Actual mono/epi squares and quotient Q-span lifting prove every structured
   transition of the canonical quotient, and its zero normalization.
5. The completed native Theorem B applies to these proved transitions. The
   normalized zero-structured-comma inclusion and the full two-parameter
   homotopy transport the conclusion to the original based fiber map.
6. The original native homotopy-fiber LES and the actual group comparison
   give the three exactness positions and the specified boundary.

No conditional `LocalizationLESAdapter`, `localizationSequenceOfComparison`,
`localizationFiberEquivOfBijective` or final `_of_structured` interface is
introduced. Each geometric conclusion is discharged before its use.

## Source correspondence and validation boundary

Implementation source: Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`,
`Localization/Serre/LocalizationTheorem.lean`, with its actual-map arguments
from `StructuredComparisonWeak`, `LocalizationEndpoint` and
`LocalizationLESAdapter`. Native owners replace historical Aglib names;
Mathlib restricted spans, realization, quotient and full subcategory remain
unchanged. The literature scope is Weibel, K-book V, Theorem 5.1, page 35.

The accompanying validation record binds the exact source and compiled
artifacts, strict compiler options, regression clients and independent axiom
closure. Library registration, generated-root checks and remote CI are separate
integration steps and must not be inferred from leaf compilation.
Their subsequent main-library integration is documented in `integration.md`.

Earlier per-slice documents in this directory are historical validation and
source-correspondence snapshots. Their former open-Theorem-B/localization
limitations are superseded by this completed proof, not by added hypotheses.
