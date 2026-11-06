# Canonical connective Serre localization

The canonical connective Serre localization theorem is now proved under the
original small abelian-category and Serre-class hypotheses. The actual based
fiber map is a weak homotopy equivalence; its group isomorphisms retain the
original forward maps. The full long exact sequence includes the actual
K₁-to-K₀ boundary and the terminal K-zero surjection. See `completion.md` for
precise statements, hypotheses, proof chain and limits.
The four complete public items and their native pipeline integration are
documented in `integration.md`.

The original baseline is Colib `a36cec736ab800767dde9eb0895d8afd18807931`;
the pinned Quillen source is `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Native Theorem B prerequisites, cartesian gluing and the complete all-component
Theorem B have been integrated as actual source, including the original
`4908146` and `a15b007` proof commits.

## Proved endpoints

- Every actual structured-comma transition of the canonical quotient Q-functor
  is a homotopy equivalence. The proof constructs the genuine auxiliary kernel
  equivalences, arbitrary-base-change equivalences, the ordinary-lift filtered
  diagram and its nerve colimit, and exact realized stage equivalences. Actual
  mono/epi natural transformations and fixed-target quotient Q-arrow lifting
  then prove every transition. No auxiliary comparison, colimit, or transition
  equivalence is supplied as an additional hypothesis. The source's conditional
  `E`/`hE` assembly interfaces are eliminated rather than imported as adapters.
- Ordinary Serre geometry uses native `Over`, kernels, pullbacks, pushouts,
  images and fraction calculi. The zero comma and isomorphism structured-comma
  inclusions have actual equivalences or Theorem A homotopy equivalences with
  their specified realized functors as forward maps. Lower Q-arrow classification
  retains actual span/cospan representatives and complete subobject endpoints.
- Arbitrary filtered realization invariance is proved for the original small
  filtered category, with no monicity, injectivity, sequentiality or countability
  assumption. Compact factorization and compact homotopy extension/lifting
  construct both inverse homotopies. The forward map is the realized cocone leg.

- The original Grothendieck-to-Quillen K-zero comparison is natural for exact
  functors, with the same zero-normalized `ExactFunctor.KMap`. In particular,
  the actual object loop maps to the loop of its image object. The proof tracks
  the original zero-object isomorphism, conjugation and equality of realized
  vertices; it does not define a substitute K-map by transporting algebraic maps.
- The actual inclusion and additive Serre localization are right exact on
  homotopical K-zero: the inclusion image equals the localization kernel, and
  the latter map is surjective. The general statement retains independent
  object and morphism universes `u` and `v`, shared by source and target as
  required by the current K-map. The canonical quotient specialization has
  the source's original `Category.{u} C` restriction.
- The actual quotient/inclusion composite has a categorical zero isomorphism,
  a realized nullhomotopy, and a zero-normalized nullhomotopy fixed at the
  original basepoint. The resulting continuous map into the original concrete
  path-space fiber is based. Projection of its homomorphism on every K-degree
  is exactly the original inclusion K-map. Quotient after inclusion is trivial
  in every degree by that based nullhomotopy.
- The normalized zero-structured-comma inclusion is a genuine homotopy
  equivalence with the specified forward map. Normalized transitions hold
  without an extra hypothesis. The costructured route equals the chosen based
  localization comparison strictly, and a jointly continuous two-parameter
  homotopy connects the structured route to it while fixing the original
  constant-path basepoint. The subsequent complete native Theorem B now proves
  that the original map into the homotopy fiber is a weak homotopy equivalence.
- The native path-space connecting homomorphism is instantiated for the actual
  normalized quotient. All three path-space exactness positions retain that
  quotient map and actual fiber projection. The proved comparison group
  isomorphism then transports this boundary to the actual K-group of the Serre
  subcategory, retaining its defining comparison equation and uniqueness.

The algebraic Stacks quotient was already present. The new K-zero result uses
its natural comparison with actual homotopical K-zero, including the proved
injectivity of the original comparison. It is not used as a substitute for a
higher-K fiber equivalence.

## Direct upstream reuse

Pinned Mathlib `16edf57de7933555826307a3d81b4391a3657a09` supplies
`HomotopyGroup`, `FundamentalGroup.mapOfEq`, `Iso.conj`, the localization category,
its quotient functor and the Serre quotient's abelian structure. Pinned Stacks
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6` supplies:

- `StacksCore.CategoryTheory.Abelian.SerreClass.Basic`: existing finite-product
  closure of a Serre class, used directly. No duplicate closure instance is added.
- `ObjectProperty.shortExact_map_ι` and
  `ObjectProperty.SerreClassLocalization.shortExact_map`: actual exact functors.
- `ObjectProperty.SerreClassLocalization.grothendieckGroupEquiv`, Stacks 02MX(1),
  through the already proved generator-preserving Colib comparison.

The exact inclusion, Q-construction, rebasing, realization, Grothendieck group,
K-groups and homotopy fiber retain their existing native owners. No historical
Aglib model or dependency is introduced. The small added lower lemmas are
naturality or constant-map statements on these same objects.

## Source correspondence

- `KTheory/GrothendieckComparison/Naturality.lean`: all eleven missing source
  declarations are retained under native owners. Existing `qObjectClass_comp`
  and `grothendieck_mulHom_ext` are reused, not copied. The original mathematical
  source is Weibel IV, Proposition 6.2 and its object-loop proof, page 54.
- `Localization/Serre/Localization.lean`: the original general and canonical
  Q-maps and K-maps are retained; algebraic declarations remain at their existing
  owners.
- `Localization/Serre/FiberComparison.lean` and `BasedFiberComparison.lean`:
  actual categorical, continuous and homotopy-group comparison maps are retained,
  with original basepoint tracks. Redundant normalized-functor abbreviations are
  replaced by the existing exact functors' `normalizedQ` expressions.
- `Localization/Serre/LocalizationLESAdapter.lean`: only its actual
  `fiberConnectingHom` is retained. Native homotopy-fiber exactness is used
  directly. Conditional comparison packages and assumed comparison equivalences
  are not imported or recreated.
- `Localization/Serre/LocalizationTheorem.lean`: `quotientKZero_surjective` and
  the degree-zero specialization of `inclusion_range_eq_quotient_ker` are proved
  by a different route through the now-proved natural K-zero comparison.
  The later direct geometric argument now closes `localizationSequence`,
  `localization_longExact` and the full `localization_KZero_tail`, including
  the K₁-to-K₀ boundary.

The completed literature scope is Weibel V, Theorem 5.1 and the connective
sequence (5.1.1), page 35. Earlier checkpoints covered only the K-zero tail
and the fiber construction; the complete geometric comparison is now proved.
The generic path-space LES is background from Weibel IV, Homotopy Fiber 1.2,
page 3. Our path coordinate retains the source convention from `f(x)` to the
basepoint, opposite to the displayed orientation in that paragraph. No new
comparison with a differently oriented boundary is asserted.

## Completed geometric and exact-sequence endpoints

`FiberEquivalence.lean` proves the actual based comparison on π₀ and all higher
homotopy groups, and the stronger all-component weak-equivalence property.
`LocalizationTheorem.lean` directly constructs the boundary and proves
`localizationSequence`, `localization_longExact` and `localization_KZero_tail`.
No geometric proof obligation remains for these canonical statements.
No global continuous homotopy inverse is claimed.

The source's conditional assembly interfaces remain eliminated. The native
Theorem A, arbitrary filtered realization, complete Theorem B and actual
homotopy-fiber LES are used with their already-proved hypotheses.

## Source and evidence groups

The subdirectories `ordinary-geometry`, `quotient-lifts`, `auxiliary-kernel`,
`comma-geometry`, `filtered-diagram`, `filtered-realization`,
`normalized-comparison` and `iso-coherence` retain the
workers' detailed source correspondences and bounded validation reports.
These document ordinary kernel geometry, quotient lifts, actual auxiliary
kernel/base-change homotopy equivalences, comma contractibility, the actual
filtered nerve colimit, and generic filtered realization respectively.
They are integrated as one proof line, not presented as separate completed
localization milestones.

## Validation boundary

The original integrated transition/coherence slice passed 119 strict source/test
compilations and an independent 6096-declaration standard-axiom audit. Those
source-bound results are retained locally as the earlier checkpoint.
The complete gluing/Theorem B and final Serre endpoints passed joint strict
compilation of 216 changed leaves: 199 production modules and 17 in-package
regression modules with 187 examples. The final source/output snapshot matches.
The native independent auditor checked 8587 declarations with only the three
standard axioms. Declaration lint of the localization endpoint's native import
environment, text lint, 82 Python tests and the existing 242-item catalog passed.
The detailed pre-registration validation, compiler and dependency bindings
are retained locally rather than included in the source repository.

The bounded independent reviews separately check the original maps, all-degree
range, hypotheses, exactness and stored build bindings. Compilation, source
correspondence, mathematical review and remote CI remain distinct.

The later main-library integration registers COL-0247 through COL-0250 and
regenerates the native root. Its original full `scripts/check.sh` run passed,
including 86 Python tests, all native tests, full declaration/text lint, the
12841-declaration standard-axiom audit and the native Library/site export.
See `integration.md` for the checked source snapshot and verification scope.
The retained metadata crosswalk preserves the reviewed proof bytes. Detailed
run logs and source/output bindings remain local; the full-package result is
not inferred from the earlier leaf check.
