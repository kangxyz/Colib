# Normalized Serre comparison and exact based coherence

## Result and boundary

The actual normalized target-zero comma comparison is a categorical equivalence and yields a
homotopy equivalence with exactly the normalized comparison functor as its forward map. Its
complete realized nullhomotopy and its map to the actual path-space homotopy fiber agree with
`basedLocalizationFiberComparison`, including every path-coordinate value.

The normalized **zero-structured-comma inclusion** is a homotopy equivalence with forward map
`classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)`. This is not a homotopy-equivalence
claim for the comparison into the homotopy fiber. For that comparison, this draft proves its
exact path-space lift formula and an actual jointly continuous two-parameter homotopy from the
existing based localization comparison. The homotopy fixes the source coordinate, has the exact
inverse-isomorphism triangle as its path coordinate, and fixes the original constant-path
basepoint for every homotopy and path parameter.

Every structured transition of the actual normalized quotient functor is a homotopy equivalence,
using the already proved `quotientStructuredTransitionHomotopyEquivalences P` directly.
No transition hypothesis is added to this Serre endpoint.

Exact zero-object, identity-structured-arrow and realized basepoint identities are included.
The source's common object/hom universe `u`, Abelian ambient category and Serre-class hypotheses
are unchanged. The generic coherence retains the source's jointly continuous families in every
simplex dimension. No homotopy-group degree restriction is introduced; no homotopy-group
bijectivity theorem is asserted.

There are no blockers for this assigned slice. The general structured-comma-to-homotopy-fiber
weak equivalence remains outside this slice, and no final Serre localization equivalence is
claimed. No conditional localization adapter or final conditional bijectivity wrapper is added.

## Production paths

All paths below are relative to their respective draft roots.

`output/serre-normalized-comparison-draft`:

1. `Colib/CategoryTheory/TheoremB/StructuredBasepoint.lean`
2. `Colib/KTheory/Quillen/Localization/Serre/NormalizedComma.lean`
3. `Colib/KTheory/Quillen/Localization/Serre/NormalizedStructuredComma.lean`
4. `Colib/KTheory/Quillen/Localization/Serre/NormalizedBasepoint.lean`

`output/serre-iso-coherence-draft`:

1. `Colib/Topology/ClassifyingSpace/Naturality.lean`
2. `Colib/CategoryTheory/TheoremB/Naturality.lean`
3. `Colib/Topology/ClassifyingSpace/FunctorChain.lean`
4. `Colib/Topology/ClassifyingSpace/InverseHomotopy.lean`
5. `Colib/Topology/HomotopyFiber/Nullhomotopy.lean`
6. `Colib/CategoryTheory/TheoremB/FunctorIso.lean`
7. `Colib/CategoryTheory/TheoremB/StructuredFunctorIso.lean`
8. `Colib/CategoryTheory/TheoremB/StructuredIsoHomotopy.lean`

The first list's `StructuredBasepoint` needs only existing `StructuredComparison`.
`NormalizedComma` needs the lower `ClassifyingSpace/Naturality`; the remaining Serre files need
the complete lower list and existing actual `StructuredTransitions`.

Generic natural-transformation and functor-chain constructions use `CategoryTheory`, actual
comma/fiber comparisons use `CategoryTheory.TheoremB`, the topological fiber-lift primitive
uses `Topology.HomotopyFiber`, and all Serre applications use
`CategoryTheory.ExactCategory.SerreLocalization`. No Aglib or parallel object model is imported.
The exact inclusion and quotient's existing `normalizedQ` expressions are used directly.

## Tests and validation

- `output/serre-normalized-comparison-draft/ColibTest/SerreNormalizedComparison.lean`:
  23 regression examples.
- `output/serre-iso-coherence-draft/ColibTest/Topology/SerreIsoCoherence.lean`:
  6 regression examples.
- Both complete owned production/test sets compile with pinned Lean 4.34.0-rc2,
  `autoImplicit=false`, `warningAsError=true` and `weak.linter.mathlibStandardSet=true`.
  Logs are each draft's `strict-build.log`.
- Audit commands are kept separately in each draft's `validation/Axioms.lean`, outside
  production and `ColibTest`, with separate `axiom-audit.log` outputs. Neither production nor
  regression files suppress the hash-command linter.
- All 21 printed endpoint dependencies contain only `propext`, `Classical.choice`, `Quot.sound`.
- Pinned Mathlib native text lint passed over all owned production/test files. Evidence:
  `serre-normalized-comparison-draft/text-style.log` and
  `serre-iso-coherence-draft/text-lint.log`.
- No placeholders, `native_decide`, new axioms, or Aglib/Quillen production imports.
- `integration-manifest.json` lists all twelve production and both test source paths and hashes.

These are leaf/regression compilation and endpoint-axiom checks, not a claim of running the
whole repository's `scripts/check.sh`, an independent mathematical review, kernel replay, or a
separate downstream-client build. Shared catalog IDs, root imports and publication are left to
the integrating parent. No git/index/catalog edits, cache copies, commits or pushes were made.

## Source correspondence

Pinned implementation source: the [Quillen K-theory repository](https://github.com/kangxyz/quillen-k-theory) at
`c561118b7795eb9780be9ed391c3251d6a4d0afd` (verified).

`source-correspondence.json` records all 34 declarations from source
`Localization/Serre/{NormalizedComma,NormalizedStructuredComma,StructuredComparisonWeak}`:
31 are retained, the normalized structured-transition endpoint is strengthened by consuming the
proved actual theorem, and three conditional wrappers are intentionally omitted:
`normalizedQuotient_transitions`, `structuredFiberComparison_bijective_of_eq`, and
`basedLocalizationFiberComparison_bijective_of_structured`.
Two explicit full-coordinate theorems are added for the comparison homotopy.

`../serre-iso-coherence-draft/SOURCE_CORRESPONDENCE.md` describes all generic source splits,
including `TheoremB/{Naturality,FunctorIso,StructuredFunctorIso,StructuredIsoHomotopy}` and
`Topology/ClassifyingSpace/FunctorChain`. Original copyright, license and authors are retained.
The original migration used a finite-coordinate comparison at the barycentric boundary.
The later native-coordinate rewrite removes that layer and uses `Convexity.StdSimplex` and
`SimplexCategory.toTopHomeo` directly, retaining the interval orientation against
`realizationInterval`. This report records the original validation scope.
