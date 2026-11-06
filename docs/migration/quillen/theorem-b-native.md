# Native Quillen Theorem B

## Source and exact scope

Implementation source: `quillen-k-theory` commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The initial native baseline was `a36cec736ab800767dde9eb0895d8afd18807931`.
The genuine gluing continuation uses the integrated Serre baseline `580e808`;
the complete theorem continuation starts from `4908146`.

The original **transition homotopy-equivalence** form of Theorem B is proved:
for every target object, the actual comma-to-homotopy-fiber comparison is a
complete weak homotopy equivalence. The statement includes surjectivity on
all path components, independently of the existence of a source point, and
bijections on the actual based homotopy sets in every finite degree.

Both costructured and structured conventions are covered. The comma categories
remain Mathlib `CostructuredArrow` and `StructuredArrow`; realization and the
simplicial replacement remain the existing native `SSet` and
`CategoryTheory.TheoremA` constructions. Fibers are the actual compact-open
`Topology.HomotopyFiber`, whose paths run from the image of a source point to
the specified target point. No alternate comparison or realization is used.

This slice does not assert a chosen global continuous homotopy inverse for the
final fiber comparison. It does not claim the more general weak-transition
variant of the pinned source, nor the final Serre localization application.
It supplies the original Theorem B input needed for that application.

## Final native endpoints

- `CategoryTheory.TheoremB.fiberComparison_isWeakHomotopyEquivalence`
  assumes only `TransitionHomotopyEquivalences F` and applies to every `d : D`.
- `CategoryTheory.TheoremB.structuredFiberComparison_isWeakHomotopyEquivalence`
  assumes only `StructuredTransitionHomotopyEquivalences F` and also applies
  to every target object.
- The resulting `Topology.IsWeakHomotopyEquivalence` has two explicit fields:
  `component_surjective`, giving actual joining paths for every target point,
  and `homotopy_bijective`, giving bijectivity of `HomotopyGroup.map` at every
  source point and every `n : ℕ`. The component field prevents an empty
  source from vacuously satisfying the conclusion over a nonempty target.
- `fiberComparison_bijective` and `structuredFiberComparison_bijective`
  identify the canonical identity-arrow basepoints exactly, including degree
  zero. Their positive-degree `fiberComparisonPiEquiv` and
  `structuredFiberComparisonPiEquiv` use the actual canonical `piMap` as
  forward homomorphism, with explicit coercion equalities.

No finite-stage, final-comparison, or domain-descent hypothesis remains at
these endpoints. Conditional geometric helpers have their hypotheses
explicitly discharged by the final proofs.

## Proof chain

### Native row and initial-stage geometry

The initial slice establishes the specified comma comparisons, transition
rows and prisms, enriched product comparisons, boundary-to-cell squares,
and actual first-stage coproduct coordinates. The stage-one vertex square
works for an arbitrary coefficient transformation. Existing native
constant-nerve-skeleton facts are reused rather than copied.

### Genuine cartesian gluing

`TopCat.CartesianPushout.leftHomotopyEquiv` and `rightHomotopyEquiv` prove
that two incoming canonical homotopy-pullback equivalences in a commuting
pushout cube, with HEP for corresponding legs, give both outgoing
comparisons. `TopCat.CartesianDomainPushout.homotopyEquiv` assembles three
corner comparisons into one fixed target across actual source/base pushouts.
Each constructed equivalence retains its exact prescribed `toFun`.

The proof uses genuine double mapping cylinders, explicit collar/product
charts, homotopy-equivalent collapses, and weak lifting for fibrational
spans derived from local fibrations and overlap equivalences. Functorial
mapping-path replacement supplies the needed fibrations. Ordinary pushout
invariance is used only where all three required equivalences are proved.

Canonical cylinder constructors and `Topology.HomotopyPullback.baseMapCongr`
were extracted from source `Topology/HomotopyPullback/Pushout.lean` into
lower owners. The gluing layer has no Theorem A/B dependency or duplicate
fiber/realization model.

### Simultaneous finite-stage induction

Actual characteristic charts satisfy exact simplex-operator and coefficient
naturality equations. Finite-dimensional domain descent proves their
boundary restrictions. These assemble into both incoming faces of the
replacement successor cube. Its two outgoing conclusions simultaneously
propagate old-stage and new-cell charts.

The induction starts at the empty skeleton and proves
`CategoryTheory.TheoremB.Skeletal.stageCharts`,
`stageRestrictionCartesian`, and `stageComparisonHomotopyEquiv` from the
original transition homotopy-equivalence hypothesis alone. The last
comparison has its exact canonical forward-map theorem.

`stageCartesian_of_restrictionCartesian` was moved from source
`SkeletalCartesianCoordinates.lean` into native `SkeletalCartesianInduction`
to keep the chart geometry independent of compact sequential machinery.
The low `ReplacementProjectionTower` extraction avoids a dependency cycle
with vertex assembly.

### Compact passage and canonical transport

`Topology.HomotopyPullback.Sequential.compact_factors` factors entire compact
families of paths, not only individual points. Relative homotopies factor
as well. Finite-stage equivalences then prove all-degree bijectivity of the
actual stage-to-colimit comparison. Testing with a constant map from
`PUnit` separately proves component surjectivity without any nonempty-source
hypothesis.

The first-stage base is discrete. Restriction to its actual strict fibers
therefore preserves complete weakness; the comparison homotopy places a
lifted component in the correct fiber even in degree zero. The resulting
vertex comparison is transported through the actual diagonal-to-resolution
and resolution fiber equivalences.

Structured transport uses the existing opposite-comma equivalence and the
explicit reversal homotopy. Identity basepoints are verified exactly.
For arbitrary basepoints, homotopy invariance is proved directly by currying
the actual homotopy into the compact-open free path space. Both endpoint
evaluations are genuine homotopy equivalences; cancelling the initial map
and composing the final one proves every-degree bijectivity. Component
surjectivity follows along the actual reversed pointwise homotopy path.
This native proof avoids importing a stronger weak-fiber criterion.

## Validation and remaining integration work

The three focused slices have the following validation scopes:

- Initial prerequisites: 30 production leaves, eight regression examples,
  ten endpoint axiom reports.
- Genuine gluing: 55 new production leaves, ten regression examples,
  18 endpoint axiom reports.
- Complete original theorem: 35 new production leaves, 18 regression
  examples in two test modules, and 22 endpoint axiom reports.

Strict compilation uses `autoImplicit=false`, `warningAsError=true`, and
`weak.linter.mathlibStandardSet=true`. Isolated validation records bind
sources and direct-import artifacts by SHA-256. Principal endpoint axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

A separate read-only mathematical/source review checks the final strong
route, exact maps, component handling, and the new free-path homotopy proof.
The endpoint import closure is acyclic and contains no weak-transition
induction, placeholder, or added axiom. This review is distinct from kernel
compilation and from the repository integration pipeline.

There is no remaining mathematical gap in the stated original strong
Theorem B endpoints. Generated roots, catalog/export coverage, the complete
`scripts/check.sh` pipeline, and the combined revision's production audit
remain integration steps on the current main branch.
