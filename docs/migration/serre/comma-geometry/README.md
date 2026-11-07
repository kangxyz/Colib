# Native Serre comma geometry

## Source and scope

Source: `Quillen/Localization/Serre/LocalizationComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Baseline: published Colib `a36cec736ab800767dde9eb0895d8afd18807931`,
using completed native additions in `../serre-kzero-native-a36cec7` and
`../serre-quotient-lifts-draft`.

This isolated overlay supplies 64 source-corresponding declarations:

- Source line 57: generic join-semilattice classifying-space contraction,
  under `Colib/Topology/ClassifyingSpace/Semilattice.lean`.
- Source line 81: the source of an exact Q-arrow to an original zero object
  is itself an original zero object, under
  `Colib/CategoryTheory/QConstruction/ZeroSource.lean`.
- Source lines 431–524 and 568–1003: 62 declarations under
  `Colib/KTheory/Quillen/Localization/Serre/LocalizationComma.lean`, in the
  native namespace `CategoryTheory.ExactCategory.SerreLocalization`.

The complete declaration mapping is `source-correspondence.tsv`.

The result includes the actual target-zero comma equivalence, its strict
projection to the Q-inclusion, the source-zero layer-lift equivalence and
contractible comma fibers, the general isomorphism-object comma-fiber
interval equivalence and contractibility, and genuine native Theorem A
homotopy equivalences. The prescribed realized inclusion maps are the
forward maps by definitional equality. It adds no Theorem B transition
hypothesis and assumes no localization equivalence.

The generic Q-arrow invariants in source lines 96–420 are consumed directly
from the previously compiled native `QConstruction/Abelian/ArrowLayers`.
The three Theorem B-dependent declarations in source lines 527–566
(`serreToZeroComma_transformation`, `serreToZeroComma_nullhomotopy`,
`serreToZeroComma_fiberComparison`) are deliberately not included.

## Verification

`/tmp/serre-comma-compile.sh` compiles owned leaves using the existing serial
Lean wrapper and lock, with `autoImplicit=false`, `warningAsError=true`,
and `weak.linter.mathlibStandardSet=true`. The overlay links inherited build
artifacts; it does not duplicate dependency caches.

The final invocation compiles all three production leaves, the 22 regression
examples in `ColibTest/SerreCommaGeometry.lean`, and the ten endpoint axiom
checks in `CheckAxioms.lean`. Evidence is `final-validation.log`. All reported
endpoint closures use only `propext`, `Classical.choice` and `Quot.sound`.
The scratch axiom file disables only the hash-command linter to permit
`#print axioms`; production and regression sources have no linter disables.

No shared repository, catalog, permanent ID, root import or git changes were
made. Full package/catalog integration checks remain the integrator's step.
