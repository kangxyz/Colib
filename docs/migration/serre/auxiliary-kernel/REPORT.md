# Genuine Serre auxiliary-kernel comparison

Source: Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Target baseline: `a36cec736ab800767dde9eb0895d8afd18807931`.

## Delivered mathematics

The actual restricted-span category over an ambient object and its kernel Q-functor are constructed. The target uses the intrinsic abelian exact structure on `P.FullSubcategory`; the actual native fully faithful Devissage Q-inclusion lifts its maps.

The epimorphic kernel comma is reflected into the surjective-kernel full subcategory via ordinary kernel pushouts. That subcategory has a constructed initial object. Native Theorem A proves `epiAuxiliaryKernelClassifyingHomotopyEquiv`.

The image-poset reduction contracts every full auxiliary-kernel comma. Native Theorem A proves `auxiliaryKernelClassifyingHomotopyEquiv`. Arbitrary base change naturally preserves the kernel functor and hence gives `auxiliaryBaseChangeClassifyingHomotopyEquiv`.

Every equivalence has a theorem identifying `toFun` with the classifying-space map of the actual stated functor. None accepts a comparison-equivalence hypothesis. No alternate Q-category, realization, K-model, or adapter package is added.

## Files and ownership

Eleven modules under `Colib/KTheory/Quillen/Localization/Serre/` retain source basenames: AuxiliaryKernel, OverQArrows, KernelPushout, KernelPushoutComparison, KernelPushoutExistence, KernelPushoutUniqueness, KernelReflection, AuxiliaryImages, AuxiliaryBaseChange, ImageKernelComma, AuxiliaryBaseChangeEquivalence.

Namespace: `CategoryTheory.ExactCategory.SerreLocalization`.

The generic factor-contraction theorem is in `Colib/Topology/ClassifyingSpace/FactorContraction.lean`, namespace `CategoryTheory`.

The ordinary geometry dependency is the separately proved `serre-kernel-geometry-draft` overlay. Q-abelian spans and Theorem A use baseline native owners. Two former bicartesian-helper calls use the actual Stacks 08N4 `CommSq.IsPushout.mono_to_isPullback` / `CommSq.IsPullback.epi_to_isPushout`, with square flips rather than wrapper lemmas.

`declaration-map.json` records 117 source declaration correspondences. Production has no Quillen/Aglib imports or source namespaces.

## Validation

All twelve modules compiled serially with `-DautoImplicit=false -DwarningAsError=true`. `ColibTest/SerreAuxiliaryKernel.lean` checks the intrinsic target type and exact functor-map identities. Axiom output for the three homotopy equivalences and the strict inclusion equation consists only of `propext`, `Classical.choice`, `Quot.sound`.

These are author source-correspondence and Lean compilation results, not an independent mathematical review. They prove the actual auxiliary-kernel homotopy comparisons, not by themselves the final higher-K Serre localization fiber sequence or long exact sequence.

## Integration notes

Do not copy the artifact overlay into production: it contains symlinked prerequisites. Integrate owned Lean sources and test. `build.sh` uses the mandatory serial Lean wrapper. Parent owns Library/catalog integration. The generic span-naturality lemma was extracted by the parent to `Colib/CategoryTheory/QConstruction/Abelian/SpanNaturality.lean`; AuxiliaryBaseChange imports that lower owner.
