# Native simple-norm scalar base change: source assignment

This long-lived independent branch is `work/native-simple-norm-base-change`, based on
`8a90269409024c63ca7c5203fc8faea01915de0c`. It must not modify main or another worker's tree.

The mathematical target is scalar-factor base change for the existing Stacks `simpleMilnorNorm`.
The canonical source and target groups remain `MilnorKRing`; all quotient fields, residue maps,
and coefficient-factor maps remain the existing Stacks/Mathlib objects. No norm model, field
presentation wrapper, replacement residue, or tower-independence claim is introduced.

Pinned inputs:

- Stacks `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
  `StacksFrontier/AlgebraicGeometry/Chow/MilnorNorm/SimpleNorm.lean:146-205` and
  `SingleResidue.lean:205-210,319-331`.
- The same Stacks pin, `FullExactness.lean:115-120,173-190` and `ResidueSupport.lean:199-210`.
- Mathlib `16edf57de7933555826307a3d81b4391a3657a09`,
  `Mathlib/RingTheory/AdjoinRoot.lean:402-415`.
- The same Stacks pin, `AffineLineResidue.lean:101-126,144-169` and
  `PolyResidueRing.lean:104-115`, for the existing rational/local scalar towers and residue field.
- The same Mathlib pin, `FieldTheory/RatFunc/Basic.lean:368-387,553-575`,
  `RingTheory/Localization/AtPrime/Basic.lean:156-160,240-247`, and
  `RingTheory/LocalRing/ResidueField/Basic.lean:116-123`, for actual-map evaluation.
- The same Mathlib pin, `RingTheory/Multiplicity.lean:336-343` and
  `RingTheory/UniqueFactorizationDomain/Multiplicity.lean:44-48,106-110`, for full factor
  extraction and the identification with normalized-factor count.

The existing Library section is `k-theory / milnor-k-theory`. The parent integrator owns
permanent IDs, catalog entries, bibliography changes, root imports, and acceptance status.

Owned paths:

- `Colib/RingTheory/Polynomial/FactorContraction.lean`
- `Colib/KTheory/MilnorK/Norm/FiniteReciprocity.lean`
- `Colib/KTheory/MilnorK/Norm/ScalarFactorReduction.lean`
- `ColibTest/PolynomialFactorContraction.lean`
- `ColibTest/MilnorFiniteReciprocity.lean`
- `ColibTest/MilnorScalarFactorReduction.lean`
- `Colib/FieldTheory/RatFunc/CoefficientMap.lean`
- `Colib/RingTheory/AdjoinRoot/Map.lean`
- `Colib/RingTheory/Polynomial/FactorMultiplicity.lean`
- `Colib/KTheory/MilnorK/Norm/CoefficientResidueFields.lean`
- `ColibTest/RatFuncCoefficientMap.lean`
- `ColibTest/PolynomialFactorMultiplicity.lean`
- `ColibTest/MilnorCoefficientResidueFields.lean`
- `SCALAR_BASE_CHANGE_SCOPE.md`
- `SCALAR_BASE_CHANGE_REPORT.md`
- `SCALAR_BASE_CHANGE_SOURCE_RECEIPT.json`

The unconditional finite reciprocity proof is the first deliverable. A separate, explicitly
conditional single-lift reduction records how the missing finite-place and infinity comparison
equations imply scalar-factor base change. It must not be reported as an unconditional
base-change theorem. Exact remaining interfaces belong in the report, not as axioms or placeholders.

## Finite-reciprocity consolidation

This branch owns the single generic lift/exactness proof in
`Colib/KTheory/MilnorK/Norm/FiniteReciprocity.lean`. The sigma-index reciprocity and finite-support
existence statements are derived from it, not independently reproved. Its prescribed-residue
interface remains unchanged for `ScalarFactorReduction.lean`.

The earlier `norm-finite-reciprocity-20261105T1451/FiniteReciprocity.lean` and
`FiniteReciprocityTest.lean` are historical source drafts, not a second production implementation.
Their useful corollaries and six degree/sign regression consumers are consolidated into the
canonical files above. The old files and their static review are not edited by this branch.

After the pinned native SimpleNorm dependency closure is ready, the norm validation owner will
perform the first actual compilation of these canonical modules and tests. This branch supplies
source checks and exact hashes only; it does not claim that the merged declarations elaborate.

## Actual coefficient maps and multiplicities

The next source-only milestone supplies actual rational/local coefficient squares, the
polynomial-quotient/residue-field dictionary, and the local uniformizer equation with the native
`multiplicity` exponent. Four new production leaves contain eleven supporting theorem bodies,
and three new test leaves contain eleven consumers. No new map or mathematical model is defined.

These equations use independent source and target universes, no separability or characteristic
hypothesis, and the pinned native objects throughout. They fill the source implementations of
obligations A-C in the report. Elaboration remains unchecked. The actual Milnor residue equation,
image-support argument, infinity naturality, and final simple-norm scalar-factor formula remain
outstanding, so neither the existing conditional reduction nor this milestone is a completed
base-change theorem.

This assignment is source-only: no Lean/Lake commands, no guard acquisition, no shared cache
writes, no main edits, no pin changes, and no push. Compilation, tests, native lint, and axiom
audits remain unperformed until separately authorized.
