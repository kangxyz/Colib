# Native Milnor K₂ to the stable Steinberg kernel

## Scope and source

The target comparison remains
`Quillen/KTheory/Field/MilnorKTwoEquivalence.lean` at Quillen revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The destination baseline is Colib
`b8e84085dbffe3f35bbe116661194d0c62cc56d7`, tree
`99bd3a42fa4aebe8023e1c00891b595237b8310d`, with unchanged Mathlib and Stacks pins.
Original Quillen authorship and Apache-2.0 notices are retained in adapted files.

Library item `COL-0255` records the actual algebraic first map used by that comparison:

`StableSteinberg.milnorToKernel F : MilnorKTheory F 2 →+ Additive (toElementary F).ker`.

It does **not** prove the Milnor-to-Quillen K₂ equivalence. No theorem in the
named final comparison module is marked migrated by this slice.

## Native interfaces audited

- Mathlib `Matrix.GeneralLinearGroup n R` is the existing unit group of square
  matrices, including rank zero and noncommutative coefficient rings. Its
  commutative-ring coefficient map does not cover the source's arbitrary-ring
  scope. The latter uses native `Units.map` and `RingHom.mapMatrix` directly.
- Mathlib `Matrix.transvection` supplies `1 + single i j a` over commutative
  rings. The required arbitrary-ring elementary unit is constructed in the
  native general linear group with inverse coefficient `-a`. There is no new
  underlying matrix type or second matrix-valued elementary definition.
- Mathlib `DirectLimit` supplies the actual quotient for stable matrices, its
  equality criterion, injective finite-stage inclusions and compatible lifts.
- Mathlib `PresentedGroup` supplies the actual quotient for finite-rank-labelled
  Steinberg roots. The selected relations are root addition, disjoint
  commutation, ordered chain commutators and standard stabilization. No
  separate countably indexed presentation or comparison adapter is introduced.
- Mathlib `Group.IsPerfect`, subgroup centers, commutators and
  `AddMonoidHom.noncommPiCoprod` supply the group-theoretic interfaces.
- Stacks `MilnorKTheory` is used unchanged. Colib's existing
  `IsMilnorKSymbolMap.lift` descends directly through the native homogeneous
  quotient. `milnorKTheoryMap_eq_transport` identifies common-universe field
  change with the literal Stacks `milnorKTransport`.

The pinned group and matrix sources contain no existing stable Steinberg group,
stable general linear group or Matsumoto K₂ comparison. The native Coxeter-group
mention of Matsumoto concerns reduced words, not this algebraic K₂ statement.
The Stacks Steinberg-symbol/residue interfaces do not supply the missing
stable-fiber-to-Quillen map.

## Source correspondence

| Source owner at the pinned revision | Destination and disposition |
| --- | --- |
| `Quillen/Aglib/LinearAlgebra/Matrix/Elementary.lean` | `Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary`: native units, ordered noncommutative commutator relation, finite elementary subgroup and precise spare-index perfectness. Source `matrix` is the literal native matrix expression; source `map`, `map_id` and `map_comp` are replaced by native `Units.map`, not copied as a parallel API. |
| `Quillen/Aglib/LinearAlgebra/Matrix/GeneralLinearGroup/Stabilization.lean` | `Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization`: same block stabilization, transitions, entry formulas, injectivity and arbitrary-ring coefficient squares. Source `GL` is replaced by the existing `Matrix.GeneralLinearGroup`. |
| `Quillen/Algebra/Group/StableGeneralLinear.lean` | `Colib.GroupTheory.StableGeneralLinear.Basic`: the same native directed limit, finite representatives, lift property and actual coefficient map. |
| `Quillen/Algebra/Group/StableElementary.lean` | `Colib.GroupTheory.StableGeneralLinear.Elementary`: generated subgroup, stabilization, perfectness, inclusion in the commutator and coefficient-map preservation. Whitehead's reverse inclusion, normality and the later consequences remain unresolved. |
| `Quillen/Algebra/Group/StableSteinberg.lean` | `Colib.GroupTheory.Steinberg.Basic` and `.Matrix`: all four actual relations, generator commutators, perfectness, canonical matrix map, corestriction and surjectivity. |
| `Quillen/Algebra/Group/StableSteinbergNaturality.lean` | `Colib.GroupTheory.Steinberg.Map`: coefficient maps, identity/composition and both actual matrix/elementary squares. |
| `Quillen/Algebra/Group/StableSteinbergCentrality.lean` | `Colib.GroupTheory.Steinberg.Centrality`: finite-stage exhaustion, fresh row/column products, actual matrix actions and centrality of the actual kernel. |
| `Quillen/Algebra/Group/StableSteinbergTorus.lean` | `Colib.GroupTheory.Steinberg.Torus`: same ordered Weyl/torus words, literal rank-two representatives, kernel-valued defect and coefficient naturality. |
| `Quillen/Algebra/Group/StableSteinbergSymbols.lean` | Group calculations are in `Colib.GroupTheory.Steinberg.Symbols`; the Milnor boundary is rewritten in `Colib.KTheory.MilnorK.Steinberg`. Source `torusSymbolMap` is replaced by the existing native symbol-map property, and source `twoEquiv`/pair-quotient transport is eliminated. All other source mathematical conclusions are retained, including the positive rank-three commutator marking. |

This is a bounded source correspondence, not a compiled declaration census of
the entire historical repository. Public and supporting group calculations are
retained in their mathematical owners. The coefficient hypotheses remain
arbitrary rings for stable matrices and every field for the Steinberg/Milnor
construction, including fields of characteristic two and three.

## Canonical generator, sign and map equations

- `toStableGeneralLinear_x` sends the actual finite root to the stable image of
  its native elementary unit, with the same rank, row, column and coefficient.
- `milnorToKernel_pair` sends `milnorKTupleSymbol ![a, b]` to
  `Additive.ofMul (torusDefectKernel a b)`.
- That kernel element is literally `h(a) * h(b) * h(a*b)⁻¹`.
- `commutator_h_h02` identifies the same ordered defect with the **positive**
  rank-three torus commutator. It is not its inverse or a swapped symbol.
- `milnorToKernel_naturality` is the square for the actual coefficient-induced
  kernel map. `milnorToKernel_naturality_transport` has the literal pinned
  Stacks transport on the Milnor side in a common universe.

## Remaining endpoint obligations

1. Algebraic kernel generation and Matsumoto injectivity are still open:
   `StableSteinbergKernelGeneration.lean`, the rank-two/Bruhat dependencies and
   `StableSteinberg/Matsumoto/Injectivity.lean`, in particular
   `milnorToKernel_injective_charZero`. Centrality alone is not an isomorphism.
2. The native stable completion and its homotopy fiber have not been constructed
   here. `SteinbergFiberComparison.steinbergKernelToRightProjectiveKTwo` must
   retain the original fiber boundary, its inverse-on-kernel construction,
   basepoint path and exact-structure Quillen K₂ target.
3. Fiber perfectness, the actual kernel-map injectivity and surjectivity, and
   their field-change squares remain required. No generic supplied comparison
   or assumed bijection replaces these results.
4. The finite-projective right-module and upper finite-module exact models,
   scalar-extension functors and their actual comparison still need the source
   correspondences used by `MilnorKTwoComparison.lean`.
5. `PositiveSymbolMarking.lean` must identify the original upper-model scalar
   unit product. The final characteristic-zero equivalences must use the
   original forward composite, and the negative normalization must remain
   minus its inverse. No positive-characteristic equivalence is inferred.

## Validation boundary

The new production modules and `ColibTest.SteinbergMilnor` are checked with the
pinned Lean toolchain, single-threaded, with `autoImplicit=false`,
`warningAsError=true` and Mathlib's standard source linters. The tests include
noncommutative coefficient order, rank zero, both perfectness instances, actual
surjectivity and centrality, ordered symbols, the Steinberg relation, positive
commutator marking and both naturality formulations.

Full default declaration lint and the pinned native text linters pass. The pinned independent axiom auditor checks
462 imported Colib declarations and allows only `propext`, `Classical.choice` and
`Quot.sound`. Native generated-entry checking and Library metadata checks pass.
A full aggregate `scripts/check.sh` is an integration check and is not inferred
from focused module compilation. No separate client check or kernel replay is
claimed.
