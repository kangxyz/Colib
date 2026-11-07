# The canonical Milnor–Quillen K₂ comparison

## Source and status

The completed source chain adapts
[`Quillen/KTheory/Field/MilnorKTwoEquivalence.lean`](https://github.com/kangxyz/quillen-k-theory/blob/c561118b7795eb9780be9ed391c3251d6a4d0afd/Quillen/KTheory/Field/MilnorKTwoEquivalence.lean)
and [`PositiveSymbolMarking.lean`](https://github.com/kangxyz/quillen-k-theory/blob/c561118b7795eb9780be9ed391c3251d6a4d0afd/Quillen/KTheory/Field/PositiveSymbolMarking.lean)
at Quillen revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Original attribution and Apache-2.0 notices are retained in adapted sources.

Library item COL-0262 records the endpoint in
`Colib.KTheory.MilnorK.QuillenEquivalence`. Its final annotated source and
regression have passed strict compilation and focused native checks on the
rebuilt native-coordinate closure. Original whole-library verification remains
pending for this integrated candidate; the local result does not discharge it.

## Exact hypotheses, objects and maps

For `F : Type u` with `[Field F] [CharZero F]`, the source defines:

- `MilnorKTheory.rightProjectiveKTwoEquivCharZero F`, from the unchanged Stacks
  `MilnorKTheory F 2` to
  `Additive ((ModuleCat.FiniteProjective.exactStructure.{u,u} Fᵐᵒᵖ).K 2)`.
- `MilnorKTheory.upperModuleKTwoEquivCharZero F`, with the same domain and
  literal target
  `Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u+1} 2)`.

Both use `AddEquiv.ofBijective` on the existing homomorphisms
`toRightProjectiveKTwo F` and `toUpperModuleKTwo F`; their forward-homomorphism
identities are `rfl`. The first map is native `StableSteinberg.milnorToKernel`
followed by `steinbergKernelToRightProjectiveKTwo`. The upper map then uses the
actual projective inclusion, opposite-ring restriction and existing upper
SmallModel/common-ambient comparison. The target K-groups remain the realized
Q-construction groups, not a presentation chosen to make the comparison hold.

[Kernel generation](field-k2-kernel-generation.md),
[native Matsumoto injectivity](matsumoto-native-injectivity.md), and the
[stable-fiber proof](field-k2-stable-fiber.md) supply the inputs. Fiber
perfectness is proved for every ring; the original Steinberg-kernel-to-K₂ map's
injectivity and surjectivity are proved over every field. No perfectness,
generation, detector-law or comparison-isomorphism premise is added to the
final theorem. The Milnor equivalences retain the pinned characteristic-zero
hypothesis. No positive-characteristic bijectivity claim is made.

## Ordered product and negative normalization

For every field, without a characteristic-zero assumption,
`MilnorKTheory.toUpperModuleKTwo_pair_eq_unitProduct` proves

`toUpperModuleKTwo F (milnorKTupleSymbol ![a, b]) = Additive.ofMul (FGModuleCat.FieldSymbols.unitProduct F a b)`.

Here `unitProduct F a b` is the original scalar identity-homotopy action of
`a` on `positiveUnitKOne F b`, which is defined by the inverse of the actual
finite-module determinant equivalence. Neither the product nor the action is
defined through the Milnor equivalence. The ordered kernel word remains
`h(a) * h(b) * h(a*b)⁻¹`, with its positive rank-three commutator marking.
The scalar-cube and connecting-sweep inversions cancel, without swapping `a`
and `b` or discarding the moving vertex track.

In characteristic zero, `upperModuleKTwoEquivCharZero_pair` gives that same
ordered product. `upperModuleKTwoNegativeEquivCharZero` is literally
`(upperModuleKTwoEquivCharZero F).symm.trans (AddEquiv.neg _)`.
It sends the actual positive `unitProduct F a b` to
`-milnorKTupleSymbol ![a, b]`; its inverse is minus the original forward map.

## Field change in both directions

For `F L : Type u` and `f : F →+* L`, the original forward squares use
`(ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap 2` and
`(FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u+1} 2`.
They are proved for arbitrary fields in
`Colib.KTheory.MilnorK.QuillenNaturality`. In this common universe, the native
Milnor map agrees with the existing Stacks transport.

When both fields have characteristic zero, the final comparison proves these
squares for each equivalence and its inverse, and for the negative
normalization in both directions. The inverses are those of the same
positive equivalences, not newly chosen field-change maps. No broader universe
range is inferred for these Quillen field-change endpoints.

## Native coordinate ownership

The coordinate source set uses native function-subtype `stdSimplex`, its
boundary and `SimplexCategory.toTopHomeo` directly. It preserves the actual
realization cylinder/product comparisons, ordered triangle edges, parameter
reversals and full natural-transformation tracks. There is no finite
Finsupp-to-function conversion layer or parallel simplex model.

`FiniteSimplexAdapter.lean` and the duplicate realization
`SimplexBoundary.lean` and `SimplexHomotopy.lean` owners are retired. The actual
native boundary, retraction, homotopy extension and path-homotopy owners remain
under `Colib.Analysis.Convex.StdSimplex`. The substantive
`Colib.Topology.Realization.SimplexBoundary` directory family also remains,
using native coordinates directly. The adapter item `COL-0059` is retired
permanently, never reused; `COL-0082` and `COL-0098` retain their identities with
updated native interfaces.

The metric order complex retains its genuine arbitrary-support Finsupp/L1
object, `chainCoordinates`, and pushforward, support, vertex, composition and
injectivity results. Only the obsolete finite helpers
`continuous_chainCoordinates` and `chainCoordinatesMap` are retired. Their
removal adds no compatibility alias and is not an assertion that every
arbitrary-index helper has a finite native replacement.

## Verification boundary

- The general-field positive marking and ordinary
  `ColibTest.PositiveSymbolMarking` regression have frozen strict compilation,
  native text/declaration lint and axiom-audit evidence. Regression coverage
  includes `ZMod 5`, literal scalar/tensor maps, coordinate order and a genuinely
  moving vertex. Its proof closure uses only `propext`, `Classical.choice` and
  `Quot.sound`.
- A focused independent source review checked the final comparison's
  hypotheses, literal maps, ordered marking, signs and both field-change
  directions. It found no mismatch in that reviewed scope. This is not an
  exhaustive review of every lower dependency or a compilation result.
- The final characteristic-zero production endpoint and ordinary regression
  passed strict compilation, native text/declaration lint and a production
  axiom audit on the 1,285-module native coordinate closure. Its 22,130 audited
  declarations use only the three standard axioms. The final annotated
  production sources were checked again; compiled metadata contains all
  15 COL-0262 bindings with their precise Quillen references and no COL-0059.
- The original repository-wide build, all tests, native lint, generated-entry,
  axiom and Library checks remain pending. The unchanged CI workflow runs
  these checks individually. Local leaf checks, source-graph scans and metadata
  inspection do not constitute that whole-library pass.

No separate client build, kernel replay, all-fields Milnor equivalence or
completion of the entire historical Quillen migration is claimed. The frozen
historical inventory and earlier slice validation remain records of their
original scopes.
