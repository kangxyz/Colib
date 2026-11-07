# The actual stable fiber and original Quillen K₂ maps

## Source and boundary

This continuation uses Quillen revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, with the existing pinned Mathlib and
Stacks objects. The endpoint source is `KTheory/Field/MilnorKTwoEquivalence.lean`.
The canonical forward maps land in the original homotopical Q-construction
groups. The completed chain proves the needed fiber perfectness, kernel-map
bijectivity and field-change squares, rather than inferring them from the
algebraic Milnor–Steinberg kernel equivalence. The
[final comparison](field-k2-comparison.md) distinguishes these source conclusions
from historical local endpoint checks and the completed Lean 4.35 whole-library
CI for published commit `0fd43f0253d6ff441fbc3e82420a0573ad694310`.

The constructions in this page apply to arbitrary rings where stated and to
all fields for Steinberg-to-fiber maps. The characteristic-zero hypothesis
remains on Matsumoto injectivity and the final Milnor–Quillen equivalences.

## Actual constructions

1. Native matrix Whitehead calculations identify the stable elementary subgroup
   with the commutator subgroup. The same subgroup is normal, and its actual
   quotient is the stable general linear group's abelianization.
2. The direct-sum Core of native finite projective modules has faithful
   translations and a cofinal rank-one object. Actual action localization,
   diagonal/iterated actions, extension spans, Cartesian lifts, fixed fibers
   and comma adjunctions construct its group-completion category. The grading
   is numerator minus denominator, with no plus property assumed.
3. Native realization colimit maps allow independent object and morphism
   universes. Actual simplex maps and whole natural-transformation vertex
   tracks give universe lifting and Theorem A/B comparisons without changing
   the realized functors, comma projections or basepoint paths.
4. The genuine extension total category and its first/second projections give
   the original completion-to-Q-loop weak equivalence. It reverses the inner
   loop exactly once; the external comparison track is unchanged. The actual
   positive homotopy groups of the completion and its zero component identify
   with the original Q-groups through the specified path and inverse loop shift.
5. Stable finite-matrix automorphisms map into the original telescope and
   completion. Literal right-module matrix conventions are retained, including
   the reversal required by right stabilization versus left direct sum. An
   actual completion character detects the quotient. The based stable π₁ map
   is surjective and has exactly the original elementary subgroup as kernel.
6. The original stable homotopy fiber maps onto that elementary group. Its
   projection kernel is central by the actual loop action. Universal central
   lifting constructs the Steinberg-to-fiber map, uniquely over the same
   elementary projection. Asphericity of the actual stable group classifying
   space makes its degree-two connecting map injective.
7. Restricting the lift to the actual Steinberg kernel, inverting the connecting
   map on its image, and transporting along the original basepoint path gives
   `steinbergKernelToCompletionPiTwo`. The proved completion-to-Q comparison
   then gives `steinbergKernelToRightProjectiveKTwo` with codomain
   `(ModuleCat.FiniteProjective.exactStructure Fᵐᵒᵖ).K 2`.
8. The finite-dimensional-module comparison uses native `FGModuleCat`, the
   original exact inclusion and opposite-ring restriction, literal scalar
   extension, and the genuine upper SmallModel/common-ambient comparison.
   Native `MilnorKTheory.toRightProjectiveKTwo` and `toUpperModuleKTwo` are the
   original composites from the unchanged Stacks homogeneous Milnor group.

There is no second matrix, Milnor, homotopy-group or Q-construction model and
no compatibility namespace. Group-completion and comma categories are the
actual mathematical constructions required by the comparison, not supplied
equivalence hypotheses.

## Source owners and native placement

- `Topology/Homotopy/HomotopyGroup`, `Topology/HomotopyFiber`, and realization universe
  foundations are placed below their applications in native `Colib.Topology`.
- `CategoryTheory/GroupCompletion`, action-localization, localization roof and
  character constructions remain generic categorical owners.
- Pure finite-projective categorical structure, matrices, extension diagrams
  and direct-sum Core live under `Colib.Algebra.Category.ModuleCat` and the
  corresponding native linear-algebra owners.
- Classifying-space realization, telescope, completion, extension and loop
  comparisons live under `Colib.Topology.ClassifyingSpace`.
- The source `KTheory/Quillen/ProjectiveCompletionPositiveK` endpoints are in
  `Colib.RingTheory.KTheory.Quillen.ProjectiveCompletion`.
- The actual stable-fiber and kernel-to-right-projective maps are in
  `Colib.RingTheory.KTheory.Quillen.Field.SteinbergFiberComparison`.
- The native Milnor composites and ordered-symbol equations are in
  `Colib.RingTheory.KTheory.MilnorK.QuillenComparison`. Upper finite-module and base-change
  constructions retain their exact-category and native module owners.

The general all-category fundamental-group comparison reuses native groupoid
completion and localization uniqueness. Positive component homotopy comparison
reuses the actual component inclusion. Cross-universe realization uses native
simplicial sets and colimits, rather than introducing a parallel simplicial-map
structure. These are proof replacements preserving the specified mathematical maps.

## Exact normalization

- An ordered native symbol maps to `Additive.ofMul (torusDefectKernel a b)`
  before the original Steinberg-kernel map to Q.K₂.
- The fiber connecting equation uses the inverse of the original degree-two
  basepoint transport, not an unspecified isomorphism.
- The original completion-to-loop map reverses the inner loop exactly once.
- The upper finite-module comparison, when transported to the original model,
  is the actual finite-projective inclusion followed by opposite-ring restriction.
- The ordered symbol is the upper model's positive `unitProduct F a b`, with
  scalar `a` acting on the positive determinant-inverse K₁ class of `b`.
- In characteristic zero, the upper negative normalization is literally minus
  the positive inverse and takes this product to `-milnorKTupleSymbol ![a, b]`.

## Completed homological and comparison chain

1. `Colib.RingTheory.KTheory.Quillen.StableZeroFiberHomology` and `.StableZeroFiberGeometry`
   construct the original simply connected cover and pullback setup, with the
   integral homology theorem for the actual lifted stable map. The proof retains
   local coefficients, covering monodromy and homological descent.
2. `Colib.RingTheory.KTheory.Quillen.StableFiberPerfectness` proves perfectness of the
   literal stable-zero fiber's π₁ for every ring. The low-degree criterion and
   actual endpoint-aware fiber map supply the proof. Perfectness of the stable
   elementary group or pullback group alone is not used as the conclusion.
3. `Colib.RingTheory.KTheory.Quillen.Field.SteinbergFiberSurjectivity` and
   `.SteinbergFiberInjectivity` prove bijectivity of the existing kernel-to-Q.K₂
   map over every field. Constructed square capping and ordered torus calibration
   give the detector's left inverse, using actual kernel generation. Native
   central evaluation replaces the source's Schur-equivalence proof; it does
   not assert literal equality of differently implemented detectors.
4. `Colib.RingTheory.KTheory.MilnorK.QuillenNaturality` retains the original right-module
   scalar extension and literal upper finite-module tensor extension. The
   general-field positive marking then identifies the actual ordered product.
   `Colib.RingTheory.KTheory.MilnorK.QuillenEquivalence` combines these inputs with native
   Matsumoto injectivity in characteristic zero, including inverse field-change
   squares and the negative normalization.

No fiber-perfectness, generation, detector-law or comparison-isomorphism
premise is added to the final endpoint. The finite-module target is literally
`Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u+1} 2)`.

## Historical construction validation

The initial construction slice and its owned in-package regression examples
were compiled against the pinned toolchain with strict implicit arguments, warnings as errors,
and the native Mathlib standard source linters. The actual maps, independent
universes, original ordered symbols, fiber connecting equation and upper-model
inclusion equation have checked examples. Native declaration/text lint and the
production axiom audit are distinct from source comparison. Those historical
checks are not validation of the final coordinate-rebuilt source closure.
Earlier snapshots of the positive-marking leaf and its ordinary regression have
separate strict compilation and native QA evidence. Earlier characteristic-zero
endpoints also passed focused native checks within their recorded source scope.
Those local results are distinct from the successful original whole-library
[CI run 42373233801](https://github.com/kangxyz/colib/actions/runs/42373233801)
for the exact published Lean 4.35 commit above, as recorded in the
[comparison verification boundary](field-k2-comparison.md#verification-boundary).
No exhaustive independent review or kernel replay is inferred from compilation.
