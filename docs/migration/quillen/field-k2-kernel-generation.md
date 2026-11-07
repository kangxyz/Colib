# Stable Steinberg kernel generation and central lifting

## Scope and source

This slice continues the actual field K₂ comparison from Quillen revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Its Colib baseline is published main
`95fceadddb4d7c178bb271358d7cfaa51a6664fa`, tree
`8f6fb96d420a1bc1a0ed7774f4d83ff5e57f22b5`.

For every field, the actual stable Steinberg-to-elementary kernel is generated
by its original ordered torus defects. Consequently the existing native map
`StableSteinberg.milnorToKernel F` is surjective. Its domain is the unchanged
Stacks `MilnorKTheory F 2`; no pair-symbol quotient or transport adapter is added.

The same stable Steinberg map is also proved to be a universal central
extension: its group lifts uniquely through every surjective central extension
of the actual stable elementary group. The extension group can occupy an
independent universe. This is a constructed lift, not an assumed lifting law.

Neither result alone proves Matsumoto injectivity or the Milnor–Quillen K₂
comparison. Their completed continuations are linked below; the final
Milnor–Quillen endpoint retains its characteristic-zero hypothesis.

## Source correspondence

- `StableSteinbergRankTwo.lean` becomes
  `Colib.GroupTheory.Steinberg.RankTwo`. The actual ordered defect subgroup,
  quotient, root conjugation and rank-two collection prove that the generated
  defect subgroup equals the rank-two stage intersected with the kernel.
  The Milnor range argument is moved to its K-theory owner.
- `StableSteinbergParabolic.lean` becomes `.Parabolic`. It proves actual
  upper-parabolic normal forms, kernel descent, root relocation and the
  nonzero row orbit result with the same finite-root words.
- `StableSteinbergBruhat.lean` becomes `.Bruhat`. Its `B * V * B` coverage is
  proved for source words in the defect quotient. Equal matrix images are
  not used to assert equality of arbitrary Steinberg words.
- `StableSteinbergKernelGeneration.lean` becomes `.KernelGeneration`. Actual
  last-row matrix detection gives one-step stage descent; finite-stage
  induction proves `defectSubgroup_eq_kernel` and `kernel_le_stage_two`.
- The native range argument and final surjectivity consequence are in
  `Colib.KTheory.MilnorK.Steinberg.Surjectivity`. Native tuple-symbol
  generation replaces the former Milnor model's extension API. The forward
  homomorphism and value `h(a) * h(b) * h(a*b)⁻¹` are unchanged.
- `StableSteinbergUniversal.lean` becomes
  `Colib.GroupTheory.Steinberg.Universal`. Commutators of actual elementary
  preimages construct the lift. Centrality, fresh coordinates and Hall–Witt
  prove the four original defining relations; perfectness proves uniqueness.

All source paths above are under `Quillen/Algebra/Group/`. Source attribution
and Apache-2.0 notices are retained. The native matrix types, stable directed
limit, stable presentation and chosen maps are the ones already in Colib.
The defect quotient is a quotient used in the generation proof, not an
alternative model for Milnor K₂. There are no Aglib imports or compatibility
namespaces. Every field is allowed, including fields of order two and three.

## Completed comparison continuations

1. The [Matsumoto continuation](matsumoto-native-injectivity.md) constructs the
   faithful native Milnor-valued detector and proves
   `milnorToKernel_injective_charZero`. Together with all-field generation,
   it gives the canonical kernel equivalence in characteristic zero.
2. The [stable-fiber continuation](field-k2-stable-fiber.md) proves the genuine
   homological inputs, fiber perfectness and bijectivity of the original
   kernel-to-Q.K₂ map. The completion-to-Q-loop map still reverses the inner
   loop exactly once and retains its specified basepoint path.
3. The [final comparison source](field-k2-comparison.md) includes the original
   upper finite-module comparison, forward and inverse field-change squares,
   general-field positive ordered marking and characteristic-zero negative
   normalization. The negative normalization is minus the positive inverse.
   Final endpoints passed focused native checks on the rebuilt coordinate
   closure. Original whole-library verification remains pending.

## Historical slice validation

The six production modules and the in-package
`ColibTest.SteinbergKernelGeneration` test are checked using the pinned toolchain
with `autoImplicit=false`, `warningAsError=true` and Mathlib's standard source
linters. The tests cover all-rank kernel generation, stage descent, actual
Milnor surjectivity and ordered symbols, independent-universe lifting, and the
identity lift of the original central extension to itself.

The full default declaration lint passes for both endpoint import closures.
Native text lint, generated-import checking and catalog validation pass. The
pinned independent axiom auditor checks 892 imported Colib declarations, using
only `propext`, `Classical.choice` and `Quot.sound`.

These historical focused checks do not validate the later coordinate-rebuilt
closure. Final endpoint and original whole-library checks are distinct.
No separate kernel replay, client check or independent mathematical review is
inferred from compilation. Detailed verification output is kept outside the
repository.
