# Canonical Grothendieck–Quillen K-zero comparison

This contribution establishes the existing canonical homomorphism
`ExactStructure.grothendieckToKZero` as a group equivalence with actual
homotopical Quillen `K 0`. The positive-degree convention, realized Q-category,
original zero basepoint, independent universes and canonical object classes are
unchanged. Library items COL-0239 and COL-0240 record the two public endpoints.

## Actual proof and mathematical ownership

1. `Topology.Homotopy.OpenCover` constructs descent from chart functors and
   natural overlap transitions, using subdivisions of actual paths and homotopy
   squares. Generic finite categorical pasting lives under
   `CategoryTheory.ComposableArrows`; equality transport and joint
   representatives have their own category-theoretic owners.
2. The `Colib.Topology.Realization.SimplexBoundary` directory family, including
   `VertexStars`, `StarTrivializations`, `BoundaryEdges` and `FilledTriangles`,
   directly uses native `Convexity.StdSimplex` for vertices, open stars, edges, midpoint
   spokes and contractions. The actual `Convexity.StdSimplex.boundary` is owned by
   `Colib.Analysis.Convex.StdSimplex.Boundary`. The old same-named
   `Colib/Topology/Realization/SimplexBoundary.lean` finite-model owner is retired,
   not this directory family. The two-dimensional case needs its triangle
   relation. In dimensions at least three, a fourth coordinate gives a genuine
   zero-coordinate face filling every edge triangle.
3. `Topology.Realization.SimplexAttachment` constructs overlap identifications
   and groupoid functor extensions along actual simplex attachments. Generic
   constructions do not depend on nerve applications. The original subtype
   maps are Mathlib `ContinuousMap.subtypeVal` and `ContinuousMap.inclusion`.
   Actual subset paths reuse `Path.inSubset`, moved unchanged to its lower
   `Topology.Path.InSubset` owner.
4. `Topology.ClassifyingSpace.NerveCompletion` constructs the graph decoder,
   computes all three actual two-cell faces, extends through higher cells, and
   retains natural restriction isomorphisms at every skeletal stage. Compact
   relative homotopies lift to a later stage with their exact boundary paths
   and endpoints. That lifting belongs to the native sequential-colimit owner.
5. A joint representative retains both its decoded localization morphism and
   its actual ambient path class. Localization generation and relative-homotopy
   reflection prove faithfulness of the unchanged completion functor. The
   already proved original surjectivity gives based-loop bijectivity.
6. The existing exact `grothendieckToKZero_factorization` supplies K-zero
   injectivity. Combining it with the earlier surjectivity defines
   `grothendieckKZeroEquiv`; its forward homomorphism is definitionally the
   original comparison. The regression tests retain this equality, original
   object classes, zero, multiplication, and both category universes.

No parallel realization, groupoid completion, or K-zero model is introduced.
The chart and transition structures are input data for descent on the actual
fundamental groupoid, not a replacement for that groupoid. Skeletal abbreviations
only name the existing `SSet.skeletonOfMono` stages and maps.

## Literature and source correspondence

The K-zero endpoint adapts Weibel, *The K-book*, Chapter IV, Proposition 6.2
and its proof, equations (6.2.1)–(6.2.2), page 54. The nerve/classifying-space
background is IV, Recipe 3.1.1 and Definition 3.1.4, pages 24–25. These are the
pinned documents already recorded in `docs/references.toml`.

The original Quillen source is fixed at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The statements of
`Quillen/Topology/ClassifyingSpace/CompletionRetraction.lean`'s final
`classifyingGroupoidCompletionMap_injective` theorem and
`CompletionSurjectivity.lean`'s `classifyingGroupoidCompletionMap_bijective`
theorem are retained on the original comparison map. The proof is an explicit
finite-skeleton route, not an imported or assumed retraction. The source's
separate `CompletionRetraction` construction is not claimed as migrated.

The supporting open-cover and decoder proofs are new proof infrastructure,
not individually migrated historical source statements. Earlier surjectivity remains
at COL-0160 and COL-0162. This contribution does not close the historical
Quillen inventory as a whole or claim a higher K-group comparison.

## Review boundary

Independent review covered the original-map endpoint, joint-representative
argument, relative finite-stage reflection, sequential compact-factorization
hypotheses, and the central higher-cell argument. Compilation and transitive
axiom auditing cover the full included chain. They are distinct from an
independent mathematical review of every lower-level grid and collar proof.

This review and validation describe the original K-zero contribution. They do
not themselves certify the later coordinate-rebuilt dependency closure. Its
original whole-library checks passed for published Lean 4.35 commit
`0fd43f0253d6ff441fbc3e82420a0573ad694310` in
[CI run 42373233801](https://github.com/kangxyz/colib/actions/runs/42373233801),
with the scope stated in the [integrated verification boundary](field-k2-comparison.md#verification-boundary).
