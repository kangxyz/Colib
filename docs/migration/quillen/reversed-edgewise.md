# Reversed edgewise realization for the Q/S comparison

The native owner is `SSet.EdgewiseSubdivision`. The indexing functor is the
actual ordered join `[n]ᵒᵖ ⋆ [n]`: on maps it uses `SimplexCategory.rev` on the
first half and the original map on the second. Its comparison is restriction
to the second half. This is not the ordinary unreversed first-half comparison
used by additivity, and it is not Mathlib's barycentric subdivision.

## Complete theorem and exact maps

`realizationHomotopyEquiv X` is an actual homotopy equivalence for every
simplicial set, including infinite-dimensional ones. Its forward map is
literally `SSet.toTop.map (endpoint X)`. Naturality and the equation at each
original chosen vertex are proved. The explicit all-degree contraction of a
subdivided standard simplex contracts each interval toward `(0,n)` and is
natural even for ordinal maps that do not preserve endpoints.

The representable theorem propagates through the existing native
`SSet.RealizationComparison.realizesEquiv_all`. This uses actual realized
monomorphism HEP, skeletal pushouts, and sequential homotopy invariance.
These foundations are reused, not redeclared or assumed as new hypotheses.

`verticalRealizationHomotopyEquiv`, `horizontalRealizationHomotopyEquiv`, and
`upperIndexRealizationHomotopyEquiv` retain the exact diagonal endpoint maps.
Their proofs use the double-subdivision diagonal and the native
`ContinuousMap.HomotopyEquiv.ofAdjacentComposites` two-out-of-six argument.
No rowwise realization-invariance assumption is needed for these statements.

## Source and literature scope

Implementation source: Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`,
`Quillen/Topology/Realization/Edgewise.lean`, `EdgewiseSimplex.lean`,
`EdgewiseRealization.lean`, and `EdgewiseBisimplicial.lean`.
The declarations retain their actual maps, hypotheses and universes. Shared
ordinal joins and join descent, reversal, diagonal, and gluing primitives use
their existing Mathlib/Colib owners. Pure simplicial lemmas were placed below
realization. The source correspondence is in `reversed-edgewise-sources.json`.

Weibel IV Exercises 3.9(b) and 3.10, page 35, are cited as background.
The inspected Chapter IV PDF has SHA-256
`9f1c1b8cccfe19d547c27dd04c61f198fd7a0cddd0018a0b84442b00fa575248`.
The exercise displays faces removing positions `i` and `2n+1-i`; the required
indexing convention here removes positions `n-i` and `n+1+i`. No equality of
these differently labelled functors is asserted without a comparison.

## Boundaries

This theorem closes the reversed-edgewise realization prerequisite for Q/S.
The exact-category comparison, reconstruction of Q-chains from native rows,
and the full canonical Quillen-Waldhausen K-equivalence remain separate
obligations. No naturally compatible homotopy inverse is claimed.

`ColibTest.EdgewiseSubdivision` checks the actual forward maps, naturality,
basepoint, all-degree contraction, and bisimplicial upper-index map. Concrete
coface and endpoint tests distinguish reversed from unreversed subdivision.
Compilation, source correspondence and independent mathematical review are
separate facts; no independent review or kernel replay is claimed here.
