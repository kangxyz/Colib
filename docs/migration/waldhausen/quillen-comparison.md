# Canonical Quillen-Waldhausen comparison equivalence

## Mathematical result

For every exact structure `E`, the canonical comparison identifies the existing
Waldhausen S-theory and Quillen Q-theory in every nonnegative degree:

- `comparisonKEquiv E n : (Waldhausen.ofExactCategory E).K n ≃* E.K n`.
- Its underlying homomorphism is exactly the previously defined `comparisonK E n`.
- `comparisonKEquiv_exactFunctor_naturality` commutes with the original
  `Waldhausen.KMap F.waldhausenExact` and `F.KMap`, without an additional
  pushout-preservation, strict-zero, or comparison-equivalence hypothesis.

The actual realized Q/S map has a homotopy equivalence whose forward continuous
map is definitionally `realizationComparison E`. Its chosen zero vertex is
preserved. The endpoint leg has the same property, so the original based zigzag
induces the group isomorphism, including degree zero. The resulting
`deloopingHomotopyEquiv` is an unbased homotopy equivalence; its inverse is not
silently treated as a strictly based map.

The object universe and morphism universe remain independent. Naturality uses
the same shared source/target universe parameters as the existing based K-map
APIs. Mixed hom universes in the row comparison are handled directly on the
native categorical nerves.

## Actual native models and maps

`Waldhausen.ofExactCategory E` uses the original inflations as cofibrations and
isomorphisms as weak equivalences. The comparison acts on the existing
`QuotientRows.Obj` and `WeakRows`. Its grid presentation is exactly
`sSetWeakRowDiagonalIso`, not a second row category.

The subdivision is the genuine reversed ordinal `[n]^op ⋆ [n]`. At vertex `i`,
the prescribed comparison takes quotient `[n-i,n+1+i]` in nerve row `n+1+i`.
The second-half endpoint is retained throughout. Ordinary ordinal subdivision
and its first-half endpoint are not substituted.

The interval-containment arrow is the actual span with intervening subquotient
apex, deflation left leg and inflation right leg. Quotient zero-corner pushouts
supply conflations; overlapping subquotient pullbacks give the original
Q-composition law. Weak maps retain their original component isomorphisms.

## Proof of the comparison

1. The central-interval `rowChainComparison` is proved faithful by recovery
   from its largest interval component, and full by recovery of the original
   subobjects, initial flag, and quotient maps.
2. Every finite Q-chain is reconstructed as an actual native quotient row.
   The inductive extension uses the representative of the final Q-arrow.
   `reconstructedRow_last_step` proves equality with that specified span,
   completing essential surjectivity. `rowChainEquivalence` has exactly
   `rowChainComparison` as its forward functor.
3. Strict reindexing, including natural-isomorphism morphisms and equality
   transports, gives `rowChainNerveMap`. The generic rowwise-to-diagonal
   realization theorem applies to the genuine categorical row equivalences.
4. Evaluation of the native `chainCoreNerve` diagonal is contracted directly
   to the ordinary nerve, using a vertically constant section. No second
   rectangular-grid classification simplicial set or adapter isomorphism is
   introduced. Evaluation takes the vertical isomorphism first and then the
   target chain's horizontal arrow.
5. `comparisonMap_factorization` identifies the prescribed simplicial map
   exactly, by pointwise definitional equality. The factorization uses the
   original weak-row presentation, second-half nerve restriction, row
   comparison, and native chain-core evaluation. The homotopy equivalences
   therefore apply to that actual map, not merely to abstract spaces of the
   same homotopy type.

For exact-functor naturality, admissible pushout preservation is derived from
the signed biproduct cokernel. The original `sSetMap` and `mapQ` satisfy the
simplicial square. The strict-zero based squares are proved first; normalization
of the original exact functor and genuine zero-fixed natural-isomorphism
homotopies remove that intermediate hypothesis. Both canonical K-map APIs are
retained, with no substitute map definition.

## Source correspondence

Pinned Quillen source: `kangxyz/quillen-k-theory`, revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

- `Waldhausen/ExactCategory.lean` and `ExactFunctor.lean`: actual exact-category
  Waldhausen structure and exact functor.
- Aglib `Aglib/CategoryTheory/ExactCategory/FunctorPushout.lean`, revision
  `2c34f185fa859e862661f939cd216b07bcccfb26`: signed biproduct proof of
  admissible pushout preservation.
- Q/S exact rectangles, interval spans, row groupoid, reindexing, flags, span
  reconstruction, full faithfulness, and essential surjectivity: re-proved
  on native quotient rows; the source's separate `Row` structure is omitted.
- `EdgewiseIndices.lean`, `SimplicialMap.lean`, `Basepoint.lean`,
  `ComparisonHom.lean`, `BisimplicialMap.lean`, `Factorization.lean`, and
  `Equivalence.lean`: original reversed indices, map, zero vertices, exact
  factorization, and canonical homotopical comparison.
- `KTheory/Map/NaturalIso.lean`, `ZeroNormalization.lean`, `BasedNaturality.lean`,
  and `ExactNaturality.lean`: actual natural-isomorphism invariance and based
  naturality, using the existing Waldhausen invariance API directly.
- Generic reversed-edgewise realization and rowwise-to-diagonal realization
  retain their separately owned native theorems. Native chain-core diagonal
  contraction replaces the source's second classification presentation.

## Validation and review scope

The integration uses the normal native `scripts/check.sh` categories: strict
production build, all in-package tests, Batteries declaration lint, Mathlib text
style, generated root check, pinned production axiom audit, and native Library
export/site validation. Only `propext`, `Classical.choice`, and `Quot.sound` are
allowed. Source, output, log and direct-import hashes bind the checked snapshot.

Regression tests retain actual spans, weak components, reversed central
indices, zero vertices, both original K-map APIs, degree zero, exact forward
maps, inverse laws, and unconditional exact-functor naturality. Independent
read-only mathematical reviews cover native row reconstruction, generic
diagonal realization, based naturality and final assembly. Their scopes are
recorded separately from compiler evidence; no kernel replay is implied.
