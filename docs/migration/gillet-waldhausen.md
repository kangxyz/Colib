# Gillet-Waldhausen on the original bounded-complex map

## Exact scope

The source is Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`, principally
`Quillen/Waldhausen/GilletWaldhausen/GeneralComparison.lean`. The destination is the
existing native Colib Waldhausen S-construction. The abelian ambient category and
its distinct object/hom universe bounds are retained.

An object property P contains zero and is closed under isomorphisms, extensions
and kernels of surjections between its objects. The actual bounded termwise-P
complexes inherit admissible cofibrations; coarse weak maps are ambient
quasi-isomorphisms. The original degree-zero single functor induces the final
K-equivalence in every nonnegative degree, including zero. Its forward map is
proved definitionally equal to the original canonical KMap.

No Quillen Q/S comparison, strict chosen-zero model comparison, scheme comparison,
nonconnective K-theory statement or chosen homotopy inverse is asserted. Weibel,
*The K-book*, V, Theorem 2.2, pp. 13-14, is the mathematical source for the
connective conclusion. Its specified abelian ambient and kernel-of-surjections
hypothesis are not omitted.

## Native dependency ownership

- Actual cochain terms, cycles, truncations, single insertion and disk maps live
  under `Colib/Algebra/Homology/CochainComplex/ExactSubcategory`. The namespace is
  `CochainComplex`. Original explicit term bounds are proved equivalent to
  Mathlib's `IsStrictlyGE` and `IsStrictlyLE`, for the same integers, rather than
  confused with homological boundedness.
- Actual identity-cone factorization, signs and quotients use Mathlib's mapping
  cone, homotopy and biproduct APIs. Pure homological lemmas remain below the
  Waldhausen application. Native exact-functor pushout preservation replaces the
  redundant full-subcategory pushout wrapper; native full-subcategory functor
  extensionality replaces the old postcomposition wrapper.
- The joint cylinder and second-endpoint section are proved from extension, cone
  and shift closure. The bounded predicate supplies the latter closure proofs.
  The coarse extension axiom follows from short exact homology sequences. Neither
  cylinder exactness nor a fiber comparison is assumed at the final endpoint.
- Finite term and cycle filtrations apply actual Waldhausen additivity. The finite
  adjacent-coordinate incidence map and alternating Euler homomorphism prove the
  unique acyclic/single decomposition with their original coordinate signs.
- The actual S-grids form a filtered union of symmetric finite term bounds.
  Compact cube and relative-homotopy factorization proves joint coverage and
  eventual equality for the original KMaps. Temporary compatible zero choices
  on the same finite-stage categories are transported back by their exact
  identity functors; they do not replace the final canonical maps.
- The established canonical fibration transports its genuine homotopy-fiber
  connecting homomorphism to the K-theory long exact sequence. The pointed-set
  tail supplies K-zero surjectivity. The fine product decomposition then proves
  bijectivity of the original coarse single-complex KMap.

## Provenance and evidence boundary

Every migrated module retains its source copyright, author and precise source
path. The additional Aglib homology and mapping-cone prerequisites use revision
`2c34f185fa859e862661f939cd216b07bcccfb26`. Imports are direct native Colib,
Mathlib and Stacks owners, without legacy namespace adapters.

COL-0257 records the bounded fine decomposition, COL-0258 the actual complex
cylinder, COL-0259 the structural connective long exact sequence, and COL-0260
the final original-map Gillet-Waldhausen theorem. Source correspondence,
compilation, native declaration lint, axiom audit and independent mathematical
review remain distinct facts. Detailed build records are kept outside the
repository. In-package regressions cover the precise native term bounds and
actual insertion, truncation, cylinder and K-map identities.
