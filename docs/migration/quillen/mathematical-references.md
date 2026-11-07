# Mathematical sources and implementation provenance

The bibliography distinguishes Daniel Quillen's 1973 paper (`Quillen1973`)
from the Lean software repository (`quillen`). A software source identifies
where an implementation came from. It does not assign authorship of the
mathematical theorem. Existing software citations and modern textbook
references are retained alongside the original mathematical sources.

Locators for Quillen's paper use the final publisher pagination, 85–147,
printed at the bottom of the archived scan. The scan also contains earlier
pagination and PDF page numbers, which are not the locators used here.

## Quillen constructions and fundamental theorems

- The nonnegative groups are the shifted homotopy groups of `BQ` at zero:
  Section 2, definition (5), page 103. The `KSpace` name denotes `BQ`, not
  its loop space. Exact-functor maps and functoriality are equation (6) and
  the following paragraph on that page.
- The canonical Grothendieck-group comparison with homotopical K-zero is
  Section 2, Theorem 1, pages 102–103.
- Theorem A and Theorem B are in Section 1, pages 93 and 97. The implemented
  costructured comma categories use the dual formulations stated there.
  Theorem B retains the hypothesis on every transition functor and the
  actual comma-to-homotopy-fiber comparison map.
- Length-one resolution is Section 4, Theorem 3, pages 108–109. Arbitrary
  objectwise finite resolution lengths are Corollary 1, pages 109–110.
  The inherited exact structure, extension closure and kernel closure
  remain explicit. Finite length is not a uniform bound on all objects.
- Abelian dévissage is Section 5, Theorem 4, page 112. Its subcategory is
  closed under subobjects, quotients and finite products. Finite filtrations
  are required, but extension closure is not added as a hypothesis.
- Serre localization is Section 5, Theorem 5 and proof, pages 113–116.
  The current endpoints concern an abelian category and its Serre quotient,
  with the connective long exact sequence ending at surjective K-zero.
  They are not statements about arbitrary scheme-open localization or
  negative K-groups.
- Finite-support positive K-theory uses finite products and filtered
  colimits, Section 2, equations (8)–(9), pages 103–104. This is an
  application of those ingredients, not a separately named theorem in
  Quillen's paper. The published endpoint retains its positive-degree
  range.

## Waldhausen comparisons

- Exact-equivalence invariance uses natural weak-equivalence invariance,
  Waldhausen's Proposition 1.3.1, pages 330–331, and functoriality. It is
  not an invocation of the Approximation Theorem.
- Additivity for a cofibration sequence of exact functors is Proposition
  1.3.2(4), pages 331–332, together with Theorem 1.4.2, page 336.
  The realized homotopy and the zero-based group-map formula are separate
  endpoints. The former does not by itself assert a constant basepoint
  track.
- The Q/S comparison is the unnumbered appendix in Section 1.9, pages
  375–376. There is no theorem numbered 1.9.1 in that appendix. The
  implemented edgewise-subdivision comparison is an adaptation retaining
  its actual maps.
- The fibration reference is Theorem 1.6.4 and proof, pages 350–352;
  approximation is Theorem 1.6.7, page 354. A reference to these classical
  results does not discharge the explicit cylinder, extension or endpoint
  data appearing in a particular formal endpoint.

## Gillet–Waldhausen and the abelian ambient

The precise bounded-complex comparison used for COL-0260 is
Thomason–Trobaugh, Theorem 1.11.7, pages 279–281, with the embedding
hypothesis in Section 1.11.3.1, page 278. The inherited exact subcategory
is closed under kernels of surjections in the specified abelian ambient.
The formal endpoint retains that condition and the original degree-zero
inclusion; it extracts the connective K-group comparison.

Thomason–Trobaugh credit Gillet's earlier argument and explicitly explain
why its proof needs the extra embedding hypothesis. That historical remark
does not justify removing the condition, and is not a claim that the
original Gillet article has been independently checked here.
