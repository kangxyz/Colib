# Quillen Resolution on the existing native objects

## Statement and actual maps

Let C be a small preadditive category with finite biproducts, E its selected exact
structure, and P an object property containing zero and closed under isomorphisms,
extensions, kernels of admissible epimorphisms between P-objects, and finite
products. Suppose every ambient object has an actual finite admissible resolution
by P-objects. There is no uniform bound on the resolution lengths.

`CategoryTheory.ExactCategory.Resolution.classifyingHomotopyEquiv` identifies the
Q-classifying space of the inherited full exact subcategory with the ambient
Q-classifying space. Its forward map is exactly the realization of the original
Q-inclusion. `KEquiv` gives the multiplicative equivalence in each degree n : Nat,
including zero. `KEquiv_coe` identifies its forward homomorphism with the original
canonical `inclusionKMap`. The chosen-zero normalization uses the actual natural
isomorphism of the existing Q-functor, not an unspecified basepoint path.

## Proof and native ownership

1. Finite resolutions retain genuine Mathlib short complexes, their E-conflation
   proofs, all resolving middle terms, and all syzygies. This extends the existing
   selected exact structure; it does not introduce a second exact category.
2. Base-change conflations, composition and inherited full-subcategory exactness
   have one owner each under `CategoryTheory.ExactCategory`. The relative closure
   conditions are for the specified admissible pairs, not all ambient kernels or
   all short exact sequences.
3. Actual cover and comma categories give the length-one contraction. The full
   ambient Q-subcategory and the inherited Q-construction are distinct categories;
   their comparison functor is proved rather than treated as an identification.
4. Theorem A is proved using native comma categories, nerves, simplicial
   replacement, realization and colimits. Its forward map is the actual realized
   functor. The replacement invariance theorem is about this explicit construction,
   not a general arbitrary bisimplicial realization theorem.
5. Adjacent finite-length strata have length-one resolutions. Induction gives
   homotopy equivalences for their actual Q-inclusions.
6. For each ambient Q-arrow, the proof chooses resolutions of its source, target,
   span apex, left kernel and right cokernel. A maximum of these five lengths
   lifts that one arrow. Faithfulness and eventual object equality then identify
   the actual ambient Q-nerve as the filtered colimit.
7. The actual countable mono diagram is reindexed from AsSmall Nat without
   shrinking C. Native realization of a simplicial mono has HEP. The existing
   sequential HEP invariance theorem identifies stage zero with the ambient
   realization, with exactly the cocone leg as forward map.

Mathlib projective resolutions and Stacks finite projective resolutions are not
substitutes for this arbitrary exact-category construction: their projectivity
and ambient abelian hypotheses would strengthen the statement. The new relative
closure predicates similarly avoid replacing admissible kernels with all kernels.
No old Aglib import, second perfect-complex model, legacy compatibility category,
or continuous-coordinate HEP adapter is introduced. Historical implementation
attribution and original author/license notices are preserved.

## Literature and public items

The mathematical reference is Weibel, *The K-book*, Chapter V, Resolution Theorem
3.1 and Proposition 3.1.1, pages 20-21, with Exercise 3.1 for the strata route.
Theorem A is Chapter IV, Theorem 3.7, page 30; adjunctions are IV.3.2, pages 25-26;
simplicial realization invariance is IV.3.6.1, page 29. The explicit countable
mono/HEP union argument is a new formal proof of the union step, with the book
cited as background rather than as a verbatim standalone topological theorem.

COL-0231 records adjunctions, COL-0232 Theorem A, COL-0233 replacement invariance,
COL-0234 finite admissible resolutions and strata, COL-0235 comma contractions,
COL-0236 length-one K-equivalence, COL-0237 objectwise-finite Resolution, and
COL-0238 the nerve colimit and sequential union passage. The existing bibliography
identity and inspected Chapter IV/V document hashes are reused.

Implementation provenance is the pinned Quillen snapshot
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Finite-resolution, cover, strata,
Theorem A and final theorem source families are adapted to the existing native
owners. Nerve-monomorphism and the countable union argument are direct new proofs,
not declarations claimed to be identical to the historical general filtered
realization statements. The historical Aglib pin is attribution only; no Aglib
source inventory or dependency is restored.

## Scope and evidence boundaries

This change does not establish general arbitrary filtered-realization invariance,
the historical every-stage-to-ambient union statement, Waldhausen Resolution
V.3.9, Devissage, Quillen/S comparison, or completion of the entire migration.
The bounded theorem is separately stated with a common N. Quillen K-zero
comparison injectivity remains separate from the all-degree Resolution theorem.

The integration begins at main ea1b405. Published shared owners are preserved,
including their newer universe generalization and removal of the HEP adapter.
Compilation, source correspondence, independent mathematical review and axiom
closure are separate evidence. The source review checked the final Resolution
chain, actual maps and upstream replacement candidates; it did not independently
reprove the previously published shared HEP/sequential foundations. No kernel
replay or separate downstream-client check is claimed.
