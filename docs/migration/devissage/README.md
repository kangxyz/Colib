# Classical Quillen devissage

Library items COL-0244–COL-0246 record actual finite admissible filtrations,
the layer/comma equivalence and classical homotopical devissage. For a small
abelian category, an object property containing zero and closed under subobjects,
quotients and finite products has the same Quillen K-theory when every object
has an actual finite filtration with factors in that property.

The realized Q-inclusion is the forward map of the classifying-space homotopy
equivalence. Canonical zero normalization gives the original exact-inclusion
KMap in every nonnegative degree, including K₀ = π₁ BQ. The forward group
homomorphism of `CategoryTheory.Abelian.Devissage.KEquiv` is definitionally that
same KMap. Neither extension closure nor a uniform filtration bound is assumed.

## Actual native objects and proof

- Mathlib constructs the intrinsic abelian full subcategory `P.FullSubcategory`.
  Its existing kernels/cokernels and Colib's standard abelian exact structure
  give the actual exact inclusion. This is not Resolution's extension-closed
  inherited exact structure, and a filtration is not treated as a resolution.
- Finite conflation towers retain their actual maps, arbitrary zero-object base
  and selected factors. Additive invariants telescope along the tower.
- Abelian Q-arrow cancellation uses the actual pullback apex maps. Every Q-arrow
  is monic. Spans between subcategory objects lift because their apex is a
  subobject of the target. The generic Q-faithfulness proof is moved unchanged
  from `KTheory.Quillen.Equivalence` to the lower exact-functor Q owner and reused.
- A layer has two nested ambient subobjects and an actual quotient in P.
  Quotient spans give an equivalence with the actual inclusion comma category.
  The pullback composition and quotient projection equations are preserved.
- Intersection restriction and enlargement give continuous homotopies through
  their actual natural transformations. Induction on the finite conflation
  tower contracts the layer classifying space. Native Quillen Theorem A then
  gives the realized inclusion equivalence.
- Existing `normalizedQ`, `normalizedQ_map_point` and
  `KEquivOfHomotopyEquiv` give the zero-based conclusion. No inverse or
  contractibility is assumed as input, and inverse homotopies need not be based.

The categorical prerequisites retain independent object and hom universes.
The final Theorem A application uses a small category. This milestone does not
assert negative K-theory, a Q/S comparison, an algebraic Grothendieck-map inverse,
or completion of the entire historical Quillen migration.

## Literature and source correspondence

The theorem adapts Weibel, *The K-book*, Chapter V, Devissage Theorem 4.1 and
its proof, page 33. The cited chapter is already pinned in `docs/references.toml`.
The full-subcategory hypotheses explicitly construct the exact abelian
subcategory used there. The proof follows its layer comparison and intersection
contraction, but proves the required natural-transformation zigzag directly
rather than asserting that the chosen functors are adjoints.

The historical source revision is Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. `source-crosswalk.json` records the
64 explicit declarations in the eight theorem-chain files, their six required
filtration/layer prerequisite files, namespace changes and native-helper reuse.
It is a bounded source crosswalk, not a compiled census of the whole source
project. Original implementation attribution is preserved without an Aglib
production dependency or alternate abelian/Q/K model. The selected inverse in
`KEquivOfHomotopyEquiv` may differ from the source's choice; only the forward
canonical map is claimed to be identical.

## Validation and review boundary

The independent mathematical review covers the fixed pre-registration proof
snapshot against main `439de508c89c315ff8c7ec4d787d032797cef84b`: the stated
hypotheses, actual span/layer/comma equivalence, filtration contraction, canonical
Q/K maps and native-helper reuse. It does not independently re-review every
previously published topological prerequisite or subsequent integration metadata.
The read-only snapshot review recomputed 2,268 source and 11,340 artifact hashes,
checked 18 successful compile records with direct imports and logs, and inspected
68 axiom endpoints, with only the standard three axioms. It included 182 native
main bindings, six frozen prerequisites and 2,062 pinned upstream source files.
It was not a new Lean execution, kernel replay or full-library run. The crosswalk
records the reviewed snapshot identities; integration retains its mathematical
proof sources unchanged, adding only reference imports and registration metadata.

The in-package tests retain the quotient projection, span composition,
supported inclusion/restriction maps, categorical equivalence, zero basepoint
and actual KMaps in degree zero and positive degrees. Resolution and devissage
are also imported together after the shared faithful-Q lemma is lowered.
Compilation, metadata checks and axiom auditing are distinct from mathematical
review; no kernel replay or separate downstream-client check is asserted.
