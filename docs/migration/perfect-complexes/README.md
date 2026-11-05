# Comparing local perfect representatives

The public comparison is
`AlgebraicGeometry.Scheme.Modules.Complex.isPerfectComplex_iff_local_bounded_finiteLocallyFree_models`
(`COL-0176`). It compares the exposed archived local witness with native Stacks perfectness on
the same chain complex. It does not introduce another perfectness predicate.

## Source and mathematical ownership

The source is Aglib at `2c34f185fa859e862661f939cd216b07bcccfb26`:

- `Modules/LocallyFree/Basic.lean:34-36` supplies the finite local-basis witness. Its packaging
  changes from `exists_localBasis` to native `exists_isFiniteLocallyFreeData`.
- `Modules/PerfectComplexes/Strict.lean:45-50` supplies interval bounds on actual terms and
  finite local freeness in every degree, not merely cohomological boundedness.
- `Modules/PerfectComplexes/Local.lean:48-54` supplies the local representative and the direction
  `Q(scheme restriction K) ≅ Q(P)`, using the standard local derived models.

Quillen at `c561118b7795eb9780be9ed391c3251d6a4d0afd` consumes these objects in
`AlgebraicGeometry/PerfectComplexes/Strict.lean` and `KTheory.lean`. The exact declaration
crosswalk and source hashes are in [source-crosswalk.json](source-crosswalk.json).

The implementation belongs to scheme module complexes, under
`Colib/AlgebraicGeometry/Modules`. Its Library reading route is the perfect-complexes section
of algebraic geometry, not the Waldhausen K-theory section.

## Existing upstream mathematics

[Stacks 0BCJ](https://stacks.math.columbia.edu/tag/0BCJ), clauses (1) and (2), already identifies
perfect objects with local bounded finite locally free representatives when structure-sheaf
stalks are local rings. The pinned Lean implementation is
`RingedSpace.isPerfect_iff_hasFiniteLocallyFreeRepresentation` in `PerfectComplexes.LocalRingStalks`.
That derived-object theorem packages an existential global representative and local chain
quasi-isomorphisms. This comparison instead retains a specified chain complex, the source
scheme restriction, and a supplied derived model on each open.

The forward direction consumes the existing finite-free-neighbourhood and restriction
comparison lemmas, then [08CN](https://stacks.math.columbia.edu/tag/08CN), clause (2), and
complex-level local gluing. It does not repeat the finite-intersection proof. The reverse
direction consumes [0BCI](https://stacks.math.columbia.edu/tag/0BCI): a retract of a finite
locally free module is finite locally free when the stalks are local rings. The scheme
hypothesis supplies those local rings. No new general perfectness theorem is claimed.

The higher blow-up and derived-fibre application files are not imported. The bounded-model
helper and model-spelling adapter remain private. There is no new global strict-perfect
predicate or category and no public wrapper for the elementary bounded-model steps.

## Exact objects, maps and universes

The theorem takes `X : Scheme.{u}`, the original `K : CochainComplex X.Modules ℤ`, and a family
`∀ U : X.Opens, HasDerivedCategory.{d} U.toScheme.Modules`. It does not require a global derived
model. The source standard models at `u + 1` are an explicit regression specialization.

Write `ρ` for the native chain-complex isomorphism from ringed-space restriction to scheme
restriction. Forward transport uses `Q.mapIso ρ ≪≫ e` for the given source isomorphism `e`.
Reverse transport retains the local complex `P` and the original quasi-isomorphism
`f : P ⟶ ringed-space restriction K`, and uses
`(Q.mapIso ρ).symm ≪≫ (asIso (Q.map f)).symm`. It does not invent an inverse chain map.

`ColibTest.PerfectLocalComparison` checks the forward full and faithful inclusion.
`ColibTest.PerfectLocalEquivalence` checks both full-subcategory functors, underlying objects
and chain maps, both forgetful composites, identity unit and counit, and preservation and
reflection of `QuasiIso`. The test predicates expose the old local-basis witness and are
private scaffolding. The original Aglib package is not imported simultaneously, so this is
not a certificate equating two named cross-library constants.

The complete chain also supplies the ambient cochain-complex Waldhausen structure
(`COL-0177`) and its native perfect-complex subcategory (`COL-0178`). Generic gluing belongs
to `Colib/Algebra/Homology/CochainComplex`; the categorical structure belongs to
`Colib/CategoryTheory/Waldhausen`; only the perfectness application belongs to geometry.

## Admission boundary

The comparison does not show that every perfect complex has a global bounded finite locally
free representative. In particular, old globally bounded finite locally free strictness is
not identified with global Stacks strictness, which asks for finite-free retract terms.
The global `strictToPerfect` inclusion and its K-map remain outside this slice.

## Actual Waldhausen structures and source cofibrations

`Waldhausen.complexes` retains the actual zero complex, all ambient monomorphisms and genuine
quasi-isomorphisms. Its gluing proof retains all four displayed comparison maps and commuting
equations. A matching generic biproduct helper already occurs in the higher upstream
`RingedSite.PerfectBiprod` application; the supporting proof here stays private rather than
creating another public wrapper or importing that larger application.

`RingedSpace.perfectComplexesWaldhausen` is defined for `RingedSpace.{u,u}`, with module
sections in universe `u`. Its quotient closure follows from the actual cone-to-quotient
quasi-isomorphism of a short exact sequence, an explicit specialization of
[Stacks 08CR](https://stacks.math.columbia.edu/tag/08CR). The exact sequence attached to a
pushout then proves closure for every displayed pushout along a monomorphism. The existing
`CofibrationClosedSubcategory` construction supplies the inherited Waldhausen structure.
A standard derived model is used only privately for finite direct-sum closure; it is not
an additional hypothesis of the public structure.

The archived `Quillen.Waldhausen.complexSubcategory` does not define cofibrations to be all
ambient monomorphisms for an arbitrary extension-closed subcategory. Its precise inflation
formula requires an ambient short exact sequence whose quotient stays in the subcategory.
`ColibTest.PerfectWaldhausen` reconstructs that formula for the exposed old local witness.
It proves that the actual cokernel of every ambient mono is still locally perfect, using
native quotient closure and `COL-0176`. Thus that source cofibration formula equals the
inherited ambient-mono predicate in this local-perfect case. This argument does not apply
to global `StrictPerfect`, which is not quasi-isomorphism invariant.

The test then certifies both functors of the identity-underlying full-category equivalence
as `Waldhausen.IsExact`: zero objects, cofibrations, weak equivalences and arbitrary displayed
pushouts are all checked. Both reconstructed models select the ambient zero, while the
archived exact-category construction selects a full-subcategory zero from `ContainsZero`.
Those selected terms are not claimed definitionally equal. Exactness preserves every zero
object, which is sufficient for this structural comparison. A pointed K-space comparison
would require its own identification of the actual chosen basepoints.

The certificate is between two structures reconstructed in the present environment on the
exposed source witness and the native predicate. It is not a theorem literally mentioning
the archived named `Quillen.PerfectComplexes.perfectWaldhausen` constant, and it does not by itself
prove a K-theory or global strict-perfect comparison. The K-group step below is separate.

Source correspondence, compilation and independent mathematical review are separate claims. `author_checked` records only the first.
The normal production validation is `scripts/check.sh`; kernel replay and separate downstream
client checks are not part of this comparison's admission scope.

## Canonical K-maps of the reconstructed comparison

`CategoryTheory.Waldhausen.KEquivOfExactEquivalence` (`COL-0179`) supplies the generic next
step. A categorical equivalence exact in both directions induces a multiplicative equivalence
in every degree `n : ℕ`. The forward and inverse homomorphisms are exactly the existing
canonical `KMap` of the functor and inverse. Composition, the actual unit/counit natural
isomorphisms and the identity law prove both inverse identities. This migrates the existing
Quillen `Waldhausen/Functoriality/ExactEquivalence.lean` result, not a new mathematical theorem.

The generic theorem does not assume strict preservation of the chosen zero: the canonical
K-map already incorporates the proved rebasing and based homotopy comparison. Its two
categories share the same object and morphism universes, which may differ from one another.
No small skeleton or universe lift is inserted for the original sheaf-complex categories.

`ColibTest.PerfectKEquivalence` imports the preceding exact-structure regression with
`import all`, so its private source/target objects, maps and exactness proofs are consumed
without copies. Thirteen examples and a named reflexive regression check the actual maps,
both composite homomorphism identities, both element inverse identities, both ambient-zero
identities, both unre-based realization homotopy-group maps, realization composition and the
standard local-derived-model specialization at `u + 1`. Two actual `HomotopyRel` constructions
use the unit/counit cylinders and fix the chosen basepoints; no free homotopy is silently
promoted to a based one.

This is K-invariance for the two reconstructed geometric structures, using the connective
groups of the released unnormalized IsZero-diagonal S-construction. It does not equate the
archived named `PerfectK` or independently selected zero, identify global strict-perfect
complexes with local perfect ones, establish Q/S or Gillet-Waldhausen comparison, or provide
a strict chosen-zero S-model, negative K-groups, a nonconnective spectrum, additivity or
K-zero commutativity.
