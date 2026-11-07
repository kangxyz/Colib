# Actual iterated S-prespectra and coarse endotransformation tracks

This contribution retains the original maps and continuous families from Quillen
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Library items COL-0276,
COL-0277 and COL-0278 record the prespectrum comparison, whole homotopies and
composition, and the grading-coarse endotransformation endpoints.

## One native category and the actual finite stages

The existing `CategoryTheory.Waldhausen.SmallWaldhausenCategory`, its arbitrary-exact
`Hom`, and its category instance move unchanged to the lower `SmallCategory`
owner. Its original `KFunctor` remains unchanged. Strict chosen-zero-preserving
maps form Mathlib's `WideSubcategory preservesZero` of that same category.
The source's separate `IteratedS.Model` and strict `Model.Hom` are not copied.

The second stage is the diagonal of the actual quotient-row S-constructions.
The one-row embedding followed by ordinal restriction gives the original
suspension cylinder. Both endpoints are literal zero rows, and the entire
chosen-zero track is constant. Recursing through actual rows and the native
diagonal functor constructs all finite stages and their original cylinders.
Every stage retains its exact-functor naturality and proved zero identities.

Realization gives the actual continuous based loop structure maps. The
prespectrum's zero space is the based loop space of the first S-realization;
its positive spaces are the successive realized stages. Its degree-zero
structure map is the identity. Strict structure squares, identity and
composition are proved. No existing sequential-prespectrum object was found
in the pinned native libraries; the generic `Topology.LoopPrespectrum` owner
therefore provides the single definition used by this construction.

Native `AsSmall` handles independent original object and morphism universes.
`originalZeroSpaceEquiv` identifies the unchanged `W.K n` with the actual
zero-space homotopy set in degree `n`. The comparison is multiplicative in
positive zero-space degree. Strict functoriality retains an explicit equality
of chosen zeros. For arbitrary exact functors, `exactOriginalPrespectrumMap`
uses the existing canonical zero rebase, and
`exactOriginalZeroSpaceEquiv_naturality` retains the original public `KMap`.
Source and target retain the original common pair of category universes.

## Whole weak-transformation homotopies and composition

An objectwise weak natural transformation gives an actual continuous based
homotopy at every level. The row-insertion square proves compatibility with
each original structure map for every homotopy time and every independent
structure parameter. At level zero, the homotopy evaluates the original
stage homotopy on the actual based loop. Canonical conjugation supplies the
same construction for arbitrary exact functors without adding chosen-zero
equality hypotheses.

The simplicial composition triangle is the original map with parameter
`Delta[2]`. Its faces are `delta_2 = eta`, `delta_0 = theta` and
`delta_1 = eta >> theta`, through their original cylinders. The whole
zero-vertex triangle is constant. The actual realization product comparison
retains an independent suspension parameter and joint continuity.

Affine interpolation compares the long edge with the two short edges. The
last face is exactly the original half-interval concatenation. This yields
`prespectrumTransformationCompositionHomotopy` on the strict chosen-zero
subcategory, relative to both endpoint maps and the entire basepoint line.
Level zero retains a separate loop-evaluation coordinate. No coherence law
or pointwise family of homotopy classes is supplied as an input.

## Genuine relative cancellation and the coarse endpoint

The generic relative homotopies retain three independent coordinates:
comparison time, original track time and the structure-map parameter.
Horizontal composition uses continuous square interchange before
concatenation, without a local-compactness assumption on prespectrum spaces.
Associativity, removal of constant tracks and reverse-track cancellation use
the actual Mathlib path reparameterizations. The cancellation families are
jointly continuous and fix their prescribed boundary.

The existing double-loop transpose is extracted once into
`Path.DoubleLoopTranspose`, with its literal parameter formula. Its original
fiber consumer uses this same lower operation; no compatibility alias or
second transpose definition remains. Parameter-looping retains the formula
`structureMap n gamma t s = structureMap n (gamma s) t`.

For an exact functor into the actual grading-coarse target, every component
of an endotransformation is weak because its endpoint grades coincide.
`zeroEndotransformation` has the original component given by the two arrows
through the chosen zero object. It absorbs an endotransformation before
realization. Its actual composition triangle and continuous reverse-track
cancellation contract the original canonically normalized self-track.
Both endpoints, the whole point line and the independent structure
coordinate remain fixed.

`Cofinality.Grading.exactEndotransformationContraction` is a contraction of
that self-track. It does not assert a nullhomotopy of the underlying map or
contractibility of the target. For the null-loop endpoint, the target map
`j` and a nullhomotopy `N` of its composite with the original map are
separate inputs. `exactEndotransformationNullLoopHomotopy` retains the actual
word `N.symm.trans (H.trans N)`, contracts its middle self-track and cancels
the two original null legs. Its conclusion is a whole homotopy to zero in
the parameter-looped target. Object, morphism and grade universes remain
independent, with the original common source/target category-universe pair.

## Source and literature correspondence

The pinned `Waldhausen/SConstruction/Iterated` sources `Double`, `LoopMap`,
`Functoriality`, `Category`, `Stages` and `Prespectrum` supply the actual
construction. `NaturalHomotopy`, `StructureHomotopy`, `ExactMaps` and
`PrespectrumHomotopy` supply the original normalized homotopies.
`NaturalTriangle`, `TriangleStructure`, `TriangleRealization`,
`TriangleComposition` and `PrespectrumCompositionHomotopy` supply the actual
relative composition. `EndotransformationContraction` and
`Waldhausen/Cofinality/EndotransformationHomotopy` supply both final endpoints.
Their generic topology is retained in its lower prespectrum, path and
realization owners. Original authorship and Apache-2.0 notices are preserved.

Thomason--Trobaugh, Sections 1.5.3--1.5.4, pages 260--261, supplies the
iterated-S and weak-natural-transformation homotopy background. The explicit
composition triangle, relative cancellation and coarse self-track contraction
are recorded as proved refinements, not as verbatim statements from that text.

The separate `exactOriginalOmegaSpectrumMap` packaging declaration remains
outside this prespectrum contribution. The three cone-specific declarations
`mappingConeLoopTransition`, `mappingConeLoopTransition_apply` and
`mappingConeLoopTransitionAlong` also remain outside it. No Omega-equivalence,
spectrum localization theorem or nonconnective K-theory is asserted.

## Verification boundary

Focused regressions cover original maps, universe parameters, exact faces,
the whole based families, independent coordinates, native transpose and
the supplied null legs. Native compiler, text/declaration lint and production
axiom checks are distinct from source correspondence and independent
mathematical review. Integration also rebuilds consumers of the moved native
definitions and checks the generated root and Library bindings.

The previously published cofinality/K-zero layer at commit
`28de0953f88db088fba1dbb632dbb47419f391f8` passed
[its original whole-library CI](https://github.com/kangxyz/colib/actions/runs/42376571892).
That result does not certify this later coherent-track contribution, which
has its own original whole-library release gate. No local whole-library pass,
kernel replay or separate downstream-client check is inferred from focused
compilation. Detailed internal validation records remain outside the repository.
