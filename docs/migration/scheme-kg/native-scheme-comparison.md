# Native scheme K/G-theory and the regular comparison

This slice migrates the scheme constructions from Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd` to the pinned Mathlib and Stacks objects.
It depends on the general exact-category, SmallModel and Quillen resolution theorems.
The geometric application lives under `Colib.AlgebraicGeometry.KTheory`; its native
sheaf and exact-category foundations live under `Colib.AlgebraicGeometry.Scheme`.
No alternate category, compatibility shell or Aglib dependency is introduced.

## Construction and canonical maps: COL-0285

For `X : Scheme.{u}`, vector-bundle K-theory uses the native `X.Vect` category of
finite locally free module sheaves. Its conflations are the actual ambient short
exact sequences, not just globally split sequences. Coherent G-theory uses the
native abelian category `SheafOfModules.CoherentModules X.ringCatSheaf`. The stated
G-group interface retains the locally Noetherian hypothesis. Both constructions
use the existing `ExactStructure.SmallK.{u+1}` and Mathlib's actual `SmallModel`.
No essential-smallness claim in the smaller universe is made.

The comparison is the original K-map of the literal inclusion of vector bundles
into coherent sheaves. Open restriction is the actual `Scheme.Modules.restrictFunctor`.
Its identity and composition isomorphisms lift Mathlib's existing comparisons,
with unchanged components. The induced K- and G-maps satisfy strict identity and
composition equalities, and K-to-G commutes with those maps. Every group-level
statement covers all natural degrees, including zero.

## Regular comparison: COL-0286

The final equivalence assumes exactly `CompactSpace X`, `HasResolutionProperty X`
and `IsRegular X`. Regularity supplies local Noetherianity. Native Stacks Tag 0FDC
makes a coherent sheaf, placed in degree zero, perfect. Tag 0F8E supplies an actual
bounded finite locally free complex with a quasi-isomorphism to the degree-zero
sheaf. The bounded
complex result registered as COL-0271 extracts an objectwise finite admissible
resolution. Its actual objects and arrows lift to the native coherent category.
The proved Quillen resolution theorem then applies through the original upper
small-model exact functors.

`KToGRegularEquiv` has definitionally the original `KToG` as its forward
homomorphism. No uniform resolution length, finite dimension, separatedness or
assertion of global projectivity of vector bundles is required. The intermediate
finite-resolution hypothesis is discharged from the geometric assumptions in
the final theorem, rather than retained as a theorem-shaped assumption.

## Literature and boundaries

Quillen, *Higher algebraic K-theory: I*, Section 7, subsection 1, equation (1.1)
and its following paragraph, p. 124, define the canonical comparison and give its
regular-scheme conclusion. That section has standing Noetherian and separated
hypotheses. The result here is therefore cited as an adaptation with the explicit
hypotheses above, not as a verbatim restatement. Section 4, Corollary 1 and its
proof, pp. 109–110, are the resolution-theorem ingredient. Stacks Tags 0FDC and
0F8E are geometric inputs, not citations for a K-group isomorphism they do not
state.

This slice does not identify vector-bundle Quillen K-theory with the existing
perfect-complex Waldhausen construction. It proves neither general scheme-open
K-localization nor nonconnective K-theory. The affine finite-module G-localization
results retain their own assumptions and canonical maps. In particular, their
surjective G-zero tail is not promoted to a general projective K-zero statement.
