# Native scheme K/G-theory and the canonical comparison

COL-0285 migrates the scheme constructions from Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd` to the pinned Mathlib and Stacks objects.
It consumes general exact-category and small-model Quillen K-theory. The geometric
application lives under `Colib.AlgebraicGeometry.KTheory`, with its native sheaf
and exact-category foundations under `Colib.AlgebraicGeometry.Scheme`.
No alternate category, compatibility shell or Aglib dependency is introduced.

## Native constructions and actual maps

For `X : Scheme.{u}`, vector-bundle K-theory uses the native `X.Vect` category of
finite locally free module sheaves. Its conflations are the actual ambient short
exact sequences, not just globally split sequences. Coherent G-theory uses the
native abelian category `SheafOfModules.CoherentModules X.ringCatSheaf`. The stated
G-group interface retains the locally Noetherian hypothesis. Both use the existing
`ExactStructure.SmallK.{u+1}` and Mathlib's actual `SmallModel`. No smaller-universe
essential-smallness assertion is made.

The canonical comparison is the original K-map of the literal inclusion of
vector bundles into coherent sheaves. Open restriction is the actual
`Scheme.Modules.restrictFunctor`. Its identity and composition isomorphisms lift
Mathlib's existing comparisons, retaining their components. The induced K- and
G-maps satisfy strict identity and composition equalities, and K-to-G commutes
with those homomorphisms. Every group-level statement includes degree zero.
The two regression modules contain twenty-four examples, including explicit
upper-universe and degree-zero checks.

## Literature and boundaries

Quillen, *Higher algebraic K-theory: I*, Section 7, subsection 1, equation (1.1)
and its following paragraph, p. 124, define the canonical comparison. That section
has standing Noetherian and separated hypotheses. The present construction is
cited as an adaptation with its stated hypotheses, not a verbatim restatement.

This item does not assert that K-to-G is an equivalence. The regular-scheme
comparison via native coherent perfectness and actual finite resolutions is a
separate continuation. It also makes no identification with perfect-complex
Waldhausen K-theory, general scheme-open localization theorem, or nonconnective
claim. In particular, the affine finite-module G-zero localization tail is not
promoted to a general projective K-zero statement.
