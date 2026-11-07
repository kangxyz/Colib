# Principal closed/open G-localization

COL-0274 identifies the existing principal supported G-theory with G-theory of
the actual quotient ring. It then transports the already proved connective
localization sequence, retaining its canonical closed and open maps.

## Constructions and exact maps

`Colib/Algebra/Category/FGModuleCat/PrincipalClosedSupport.lean` restricts actual
finite quotient-ring modules along the native quotient map. Quotient-map
surjectivity proves fullness; the genuine quotient action on an annihilated
module proves essential surjectivity onto exactly the r-killed objects.
Restriction preserves finite colimits in general and finite limits over a
Noetherian base. The exact functor's underlying functor is the original lift.

`Colib/CategoryTheory/Abelian/Devissage/CentralEndomorphism.lean` constructs a
finite filtration of any object killed by a power of a natural endomorphism.
Each actual conflation is its image inclusion followed by its cokernel; the
nilpotence exponent drops on the image and the cokernel is killed outright.
Exponent zero gives a genuine zero object. The killed property is closed under
subobjects, quotients and finite products, without requiring extension closure.
`Colib/Algebra/Category/FGModuleCat/ScalarFiltration.lean` realizes this natural
endomorphism as actual scalar multiplication through a fully faithful functor.

The three `Colib/KTheory/GTheory/FiniteModules/Principal*.lean` leaves apply
these constructions inside the existing supported full subcategory of the
native SmallModel. They factor the original small-model quotient restriction
through r-killed supported objects and prove that factor is an equivalence.
Its source retains the original transported exact structure, and its target
uses the standard abelian structure. The existing homotopical dévissage theorem
then identifies its K-theory with the supported term.

The forward homomorphism of `closedSupportGEquiv` is exactly
`closedSupportedKMap`. Composing it with the original supported inclusion is
exactly `closedRestrictionExact.smallKMap`. The closed boundary is defined only
as the original localization boundary followed by the inverse proved
equivalence. All three recurring range/kernel equalities and the terminal
homotopical G-zero surjection follow for those actual maps.

## Hypotheses and limits

The full sequence requires a commutative Noetherian ring `R : Type u`, any
`r : R`, and `Small.{v,u} R` for native localization on module universe `v`.
The smallness condition is automatic when `v = u`. The lower quotient
restriction equivalence needs neither Noetherianity nor smallness. Zero rings,
r = 0 and units are allowed; no domain, regular-element or proper-ideal
hypothesis is introduced. Filtration lengths are objectwise finite, with no
uniform bound.

This is a connective affine finite-module theorem. It proves no general
scheme-open localization, negative G-theory or boundary-symbol formula. In
particular, a formula sending a unit symbol to a quotient class would require
its own normalization and appropriate regularity hypotheses.

## Pinned correspondence

The proof adapts these files at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`:

- `Aglib/CategoryTheory/ExactCategory/Filtration/CentralEndomorphism.lean`:
  the actual finite image tower and scalar realization.
- `Aglib/Algebra/Category/FGModuleCat/PrincipalClosedSupport.lean`:
  native quotient restriction and annihilated objects.
- `Aglib/Algebra/Category/FGModuleCat/PrincipalSupportSmallModel.lean` and
  `ClosedSupportSmallModel.lean`: the existing supported model and exact
  quotient-restriction factorization.
- `Devissage/CentralEndomorphism.lean`: the dévissage application.
- `AlgebraicGeometry/Scheme/Coherent/Affine/ClosedDevissage.lean`: the
  finite-module G-equivalence, original pushforward and transported sequence.

The new finite-module endpoint is placed under G-theory, without importing
scheme or coherent-sheaf models. Weibel, *The K-book*, V.4.1, page 33, and V.5.1,
page 35, are the dévissage and localization references respectively.

## Validation scope

The thirteen principal closed/open regression examples cover all lowest-degree
positions, literal map identities, zero and unit elements, the lower quotient
equivalence without Noetherianity or smallness, and equal universes. Independent
mathematical review checks the complete finite image-filtration and quotient
restriction argument, the original forward map and transported boundary, and
all degree-zero claims. The [batch overview](README.md#validation-scope) records
the current native validation scope. Verification records remain private rather
than repository deliverables.
