# Native Waldhausen fibration

The implementation is migrated from Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the existing Colib
unnormalized diagonal `IsZero` S-construction and its canonical maps.
The mathematical reference is Waldhausen, *Algebraic K-theory of spaces*,
Section 1.6, Theorem 1.6.4 and its proof, pages 350–352.

## Public mathematical surface

- **COL-0251:** the fine Waldhausen structure on the full category of coarse
  acyclic objects, its exact inclusion, and weak-cofibration detection by the
  actual displayed cofiber.
- **COL-0252:** the original canonical comparison into the path-space homotopy
  fiber of change of weak equivalences. Its entire path is the reversed
  zero-to-inclusion nullhomotopy. Projection is the original acyclic inclusion.
- **COL-0253:** the original relative-row total-tail fiber comparison is weak,
  including components. The proof supplies all transition comparisons before
  applying the two-sided-bar zero-row fiber theorem.
- **COL-0254:** the original canonical comparison is a weak homotopy equivalence
  in arbitrary object and morphism universes. Its assumptions are coarse
  two-out-of-three, the extension axiom, exact base-category joint-cylinder data and an
  actual second-endpoint section. No fiber-equivalence premise remains.

The existing additivity item COL-0219 also includes the actual unbased space-level
homotopy between the realized middle functor and the quotient-before-subobject
coproduct functor. It is the homotopy used in the relative-row argument.

## Proof and native ownership

Categorical foundations belong to `CategoryTheory.Waldhausen`: actual extension
objects, Reedy quotient rows and pushouts, joint factorizations, acyclic objects,
mixed weak chains and relative rows. Realization and K-theory comparisons belong
to `KTheory.Waldhausen`. Generic compact lifting, weak pushout, homotopy-fiber and
weak-cartesian realization results retain their topology or theorem-B owners.

The proof first identifies actual relative-row fibers and ordinal transitions.
General weak-cartesian skeletal assembly and the two-sided bar yield the total
relative fiber. Mixed nerves and the structural cylinder identify coarse
evaluation. The all-weak contraction and common-base fiber square then identify
the resulting comparison with the original canonical map, as an equality of
both source coordinates and complete paths.

Mathlib `AsSmall.{0}` is used directly for the universe reduction. The source's
mere `SmallModel` alias is removed. Pulled-back morphism classes, exact up/down
functors and actual realization homeomorphisms transport the full canonical
nullhomotopy, not only its endpoints. Existing native products, sum functors,
realization maps and homotopy-group maps are reused rather than redeclared.
Initial intervals and their canonical quotient arrow are shared by exact-category
reconstruction and generic Waldhausen row descent.

Some source modules also contain specialized complex-category applications.
Those tails are outside this contribution; the generic theorems and their
structural hypotheses are retained. The result is an adaptation for the
existing unnormalized model, not a newly asserted strict chosen-zero model
comparison. A connective long exact sequence is not part of this item.

## Correspondence and review boundary

The cited primary text was checked on 2026-11-06 using the published article
and its [Rochester mirror](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/waldhausen1.pdf).
Its cylinder/saturation/extension framework is reflected by the explicit
structural hypotheses above; no equivalence of every classical cylinder
formulation is asserted.

A separate read-only mathematical review compared the complete canonical-map,
global-comparison, general-comparison, weak-total-fiber and six AsSmall modules
with the pinned source. It also inspected the invoked row, all-weak contraction,
full-path transport and zero-bar interfaces. It found no regression in that
scope. This is not an exhaustive independent review of every transitive
foundation. Lean compilation, source correspondence and that bounded review
are distinct evidence. Final validation is reported with the integration
commit; large build logs and machine-generated validation records are not
maintained as mathematical source.
