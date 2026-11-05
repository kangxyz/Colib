/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.AffineBaseChange

/-!
# The original fixed-open coefficient functor

The source open immersion is pulled back once at each coefficient algebra. The original
pullback lifts give a strict functor to opposite schemes. The specified inclusions form a
natural transformation from the original affine coefficient functor. At the identity algebra
we retain the existing projection isomorphism, rather than identifying its source with the
original open. No quasi-compactness assumption is used.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.AffineOpenPair

variable {R : CommRingCat.{u}} {U : AlgebraicGeometry.Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Each coefficient algebra retains its specified original pulled-back open. -/
def openFunctor : Under R ⥤ AlgebraicGeometry.Scheme.{u}ᵒᵖ where
  obj a := op (openSpace j a)
  map f := (openMap j f).op
  map_id a := by rw [openMap_id]; rfl
  map_comp f g := by rw [openMap_comp]; rfl

/-- The affine base of the same original coefficient diagram. -/
def ambientFunctor (R : CommRingCat.{u}) : Under R ⥤ AlgebraicGeometry.Scheme.{u}ᵒᵖ :=
  Under.forget R ⋙ AlgebraicGeometry.Scheme.Spec.rightOp

/-- The actual inclusions give a natural transformation with the original pullback square. -/
def inclusionTransformation : ambientFunctor R ⟶ openFunctor j where
  app a := (inclusion j a).op
  naturality _ _ f := by
    apply Quiver.Hom.unop_inj
    exact (openMap_inclusion j f).symm

/-- The original map, rather than a chosen comparison, is the coefficient action. -/
theorem openFunctor_map_unop {a b : Under R} (f : a ⟶ b) :
    ((openFunctor j).map f).unop = openMap j f := rfl

/-- The identity-algebra fiber is related to the original open by its actual projection. -/
theorem openFunctor_identityProjection :
    (identityProjectionIso j).hom ≫ j =
      ((inclusionTransformation j).app (Under.mk (𝟙 R))).unop :=
  identityProjectionIso_inclusion j

end AlgebraicGeometry.Scheme.AffineOpenPair

attribute [colib_tag "COL-0149",
  stacks 01JY "Background for the chosen affine-base-change functor, not its strict formulas"]
  AlgebraicGeometry.Scheme.AffineOpenPair.openFunctor
  AlgebraicGeometry.Scheme.AffineOpenPair.ambientFunctor
  AlgebraicGeometry.Scheme.AffineOpenPair.inclusionTransformation
  AlgebraicGeometry.Scheme.AffineOpenPair.openFunctor_map_unop
  AlgebraicGeometry.Scheme.AffineOpenPair.openFunctor_identityProjection
