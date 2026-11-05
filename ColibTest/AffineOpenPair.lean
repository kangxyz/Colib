module

import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Functor
import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Compactness

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair

universe u

variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)

example (a : Under R) : openSpace j a = pullback j (Spec.map a.hom) := rfl

example (a : Under R) : inclusion j a = pullback.snd j (Spec.map a.hom) := rfl

example {a b : Under R} (f : a ⟶ b) :
    openMap j f ≫ projection j a = projection j b := openMap_projection j f

example {a b : Under R} (f : a ⟶ b) :
    openMap j f ≫ inclusion j a = inclusion j b ≫ Spec.map f.right :=
  openMap_inclusion j f

example [IsOpenImmersion j] (a : Under R) :
    openMap j (𝟙 a) = 𝟙 (openSpace j a) := openMap_id j a

example [IsOpenImmersion j] {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c) :
    openMap j (f ≫ g) = openMap j g ≫ openMap j f := openMap_comp j f g

example [IsOpenImmersion j] {a b : Under R} (f : a ⟶ b) :
    ((openFunctor j).map f).unop = openMap j f := rfl

example [IsOpenImmersion j] (a : Under R) :
    ((inclusionTransformation j).app a).unop = inclusion j a := rfl

example : (identityProjectionIso j).hom = projection j (Under.mk (𝟙 R)) := rfl

example : (identityProjectionIso j).hom ≫ j = inclusion j (Under.mk (𝟙 R)) :=
  identityProjectionIso_inclusion j

example [CompactSpace U] (a : Under R) : CompactSpace (openSpace j a) :=
  compactSpace_openSpace j a
