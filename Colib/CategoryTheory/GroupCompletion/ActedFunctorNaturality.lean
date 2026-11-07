/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ActedFunctoriality

/-! # Localization of original linear natural transformations -/

/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/GroupCompletion/ActedFunctorNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open CategoryTheory.Functor.LaxLeftLinear
universe u v u₁ v₁ u₂ v₂
namespace CategoryTheory.GroupCompletion.Localization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  (F G : D ⥤ E) [F.LaxLeftLinear C] [G.LaxLeftLinear C]

/-- Retain the first coordinate while applying the specified natural transformation. -/
def actedPairNatTrans (η : F ⟶ G) : actedPairFunctor (C := C) F ⟶ actedPairFunctor G where
  app X := (𝟙 X.1, η.app X.2)
  naturality {_ _} f := Prod.ext (by simp [actedPairFunctor]) (η.naturality f.2)

/-- An actual action-compatible transformation induces its original localization map. -/
def actedMapNatTrans (η : F ⟶ G)
    (hη : ∀ (s : C) (X : D),
      μₗ F s X ≫ η.app (s ⊙ₗ X) = s ⊴ₗ η.app X ≫ μₗ G s X) :
    actedMapFunctor (C := C) F ⟶ actedMapFunctor (C := C) G :=
  ActionLocalization.mapNatTrans (actedPairFunctor F) (actedPairNatTrans F G η) (by
    intro s X
    apply Prod.ext
    · change 𝟙 _ ≫ 𝟙 _ = s ◁ 𝟙 _ ≫ 𝟙 _
      simp
    · exact hη s X.2)

/-- The component is exactly the original acted-on transformation, with unit denominator. -/
theorem actedMapNatTrans_app (η : F ⟶ G)
    (hη : ∀ (s : C) (X : D),
      μₗ F s X ≫ η.app (s ⊙ₗ X) = s ⊴ₗ η.app X ≫ μₗ G s X)
    (X : Localization C D) :
    (actedMapNatTrans F G η hη).app X =
      ActionLocalization.ofHom (C := C)
        (X := (X.obj.1, F.obj X.obj.2)) (Y := (X.obj.1, G.obj X.obj.2))
        (𝟙 X.obj.1, η.app X.obj.2) := rfl

end CategoryTheory.GroupCompletion.Localization
