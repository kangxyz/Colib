/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.DiagonalAction
public import Colib.CategoryTheory.GroupCompletion.Functoriality

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/ActedFunctoriality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Localization of genuine linear functors in the acted-on coordinate -/

@[expose] public section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open CategoryTheory.Functor.LaxLeftLinear
universe u v u' v' u'' v''
namespace CategoryTheory.GroupCompletion.Localization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
  {E : Type u''} [Category.{v''} E] [MonoidalLeftAction C E]
  (F : D ⥤ E) [F.LaxLeftLinear C]

/-- Keep the denominator coordinate and apply the original acted-on functor. -/
def actedPairFunctor : C × D ⥤ C × E := (𝟭 C).prod F

/-- The product lineator fixes the denominator and uses the original acted-on lineator. -/
instance actedPairFunctorLinear : (actedPairFunctor (C := C) F).LaxLeftLinear C where
  μₗ s X := (𝟙 _, μₗ F s X.2)
  μₗ_naturality_left f X := Prod.ext (by
    change f ▷ X.1 ≫ 𝟙 _ = 𝟙 _ ≫ f ▷ X.1
    simp) (μₗ_naturality_left F f X.2)
  μₗ_naturality_right s _ _ f := Prod.ext (by
    change s ◁ f.1 ≫ 𝟙 _ = 𝟙 _ ≫ s ◁ f.1
    simp) (μₗ_naturality_right F s f.2)
  μₗ_associativity s t X := Prod.ext (by
    change 𝟙 _ ≫ (α_ s t X.1).hom = (α_ s t X.1).hom ≫ s ◁ 𝟙 _ ≫ 𝟙 _
    simp) (μₗ_associativity F s t X.2)
  μₗ_unitality X := Prod.ext (by
    change (λ_ X.1).hom = 𝟙 _ ≫ (λ_ X.1).hom
    simp) (μₗ_unitality F X.2)

/-- The genuine induced functor on localizations, retaining the original denominator. -/
def actedMapFunctor : Localization C D ⥤ Localization C E :=
  ActionLocalization.mapFunctor (actedPairFunctor F)

/-- The original denominator is unchanged on objects. -/
theorem actedMapFunctor_obj (X : Localization C D) :
    (actedMapFunctor F).obj X = ⟨(X.obj.1, F.obj X.obj.2)⟩ := rfl

/-- The actual map on a quotient representative, with its lineator retained. -/
theorem actedMapFunctor_mkHom {X Y : C × D} (s : C)
    (f : s ⊗ X.1 ⟶ Y.1) (g : s ⊙ₗ X.2 ⟶ Y.2) :
    (actedMapFunctor F).map (mkHom s f g) =
      mkHom (X := (X.1, F.obj X.2)) (Y := (Y.1, F.obj Y.2))
        s f (μₗ F s X.2 ≫ F.map g) := by
  change mkHom (X := (X.1, F.obj X.2)) (Y := (Y.1, F.obj Y.2))
    s (𝟙 _ ≫ f) (μₗ F s X.2 ≫ F.map g) = _
  rw [Category.id_comp]

/-- A unit-denominator arrow retains its first coordinate under descent. -/
theorem actedMapFunctor_ofHom {X Y : C × D} (f : X ⟶ Y) :
    (actedMapFunctor F).map (ActionLocalization.ofHom (C := C) f) =
      ActionLocalization.ofHom (C := C) (f.1, F.map f.2) :=
  ActionLocalization.mapFunctor_ofHom (actedPairFunctor F) f

end CategoryTheory.GroupCompletion.Localization
