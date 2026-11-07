/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.SecondProjectionLinear

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/IteratedFiberEntry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The actual entry of a fixed fiber into the iterated localization -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- The original actor category inserted over a fixed acted-on object. -/
def fixedSecondEntry (X : D) : C ⥤ Localization C D :=
  secondFiberEntry X ⋙ Functor.Fiber.fiberInclusion

@[simp]
theorem fixedSecondEntry_obj (X : D) (A : C) :
    (fixedSecondEntry X).obj A = ⟨(A, X)⟩ := rfl

@[simp]
theorem fixedSecondEntry_map (X : D) {A B : C} (f : A ⟶ B) :
    (fixedSecondEntry X).map f = secondFiberHom X f := rfl

variable [BraidedCategory C]
attribute [local instance] firstCoordinateLeftAction

instance fixedSecondEntryLinear (X : D) : (fixedSecondEntry (C := C) X).LaxLeftLinear C where
  μₗ s A := secondFiberHom X (β_ A s).hom
  μₗ_naturality_left {s t} f A := by
    change (f ⊵ₗ (fixedSecondEntry X).obj A) ≫ secondFiberHom X (β_ A t).hom =
      secondFiberHom X (β_ A s).hom ≫ secondFiberHom X (f ▷ A)
    rw [firstCoordinateLeftAction_actorMap]
    erw [secondFiberHom_comp, secondFiberHom_comp]
    exact congrArg (secondFiberHom X) (braiding_naturality_right A f)
  μₗ_naturality_right s {A B} f := by
    change s ⊴ₗ secondFiberHom X f ≫ secondFiberHom X (β_ B s).hom =
      secondFiberHom X (β_ A s).hom ≫ secondFiberHom X (s ◁ f)
    rw [firstCoordinateLeftAction_map, firstCoordinateTranslation_secondFiberHom,
      secondFiberHom_comp, secondFiberHom_comp]
    exact congrArg (secondFiberHom X) (braiding_naturality_left f s)
  μₗ_associativity s t A := by
    change secondFiberHom X (β_ A (s ⊗ t)).hom ≫
        secondFiberHom X (α_ s t A).hom =
      (secondFiberHom X (A ◁ (β_ t s).inv) ≫
        secondFiberHom X (α_ A t s).inv) ≫
          s ⊴ₗ secondFiberHom X (β_ A t).hom ≫
            secondFiberHom X (β_ (t ⊗ A) s).hom
    rw [firstCoordinateLeftAction_map, firstCoordinateTranslation_secondFiberHom]
    simp only [secondFiberHom_comp]
    apply congrArg (secondFiberHom X)
    rw [braiding_tensor_left_hom]
    simp only [Category.assoc]
    rw [← hexagon_forward_assoc]
    simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [braiding_naturality_right_assoc]
    simp only [inv_hom_whiskerRight_assoc]
  μₗ_unitality A := by
    change secondFiberHom X (A ◁ 𝟙 (𝟙_ C)) ≫ secondFiberHom X (ρ_ A).hom =
      secondFiberHom X (β_ A (𝟙_ C)).hom ≫ secondFiberHom X (λ_ A).hom
    rw [secondFiberHom_comp, secondFiberHom_comp]
    apply congrArg (secondFiberHom X)
    simp only [whiskerLeft_id, Category.id_comp, braiding_leftUnitor]

/-- Keep the first actor coordinate and insert the second over `X`. -/
def fixedSecondPairEntry (X : D) : C × C ⥤ C × Localization C D :=
  (𝟭 C).prod (fixedSecondEntry X)

instance fixedSecondPairEntryLinear (X : D) :
    (fixedSecondPairEntry (C := C) X).LaxLeftLinear C where
  μₗ s A := (𝟙 _, secondFiberHom X (β_ A.2 s).hom)
  μₗ_naturality_left f A := by
    apply Prod.ext
    · change (f ▷ A.1) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ A.1)
      simp
    · exact Functor.LaxLeftLinear.μₗ_naturality_left (fixedSecondEntry X) f A.2
  μₗ_naturality_right s _ _ f := by
    apply Prod.ext
    · change (s ◁ f.1) ≫ 𝟙 _ = 𝟙 _ ≫ (s ◁ f.1)
      simp
    · exact Functor.LaxLeftLinear.μₗ_naturality_right (fixedSecondEntry X) s f.2
  μₗ_associativity s t A := by
    apply Prod.ext
    · change 𝟙 _ ≫ (α_ s t A.1).hom = (α_ s t A.1).hom ≫ s ◁ 𝟙 _ ≫ 𝟙 _
      simp
    · exact Functor.LaxLeftLinear.μₗ_associativity (fixedSecondEntry X) s t A.2
  μₗ_unitality A := by
    apply Prod.ext
    · change (λ_ A.1).hom = 𝟙 _ ≫ (λ_ A.1).hom
      simp
    · exact Functor.LaxLeftLinear.μₗ_unitality (fixedSecondEntry X) A.2

/-- The actual localization entry whose image lies in one strict fiber. -/
def iteratedFiberEntry (X : D) : Localization C C ⥤ Localization C (Localization C D) :=
  ActionLocalization.mapFunctor (fixedSecondPairEntry X)

@[simp]
theorem iteratedFiberEntry_obj (X : D) (A : Localization C C) :
    (iteratedFiberEntry X).obj A = ⟨(A.obj.1, ⟨(A.obj.2, X)⟩)⟩ := rfl

@[simp]
theorem iteratedFiberEntry_mkHom (X : D) {A B : C × C}
    (s : C) (f : s ⊗ A.1 ⟶ B.1) (g : s ⊗ A.2 ⟶ B.2) :
    (iteratedFiberEntry X).map (mkHom s f g) =
      mkHom (X := (A.1, (⟨(A.2, X)⟩ : Localization C D)))
        (Y := (B.1, (⟨(B.2, X)⟩ : Localization C D))) s f
          (secondFiberHom X ((β_ A.2 s).hom ≫ g)) := by
  change ActionLocalization.mkHom
    (X := (A.1, (⟨(A.2, X)⟩ : Localization C D)))
    (Y := (B.1, (⟨(B.2, X)⟩ : Localization C D))) ⟨s, (𝟙 _ ≫ f,
    secondFiberHom X (β_ A.2 s).hom ≫ secondFiberHom X g)⟩ = _
  rw [Category.id_comp, secondFiberHom_comp]
  rfl

@[simp]
theorem iteratedFiberEntry_projection_map (X : D) {A B : Localization C C}
    (f : A ⟶ B) :
    iteratedSecondProjection.map ((iteratedFiberEntry X).map f) =
      𝟙 (⟨X⟩ : ActionLocalization C D) := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective A.obj B.obj f
  change iteratedSecondProjection.map
    ((iteratedFiberEntry X).map (mkHom r.denom r.map.1 r.map.2)) = _
  rw [iteratedFiberEntry_mkHom, iteratedSecondProjection_mkHom,
    secondProjection_secondFiberHom]

/-- The entry lands in the actual strict fiber, not merely a comma model. -/
def iteratedStrictFiberEntry (X : D) :
    Localization C C ⥤ Functor.Fiber (iteratedSecondProjection (C := C)) ⟨X⟩ where
  obj A := ⟨(iteratedFiberEntry X).obj A, rfl⟩
  map f := ⟨(iteratedFiberEntry X).map f, by
    rw [← iteratedFiberEntry_projection_map X f]
    exact IsHomLift.map _ _⟩
  map_id A := by
    apply Subtype.ext
    exact (iteratedFiberEntry X).map_id A
  map_comp f g := by
    apply Subtype.ext
    exact (iteratedFiberEntry X).map_comp f g

end CategoryTheory.GroupCompletion.Localization
