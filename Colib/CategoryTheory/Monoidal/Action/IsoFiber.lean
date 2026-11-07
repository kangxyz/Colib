/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.FiberedCategory.IsoFiber.Basic
public import Colib.CategoryTheory.Monoidal.TrivialAction
public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Monoidal/Action/IsoFiber.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The induced action on an actual isomorphism fiber -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u₁ v₁ u₂ v₂
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Functor.LaxLeftLinear
namespace CategoryTheory.IsoFiber
variable {S : Type u} [Category.{v} S] [MonoidalCategory S]
  {C : Type u₁} [Category.{v₁} C] [MonoidalLeftAction S C]
  {B : Type u₂} [Category.{v₂} B]

/-- Only the projection target receives the trivial action. -/
local instance trivialTarget : MonoidalLeftAction S B := MonoidalLeftAction.trivial S B

variable (F : C ⥤ B) [F.LaxLeftLinear S]
  [∀ (s : S) (X : C), IsIso (μₗ F s X)] (b : B)

/-- Equality in the actual isomorphism fiber is detected by its original arrow. -/
lemma action_hom_ext {X Y : IsoFiber F b} {f g : X ⟶ Y}
    (h : f.hom.right = g.hom.right) : f = g := by
  apply ObjectProperty.hom_ext
  exact StructuredArrow.hom_ext _ _ h

/-- Translate the original object and transport its specified structure isomorphism
using the actual projection lineator. -/
def actionObj (s : S) (X : IsoFiber F b) : IsoFiber F b :=
  mk F b (s ⊙ₗ X.obj.right) (asIso X.obj.hom ≪≫ asIso (μₗ F s X.obj.right))

/-- The action on fiber morphisms is the unchanged original action map. -/
def actionMap (s : S) {X Y : IsoFiber F b} (f : X ⟶ Y) :
    actionObj F b s X ⟶ actionObj F b s Y :=
  ⟨StructuredArrow.homMk (s ⊴ₗ f.hom.right) (by
    change (X.obj.hom ≫ μₗ F s X.obj.right) ≫ F.map (s ⊴ₗ f.hom.right) =
      Y.obj.hom ≫ μₗ F s Y.obj.right
    rw [Category.assoc, ← μₗ_naturality_right]
    change X.obj.hom ≫ F.map f.hom.right ≫ μₗ F s Y.obj.right = _
    rw [← Category.assoc, StructuredArrow.w])⟩

/-- Actor morphisms act through their original source-category maps. -/
def actorMap {s t : S} (f : s ⟶ t) (X : IsoFiber F b) :
    actionObj F b s X ⟶ actionObj F b t X :=
  ⟨StructuredArrow.homMk (f ⊵ₗ X.obj.right) (by
    change (X.obj.hom ≫ μₗ F s X.obj.right) ≫ F.map (f ⊵ₗ X.obj.right) =
      X.obj.hom ≫ μₗ F t X.obj.right
    rw [Category.assoc, ← μₗ_naturality_left]
    change X.obj.hom ≫ (𝟙 _ ≫ μₗ F t X.obj.right) = _
    rw [Category.id_comp])⟩

/-- The original action associator, with its actual fiber structure equation. -/
def actionAssoc (s t : S) (X : IsoFiber F b) :
    actionObj F b (s ⊗ t) X ≅ actionObj F b s (actionObj F b t X) :=
  (isoFiberProperty F b).isoMk (StructuredArrow.isoMk (αₗ s t X.obj.right) (by
    change (X.obj.hom ≫ μₗ F (s ⊗ t) X.obj.right) ≫ F.map (αₗ s t X.obj.right).hom =
      (X.obj.hom ≫ μₗ F t X.obj.right) ≫ μₗ F s (t ⊙ₗ X.obj.right)
    have h := μₗ_associativity F s t X.obj.right
    change μₗ F (s ⊗ t) X.obj.right ≫ F.map (αₗ s t X.obj.right).hom =
      𝟙 _ ≫ μₗ F t X.obj.right ≫ μₗ F s (t ⊙ₗ X.obj.right) at h
    simpa only [Category.assoc, Category.id_comp] using congrArg (fun k ↦ X.obj.hom ≫ k) h))

/-- The original action unitor, with its actual fiber structure equation. -/
def actionUnit (X : IsoFiber F b) : actionObj F b (𝟙_ S) X ≅ X :=
  (isoFiberProperty F b).isoMk (StructuredArrow.isoMk (λₗ[S] X.obj.right) (by
    change (X.obj.hom ≫ μₗ F (𝟙_ S) X.obj.right) ≫ F.map (λₗ[S] X.obj.right).hom = X.obj.hom
    have h := μₗ_unitality (C := S) F X.obj.right
    change 𝟙 _ = μₗ F (𝟙_ S) X.obj.right ≫ F.map (λₗ[S] X.obj.right).hom at h
    rw [Category.assoc, ← h]
    exact Category.comp_id _))

/-- Isomorphism fibers inherit the whole coherent action; no structure map
or original arrow is discarded. -/
@[instance_reducible]
def monoidalLeftAction : MonoidalLeftAction S (IsoFiber F b) where
  actionObj := actionObj F b
  actionHomLeft := fun f X ↦ actorMap F b f X
  actionHomRight := fun s _ _ f ↦ actionMap F b s f
  actionAssocIso := actionAssoc F b
  actionUnitIso := actionUnit F b
  actionHomRight_id s X := by
    apply action_hom_ext F b
    exact MonoidalLeftAction.actionHomRight_id s X.obj.right
  id_actionHomLeft s X := by
    apply action_hom_ext F b
    exact MonoidalLeftAction.id_actionHomLeft s X.obj.right
  actionHom_comp f g h k := by
    apply action_hom_ext F b
    have e := MonoidalLeftAction.actionHom_comp f g h.hom.right k.hom.right
    simp only [MonoidalLeftAction.actionHom_def] at e
    exact e
  actionAssocIso_hom_naturality f g h := by
    apply action_hom_ext F b
    have e := MonoidalLeftAction.actionAssocIso_hom_naturality f g h.hom.right
    simp only [MonoidalLeftAction.actionHom_def] at e
    exact e
  actionUnitIso_hom_naturality f := by
    apply action_hom_ext F b
    exact MonoidalLeftAction.actionUnitIso_hom_naturality f.hom.right
  whiskerLeft_actionHomLeft s _ _ f X := by
    apply action_hom_ext F b
    exact MonoidalLeftAction.whiskerLeft_actionHomLeft s f X.obj.right
  whiskerRight_actionHomLeft s f X := by
    apply action_hom_ext F b
    exact MonoidalLeftAction.whiskerRight_actionHomLeft s f X.obj.right
  associator_actionHom s t r X := by
    apply action_hom_ext F b
    exact MonoidalLeftAction.associator_actionHom s t r X.obj.right
  leftUnitor_actionHom s X := by
    apply action_hom_ext F b
    exact MonoidalLeftAction.leftUnitor_actionHom s X.obj.right
  rightUnitor_actionHom s X := by
    apply action_hom_ext F b
    exact MonoidalLeftAction.rightUnitor_actionHom s X.obj.right

attribute [local instance] monoidalLeftAction

/-- Forgetting the specified base isomorphism preserves the original action
with identity lineators. -/
instance forgetLinear : (forget F b).LaxLeftLinear S where
  μₗ s X := 𝟙 _
  μₗ_naturality_left f X := by
    change (f ⊵ₗ X.obj.right) ≫ 𝟙 _ = 𝟙 _ ≫ (f ⊵ₗ X.obj.right)
    simp
  μₗ_naturality_right s _ _ f := by
    change (s ⊴ₗ f.hom.right) ≫ 𝟙 _ = 𝟙 _ ≫ (s ⊴ₗ f.hom.right)
    simp
  μₗ_associativity s t X := by
    change 𝟙 _ ≫ (αₗ s t X.obj.right).hom =
      (αₗ s t X.obj.right).hom ≫ s ⊴ₗ 𝟙 _ ≫ 𝟙 _
    simp
  μₗ_unitality X := by
    change (λₗ[S] X.obj.right).hom = 𝟙 _ ≫ (λₗ[S] X.obj.right).hom
    simp

end CategoryTheory.IsoFiber
