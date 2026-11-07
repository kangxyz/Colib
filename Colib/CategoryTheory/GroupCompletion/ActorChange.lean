/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.Action.Restriction
public import Colib.CategoryTheory.GroupCompletion.Functoriality

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/ActorChange.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Changing the actor in the original action localization

The denominator is sent through the actual strong monoidal functor. Its unit
and tensor comparisons witness the original quotient identity and composition
laws. No equality of the two acting categories is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
universe u v u' v' w z u₁ v₁
namespace CategoryTheory.GroupCompletion.ActionLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {C' : Type u'} [Category.{v'} C'] [MonoidalCategory C']
  {D : Type w} [Category.{z} D] [MonoidalLeftAction C' D]
  (F : C ⥤ C') [F.Monoidal]

/-- Change only the translating object, retaining the actual represented map. -/
def changeActorRep {X Y : D} :
    letI := MonoidalLeftAction.restrictAlong (D := D) F
    HomRep (C := C) X Y → HomRep (C := C') X Y := by
  let := MonoidalLeftAction.restrictAlong (D := D) F
  exact fun f ↦ ⟨F.obj f.denom, f.map⟩

/-- An original denominator isomorphism is sent through the actual actor functor. -/
lemma changeActorRep_rel {X Y : D} :
    letI := MonoidalLeftAction.restrictAlong (D := D) F
    ∀ {f g : HomRep (C := C) X Y}, HomRep.Rel f g →
      HomRep.Rel (changeActorRep F f) (changeActorRep F g) := by
  let := MonoidalLeftAction.restrictAlong (D := D) F
  intro f g h
  obtain ⟨e, he⟩ := h
  exact ⟨F.mapIso e, he⟩

/-- The inverse unit comparison is the exact identity-denominator witness. -/
lemma changeActorRep_id (X : D) :
    letI := MonoidalLeftAction.restrictAlong (D := D) F
    HomRep.Rel (changeActorRep F (HomRep.id (C := C) X))
      (HomRep.id (C := C') X) := by
  let := MonoidalLeftAction.restrictAlong (D := D) F
  refine ⟨(Functor.Monoidal.εIso F).symm, ?_⟩
  exact (MonoidalLeftAction.restrictAlong_unitor F X).symm

/-- The inverse tensor comparison is the exact composition-denominator witness. -/
lemma changeActorRep_comp {X Y Z : D} :
    letI := MonoidalLeftAction.restrictAlong (D := D) F
    ∀ (f : HomRep (C := C) X Y) (g : HomRep (C := C) Y Z),
      HomRep.Rel (changeActorRep F (f.comp g))
        ((changeActorRep F f).comp (changeActorRep F g)) := by
  let := MonoidalLeftAction.restrictAlong (D := D) F
  intro f g
  refine ⟨(Functor.Monoidal.μIso F g.denom f.denom).symm, ?_⟩
  change (Functor.Monoidal.μIso F g.denom f.denom).inv ⊵ₗ X ≫
    ((αₗ (F.obj g.denom) (F.obj f.denom) X).hom ≫
      F.obj g.denom ⊴ₗ f.map ≫ g.map) =
    (αₗ g.denom f.denom X).hom ≫ g.denom ⊴ₗ f.map ≫ g.map
  rw [MonoidalLeftAction.restrictAlong_associator]
  exact (Category.assoc _ _ _).symm

/-- The actual quotient functor changing the acting monoidal category. -/
def changeActor :
    letI := MonoidalLeftAction.restrictAlong (D := D) F
    ActionLocalization C D ⥤ ActionLocalization C' D := by
  let := MonoidalLeftAction.restrictAlong (D := D) F
  exact {
    obj := fun X ↦ ⟨X.obj⟩
    map := Quotient.map (changeActorRep F) (fun _ _ h ↦ changeActorRep_rel F h)
    map_id := fun X ↦ Quotient.sound (changeActorRep_id F X.obj)
    map_comp := by
      rintro X Y Z ⟨f⟩ ⟨g⟩
      exact Quotient.sound (changeActorRep_comp F f g) }

/-- The functor sends exactly the original denominator and leaves its map unchanged. -/
lemma changeActor_mkHom {X Y : D} :
    letI := MonoidalLeftAction.restrictAlong (D := D) F
    ∀ f : HomRep (C := C) X Y,
      (changeActor F).map (mkHom f) = mkHom (changeActorRep F f) := by
  let := MonoidalLeftAction.restrictAlong (D := D) F
  intro f
  rfl

/-- Unit-denominator arrows remain the actual original arrows after actor change. -/
lemma changeActor_ofHom {X Y : D} (f : X ⟶ Y) :
    letI := MonoidalLeftAction.restrictAlong (D := D) F
    (changeActor F).map (ofHom (C := C) f) = ofHom (C := C') f := by
  let := MonoidalLeftAction.restrictAlong (D := D) F
  apply Quotient.sound
  refine ⟨(Functor.Monoidal.εIso F).symm, ?_⟩
  change (Functor.Monoidal.εIso F).inv ⊵ₗ X ≫ ((λₗ[C'] X).hom ≫ f) =
    (λₗ[C] X).hom ≫ f
  rw [MonoidalLeftAction.restrictAlong_unitor]
  exact (Category.assoc _ _ _).symm

variable {E : Type u₁} [Category.{v₁} E] [MonoidalLeftAction C E]

/-- An actual compatible functor descends while also changing its actor. The
linearity is mathlib's original structure for the explicitly restricted target action. -/
def mapAlong (G : E ⥤ D)
    (hG : letI := MonoidalLeftAction.restrictAlong (D := D) F; G.LaxLeftLinear C) :
    ActionLocalization C E ⥤ ActionLocalization C' D := by
  let := MonoidalLeftAction.restrictAlong (D := D) F
  let := hG
  exact mapFunctor G ⋙ changeActor F

/-- Both the new denominator and the actual original lineator are visible on representatives. -/
lemma mapAlong_mkHom (G : E ⥤ D)
    (hG : letI := MonoidalLeftAction.restrictAlong (D := D) F; G.LaxLeftLinear C)
    {X Y : E} (f : HomRep (C := C) X Y) :
    letI := MonoidalLeftAction.restrictAlong (D := D) F
    letI := hG
    (mapAlong F G hG).map (mkHom f) = mkHom (C := C')
      ⟨F.obj f.denom, Functor.LaxLeftLinear.μₗ G f.denom X ≫ G.map f.map⟩ := by
  let := MonoidalLeftAction.restrictAlong (D := D) F
  let := hG
  rfl

/-- The functor retains the actual object map. -/
lemma mapAlong_obj (G : E ⥤ D)
    (hG : letI := MonoidalLeftAction.restrictAlong (D := D) F; G.LaxLeftLinear C)
    (X : ActionLocalization C E) : (mapAlong F G hG).obj X = ⟨G.obj X.obj⟩ := rfl

/-- The original unit-entry maps commute with actual change of actor and objects. -/
lemma mapAlong_ofHom (G : E ⥤ D)
    (hG : letI := MonoidalLeftAction.restrictAlong (D := D) F; G.LaxLeftLinear C)
    {X Y : E} (f : X ⟶ Y) :
    (mapAlong F G hG).map (ofHom (C := C) f) = ofHom (C := C') (G.map f) := by
  let := MonoidalLeftAction.restrictAlong (D := D) F
  let := hG
  change (changeActor F).map ((mapFunctor G).map (ofHom f)) = _
  rw [mapFunctor_ofHom]
  exact changeActor_ofHom F (G.map f)

end CategoryTheory.GroupCompletion.ActionLocalization
