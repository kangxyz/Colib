/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Action.End

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Monoidal/Action/Restriction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Restriction of an actual action along a strong monoidal functor
-/
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
attribute [local instance] endofunctorMonoidalCategory
universe u v u' v' w z
namespace CategoryTheory.MonoidalCategory.MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {C' : Type u'} [Category.{v'} C'] [MonoidalCategory C']
  {D : Type w} [Category.{z} D] [MonoidalLeftAction C' D]
  (F : C ⥤ C') [F.Monoidal]

/-- Restrict the original target action using the actual strong monoidal functor.
This is named rather than globally installed, so the actor is never silently changed. -/
@[instance_reducible]
def restrictAlong : MonoidalLeftAction C D :=
  actionOfMonoidalFunctorToEndofunctorMop (F ⋙ curriedActionMop C' D)

/-- Restricted objects retain the original functor's object map. -/
lemma restrictAlong_obj (s : C) (X : D) :
    letI := restrictAlong (D := D) F
    s ⊙ₗ X = F.obj s ⊙ₗ X := rfl

/-- Restricted actor arrows retain the original functor's map. -/
lemma restrictAlong_actorMap {s t : C} (f : s ⟶ t) (X : D) :
    letI := restrictAlong (D := D) F
    f ⊵ₗ X = F.map f ⊵ₗ X := rfl

/-- Restricted object arrows are acted on by the original image actor. -/
lemma restrictAlong_map (s : C) {X Y : D} (f : X ⟶ Y) :
    letI := restrictAlong (D := D) F
    s ⊴ₗ f = F.obj s ⊴ₗ f := rfl

/-- The restricted unitor contains exactly the original inverse unit comparison. -/
lemma restrictAlong_unitor (X : D) :
    letI := restrictAlong (D := D) F
    (λₗ[C] X).hom = (Functor.Monoidal.εIso F).inv ⊵ₗ X ≫ (λₗ[C'] X).hom := rfl

/-- The restricted associator contains exactly the original inverse tensor comparison. -/
lemma restrictAlong_associator (s t : C) (X : D) :
    letI := restrictAlong (D := D) F
    (αₗ s t X).hom = (Functor.Monoidal.μIso F s t).inv ⊵ₗ X ≫
      (αₗ (F.obj s) (F.obj t) X).hom := rfl

end CategoryTheory.MonoidalCategory.MonoidalLeftAction
