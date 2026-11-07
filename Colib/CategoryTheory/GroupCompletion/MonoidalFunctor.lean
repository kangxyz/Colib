/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ActorChange
public import Colib.CategoryTheory.GroupCompletion.UnitEntry

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/MonoidalFunctor.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Actual strong monoidal functors on projective-style group completion -/
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
universe u v w z
namespace CategoryTheory.GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type w} [Category.{z} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- Cancel the actor tensor comparison in the original monoidal associativity square. -/
lemma monoidalFunctor_action_associativity (s t X : C) :
    Functor.LaxMonoidal.μ F (s ⊗ t) X ≫ F.map (α_ s t X).hom =
      (Functor.Monoidal.μIso F s t).inv ▷ F.obj X ≫
        (α_ (F.obj s) (F.obj t) (F.obj X)).hom ≫
        F.obj s ◁ Functor.LaxMonoidal.μ F t X ≫
        Functor.LaxMonoidal.μ F s (t ⊗ X) := by
  have h := (Functor.Monoidal.μIso F s t).inv ▷ F.obj X ≫=
    Functor.LaxMonoidal.associativity F s t X
  simpa only [Functor.Monoidal.μIso_inv, Category.assoc,
    Functor.Monoidal.whiskerRight_δ_μ_assoc, Category.id_comp] using h

/-- Cancel the actor unit comparison in the original monoidal unit square. -/
lemma monoidalFunctor_action_unitality (X : C) :
    (Functor.Monoidal.εIso F).inv ▷ F.obj X ≫ (λ_ (F.obj X)).hom =
      Functor.LaxMonoidal.μ F (𝟙_ C) X ≫ F.map (λ_ X).hom := by
  have h := (Functor.Monoidal.εIso F).inv ▷ F.obj X ≫=
    Functor.LaxMonoidal.left_unitality F X
  simpa only [Functor.Monoidal.εIso_inv, Category.assoc,
    Functor.Monoidal.whiskerRight_η_ε_assoc, Category.id_comp] using h

/-- The actual pair functor respects the restricted diagonal action. -/
@[instance_reducible]
def monoidalPairLinear :
    letI := MonoidalLeftAction.restrictAlong (D := D × D) F
    (F.prod F).LaxLeftLinear C := by
  letI := MonoidalLeftAction.restrictAlong (D := D × D) F
  exact {
    μₗ := fun s X ↦ (Functor.LaxMonoidal.μ F s X.1, Functor.LaxMonoidal.μ F s X.2)
    μₗ_naturality_left := fun f X ↦ Prod.ext
      (Functor.LaxMonoidal.μ_natural_left F f X.1)
      (Functor.LaxMonoidal.μ_natural_left F f X.2)
    μₗ_naturality_right := fun s _ _ f ↦ Prod.ext
      (Functor.LaxMonoidal.μ_natural_right F s f.1)
      (Functor.LaxMonoidal.μ_natural_right F s f.2)
    μₗ_associativity := by
      intro s t X
      apply Prod.ext
      · change Functor.LaxMonoidal.μ F (s ⊗ t) X.1 ≫ F.map (α_ s t X.1).hom =
          ((Functor.Monoidal.μIso F s t).inv ▷ F.obj X.1 ≫
            (α_ (F.obj s) (F.obj t) (F.obj X.1)).hom) ≫
            F.obj s ◁ Functor.LaxMonoidal.μ F t X.1 ≫
              Functor.LaxMonoidal.μ F s (t ⊗ X.1)
        simpa only [Category.assoc] using monoidalFunctor_action_associativity F s t X.1
      · change Functor.LaxMonoidal.μ F (s ⊗ t) X.2 ≫ F.map (α_ s t X.2).hom =
          ((Functor.Monoidal.μIso F s t).inv ▷ F.obj X.2 ≫
            (α_ (F.obj s) (F.obj t) (F.obj X.2)).hom) ≫
            F.obj s ◁ Functor.LaxMonoidal.μ F t X.2 ≫
              Functor.LaxMonoidal.μ F s (t ⊗ X.2)
        simpa only [Category.assoc] using monoidalFunctor_action_associativity F s t X.2
    μₗ_unitality := fun X ↦ Prod.ext
      (monoidalFunctor_action_unitality F X.1)
      (monoidalFunctor_action_unitality F X.2) }

/-- The original two-coordinate localization map induced by a strong monoidal functor. -/
def monoidalMap : Localization C C ⥤ Localization D D :=
  ActionLocalization.mapAlong F (F.prod F) (monoidalPairLinear F)

/-- Both original object coordinates are mapped by the actual functor. -/
lemma monoidalMap_obj (X : Localization C C) :
    (monoidalMap F).obj X = ⟨(F.obj X.obj.1, F.obj X.obj.2)⟩ := rfl

/-- The original common denominator and both tensor comparisons remain explicit. -/
lemma monoidalMap_mkHom {A B A' B' : C} (s : C)
    (f : s ⊗ A ⟶ A') (g : s ⊗ B ⟶ B') :
    (monoidalMap F).map (Localization.mkHom (X := (A, B)) (Y := (A', B')) s f g) =
      Localization.mkHom (X := (F.obj A, F.obj B)) (Y := (F.obj A', F.obj B')) (F.obj s)
        (Functor.LaxMonoidal.μ F s A ≫ F.map f)
        (Functor.LaxMonoidal.μ F s B ≫ F.map g) := rfl

/-- The original unit entry is preserved by the canonical inverse unit comparison. -/
def monoidalMapUnitIso :
    Localization.unitEntry (C := C) ⋙ monoidalMap F ≅
      F ⋙ Localization.unitEntry (C := D) :=
  NatIso.ofComponents
    (fun X ↦ (ActionLocalization.ofFunctor (C := D) (D := D × D)).mapIso
      ((Functor.Monoidal.εIso F).symm.prod (Iso.refl (F.obj X)))) (by
    intro X Y f
    change (monoidalMap F).map (ActionLocalization.ofHom
      (X := (𝟙_ C, X)) (Y := (𝟙_ C, Y)) (𝟙 _, f)) ≫
      ActionLocalization.ofHom (C := D)
        (X := (F.obj (𝟙_ C), F.obj Y)) (Y := (𝟙_ D, F.obj Y))
        ((Functor.Monoidal.εIso F).inv, 𝟙 _)  =
        ActionLocalization.ofHom (C := D)
          (X := (F.obj (𝟙_ C), F.obj X)) (Y := (𝟙_ D, F.obj X))
          ((Functor.Monoidal.εIso F).inv, 𝟙 _)  ≫
          ActionLocalization.ofHom (C := D)
            (X := (𝟙_ D, F.obj X)) (Y := (𝟙_ D, F.obj Y)) (𝟙 _, F.map f)
    rw [show (monoidalMap F).map (ActionLocalization.ofHom
      (X := (𝟙_ C, X)) (Y := (𝟙_ C, Y)) (𝟙 _, f)) =
      ActionLocalization.ofHom (C := D)
        (X := (F.obj (𝟙_ C), F.obj X)) (Y := (F.obj (𝟙_ C), F.obj Y))
        (F.map (𝟙 _), F.map f) from
        ActionLocalization.mapAlong_ofHom F (F.prod F) (monoidalPairLinear F) _]
    rw [← ActionLocalization.ofHom_comp, ← ActionLocalization.ofHom_comp]
    congr 1
    apply Prod.ext <;> simp)

end CategoryTheory.GroupCompletion
