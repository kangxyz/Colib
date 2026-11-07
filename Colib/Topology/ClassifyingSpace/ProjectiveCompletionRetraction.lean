/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableProjectiveCompletion
public import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeInterchange
public import Colib.CategoryTheory.GroupCompletion.FirstCoordinateAssociativity
public import Colib.CategoryTheory.GroupCompletion.InverseCoconeUnit

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionRetraction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; original functors and arrows retained.

# The actual inverse cocone on the completed projective telescope

The successor maps are obtained from the genuine completed diagonal-translation
transformation and the original associator. No objectwise choice of inverse
homotopies is used in this categorical cocone.
-/

@[expose] public section

open CategoryTheory.GroupCompletion

noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u
namespace ModuleCat.FiniteProjective.StableFreeRight
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
variable (R : Type u) [Ring R]

/-- The n-th inverse completed translation, with its original right first-coordinate action. -/
def completedInverseFiber (n : ℕ) : StableCompletion.Completion R ⥤
    StableCompletion.Completion R :=
  Localization.firstCoordinateTranslation (rankOnePower Rᵐᵒᵖ n)

/-- The original diagonal coevaluation, displayed with its actual quotient representative. -/
def completedDiagonalStep : 𝟭 (StableCompletion.Completion R) ⟶
    Localization.secondTranslation (freeIso Rᵐᵒᵖ 1) ⋙
      Localization.firstCoordinateTranslation (freeIso Rᵐᵒᵖ 1) where
  app X := GroupCompletion.Localization.mkHom (freeIso Rᵐᵒᵖ 1)
    (β_ (freeIso Rᵐᵒᵖ 1) X.obj.1).hom (β_ (freeIso Rᵐᵒᵖ 1) X.obj.2).hom
  naturality {X Y} f := by
    change f ≫ (Localization.diagonalTranslationNatTrans (freeIso Rᵐᵒᵖ 1)).app Y =
      (Localization.diagonalTranslationNatTrans (freeIso Rᵐᵒᵖ 1)).app X ≫
        (Localization.secondTranslation (freeIso Rᵐᵒᵖ 1) ⋙
          Localization.firstTranslation (freeIso Rᵐᵒᵖ 1)).map f
    have h := eq_of_heq (CategoryTheory.Functor.hcongr_hom
      (Localization.secondTranslation_comp_firstTranslation
        (freeIso Rᵐᵒᵖ 1) (freeIso Rᵐᵒᵖ 1)) f)
    rw [h]
    exact (Localization.diagonalTranslationNatTrans _).naturality f

/-- The genuine diagonal-translation map and associator give the actual successor cocone. -/
def completedInverseStep (n : ℕ) : completedInverseFiber R n ⟶
    Localization.secondTranslation (freeIso Rᵐᵒᵖ 1) ⋙ completedInverseFiber R (n + 1) :=
  Functor.whiskerRight (completedDiagonalStep R)
      (completedInverseFiber R n) ≫
    Functor.whiskerLeft (Localization.secondTranslation (freeIso Rᵐᵒᵖ 1))
      (Localization.firstCoordinateAssociator (freeIso Rᵐᵒᵖ 1) (rankOnePower Rᵐᵒᵖ n)).inv

/-- Extend the prescribed inverse cocone over the original completed endofunctor telescope. -/
def originalCompletedRetraction :
    EndofunctorTelescope.Model (Localization.secondTranslation (freeIso Rᵐᵒᵖ 1)) ⥤
      StableCompletion.Completion R :=
  EndofunctorTelescope.functorFromSequence _ (completedInverseFiber R) (completedInverseStep R)

/-- The exact diagram equality identifies the completed telescope used by the interchange. -/
def completedRetraction : Grothendieck (projectiveCompletedTelescopeDiagram R) ⥤
    StableCompletion.Completion R :=
  Grothendieck.map (eqToHom (projectiveCompletedTelescopeDiagram_eq R)) ⋙
    originalCompletedRetraction R

/-- The inverse cocone retains the original first-coordinate translation on every stage. -/
def completedRetractionStageIso (n : ℕ) :
    Grothendieck.ι (projectiveCompletedTelescopeDiagram R) n ⋙ completedRetraction R ≅
      completedInverseFiber R n := by
  refine Functor.isoWhiskerRight
      (Grothendieck.ιCompMap (eqToHom (projectiveCompletedTelescopeDiagram_eq R)) n)
      (originalCompletedRetraction R) ≪≫ ?_
  exact eqToIso (by
    simp only [eqToHom_app, eqToHom_refl, Cat.Hom.id_toFunctor, Functor.id_comp]
    exact EndofunctorTelescope.inclusion_functorFromSequence _
      (completedInverseFiber R) (completedInverseStep R) n)

/-- At stage zero the retraction is the original completed identity up to its specified unitor. -/
def completedRetractionZeroIso :
    Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0 ⋙ completedRetraction R ≅
      𝟭 (StableCompletion.Completion R) :=
  completedRetractionStageIso R 0 ≪≫ Localization.firstCoordinateUnitor

/-- On the original unit entry, the inverse stage is identified with the
original completion fiber by its prescribed left-unitor arrow. -/
def completedInverseFiberUnitHom (n : ℕ) :
    Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := IsoCategory Rᵐᵒᵖ) ⋙
      completedInverseFiber R n ⟶ completionFiber R n :=
  Localization.unitFirstCoordinateHom (rankOnePower Rᵐᵒᵖ n)

/-- The prescribed left unitor respects the actual completion successor. -/
theorem completedInverseFiberUnit_successor (n : ℕ) (X : IsoCategory Rᵐᵒᵖ) :
    (completedInverseStep R n).app (Localization.unitEntry.obj X) ≫
      (completedInverseFiberUnitHom R (n + 1)).app (X ⊗ freeIso Rᵐᵒᵖ 1) =
    (completedInverseFiberUnitHom R n).app X ≫ (completionStep R n).app X := by
  dsimp only [completedInverseStep, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc]
  exact Localization.inverseCocone_unit_successor (freeIso Rᵐᵒᵖ 1) (rankOnePower Rᵐᵒᵖ n) X

end ModuleCat.FiniteProjective.StableFreeRight
