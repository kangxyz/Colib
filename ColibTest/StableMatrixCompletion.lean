/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.GroupCompletion.StableGeneralLinearCharacter

/-!
# Original matrix actions and finite-stage projective completion maps

The tests retain ordinary matrix multiplication on right columns, the explicit
basis reversal for left stabilization, every finite-rank transition, and the
original Grothendieck fiber functors. The coefficient ring need not commute.
-/

noncomputable section
universe u v
open CategoryTheory
open scoped Matrix
open ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric

variable (R : Type u) [Ring R]

example (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (x : Fin n → Rᵐᵒᵖ) (i : Fin n) :
    (Matrix.RightModule.moduleAutEquiv R n g).hom x i =
      MulOpposite.op ((g.val *ᵥ fun j => MulOpposite.unop (x j)) i) :=
  Matrix.RightModule.moduleAutEquiv_hom_apply R n g x i

example (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (x : Fin (n + 1) → Rᵐᵒᵖ) :
    (Matrix.RightModule.leftModuleAutEquiv R (n + 1)
      (StableGeneralLinear.step R n g)).hom x 0 = x 0 :=
  Matrix.RightModule.leftModuleAutEquiv_step_zero R n g x

example {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    ((StableFree.powerGroupDiagram R).map (homOfLE h)).hom
        (StableFree.powerEndEquiv R n g) =
      StableFree.powerEndEquiv R m (StableGeneralLinear.transition R n m h g) := by
  have hn := (StableFree.matrixToPowerDiagram R).naturality (homOfLE h)
  exact (congrArg (fun f => f.hom g) hn).symm

example (n : ℕ) :
    (StableFree.matrixPowerDiagramIso R).hom.app n ≫
        (StableFree.matrixPowerDiagramIso R).inv.app n =
      𝟙 ((StableFree.matrixGroupDiagram R).obj n) :=
  NatTrans.congr_app (StableFree.matrixPowerDiagramIso R).hom_inv_id n

example {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableCompletion.stageAction R n g ≫ (StableCompletion.stageSequence R).map (homOfLE h) =
      (StableCompletion.stageSequence R).map (homOfLE h) ≫
        StableCompletion.stageAction R m (StableGeneralLinear.transition R n m h g) :=
  StableCompletion.stageAction_transition R h g

example (n : ℕ) :
    CategoryTheory.Grothendieck.ι (StableGeneralLinear.categoryDiagram R)
        (StableGeneralLinear.rankIndex n) ⋙ StableCompletion.telescopeFunctor R =
      StableCompletion.stageFunctor R n :=
  StableCompletion.inclusion_telescopeFunctor R n

example (P : Matrix.RightModule.ProjectiveMatrices R) (g : Aut P) :
    Matrix.RightModule.projectiveAutomorphismClass (Matrix.RightModule.imageFunctor.obj P)
        (Matrix.RightModule.imageFunctor.mapIso g) =
      Matrix.RightModule.automorphismClass P g :=
  Matrix.RightModule.projectiveAutomorphismClass_image P g

example (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    coreCharacter (rankOnePower Rᵐᵒᵖ n) (StableFree.powerEndEquiv R n g) =
      StableGeneralLinear.finiteClass R n g :=
  coreCharacter_powerEndEquiv R n g

example (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (StableCompletion.stableFramedCharacter R).map
      (show CategoryTheory.GroupCompletion.Localization.diagonalFrame (rankOnePower Rᵐᵒᵖ n) ⟶
        CategoryTheory.GroupCompletion.Localization.diagonalFrame (rankOnePower Rᵐᵒᵖ n) from
          StableCompletion.stageAction R n g) = StableGeneralLinear.finiteClass R n g :=
  StableCompletion.stableFramedCharacter_stageAction R n g

example : StableCompletion.telescopeFunctor R ⋙ StableCompletion.stableCompletionCharacter R ≅
    StableGeneralLinear.GrothendieckModel.projection R ⋙
      StableCompletion.quotientCategoryFunctor R :=
  StableCompletion.telescopeCharacterIso R

section Numerator
open CategoryTheory.GroupCompletion.Localization CategoryTheory.MonoidalCategory
attribute [local instance] CategoryTheory.Localization.groupoid
variable {C : Type u} [Category.{u} C] [MonoidalCategory C] [IsGroupoid C] [BraidedCategory C]

example (a : End ((completionFunctor (C := C)).obj ⟨𝟙_ C, 𝟙_ C⟩)) :
    ∃ P : C, ∃ g : P ⟶ P, a = numeratorLoop g :=
  exists_numeratorLoop a

end Numerator

example {S : Type v} [Ring S] (f : R →+* S) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (rightBaseChange f).map (Matrix.RightModule.freeAutEquiv R n g).hom ≫
        (Matrix.RightModule.freeBaseChangeIso f n).hom =
      (Matrix.RightModule.freeBaseChangeIso f n).hom ≫
        (Matrix.RightModule.freeAutEquiv S n (StableGeneralLinear.finiteMap f n g)).hom :=
  Matrix.RightModule.freeBaseChangeIso_matrix_action f n g
