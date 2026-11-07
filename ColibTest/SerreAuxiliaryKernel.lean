/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryBaseChangeEquivalence

open CategoryTheory CategoryTheory.ExactCategory
open CategoryTheory.ExactCategory.SerreLocalization

noncomputable section
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass] (N : C)

example : AuxiliaryKernel P N ⥤ (abelianExactStructure P.FullSubcategory).QCategory :=
  auxiliaryKernelFunctor P N

example : ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
    (ClassifyingSpace (abelianExactStructure P.FullSubcategory).QCategory) :=
  auxiliaryKernelClassifyingHomotopyEquiv P N

example : (auxiliaryKernelClassifyingHomotopyEquiv P N).toFun =
    (classifyingSpaceMap (auxiliaryKernelFunctor P N)).hom :=
  auxiliaryKernelClassifyingHomotopyEquiv_toFun P N

example {M : C} (i : M ⟶ N) :
    (auxiliaryBaseChangeClassifyingHomotopyEquiv P i).toFun =
      (classifyingSpaceMap (auxiliaryBaseChange P i)).hom :=
  auxiliaryBaseChangeClassifyingHomotopyEquiv_toFun P i
