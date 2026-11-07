/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Uses native Q-construction and intrinsic abelian full-subcategory exact structure. -/

public import Colib.KTheory.Quillen.Localization.Serre.ImageKernelComma
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion

/-! # Arbitrary-base pullback equivalences for Serre auxiliary categories -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.SerreLocalization

open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Abelian
attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- Pullback along any ambient map is a homotopy equivalence of auxiliary
categories, since it naturally preserves the actual kernel functor. -/
def auxiliaryBaseChangeClassifyingHomotopyEquiv {M N : C} (i : M ⟶ N) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
      (ClassifyingSpace (AuxiliaryKernel P M)) := by
  let eN := auxiliaryKernelClassifyingHomotopyEquiv P N
  let eM := auxiliaryKernelClassifyingHomotopyEquiv P M
  let f := (classifyingSpaceMap (auxiliaryBaseChange P i)).hom
  have h : (eM.toFun.comp f).Homotopic eN.toFun := by
    simpa only [eM, eN, f, auxiliaryKernelClassifyingHomotopyEquiv_toFun,
      classifyingSpaceMap_comp, TopCat.hom_comp] using
      (show (classifyingSpaceMap (auxiliaryBaseChange P i ⋙ auxiliaryKernelFunctor P
        M)).hom.Homotopic
        (classifyingSpaceMap (auxiliaryKernelFunctor P N)).hom from
        ⟨classifyingSpaceNaturalTransformationHomotopy (auxiliaryBaseChangeKernelIso P i).hom⟩)
  apply TheoremA.homotopyEquivWithMap (eN.trans eM.symm) f
  exact (show f.Homotopic (eM.invFun.comp (eM.toFun.comp f)) from by
    simpa using ContinuousMap.Homotopic.comp eM.left_inv.symm (.refl f)).trans
      (ContinuousMap.Homotopic.comp (.refl eM.invFun) h)

@[simp]
theorem auxiliaryBaseChangeClassifyingHomotopyEquiv_toFun {M N : C} (i : M ⟶ N) :
    (auxiliaryBaseChangeClassifyingHomotopyEquiv P i).toFun =
      (classifyingSpaceMap (auxiliaryBaseChange P i)).hom := rfl

end CategoryTheory.ExactCategory.SerreLocalization
