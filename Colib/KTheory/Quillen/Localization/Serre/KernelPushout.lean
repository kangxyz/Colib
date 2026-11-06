/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Uses native Q-construction and intrinsic abelian full-subcategory exact structure. -/

public import Colib.CategoryTheory.Abelian.SerreClass.KernelPushout
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryKernel
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion

/-!
# Pushing out an auxiliary epimorphism along its kernel

This constructs the actual enlarged extension used in the kernel-comma
reflection. The new kernel, quotient, epimorphism, and Serre membership are
proved from pushout and cokernel universal properties.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CategoryTheory.ExactCategory.SerreLocalization

open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Abelian
attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{u} C] [Abelian C]

variable {N : C} (X : Over N) {U : C} (i : (overKernel N).obj X ⟶ U)

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- The actual enlarged object belongs to the epimorphic auxiliary category. -/
def kernelPushoutAuxiliary [Epi X.hom] (hU : P U) : EpiAuxiliaryKernel P N :=
  ⟨QConstruction.of _ _ (Over.mk (kernelPushoutMap X i)), kernelPushoutMap_isoModSerre X i P hU,
    inferInstanceAs (Epi (kernelPushoutMap X i))⟩

end CategoryTheory.ExactCategory.SerreLocalization
