/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensions
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionAction
public import Colib.CategoryTheory.ExactCategory.Extensions.Product
public import Mathlib.CategoryTheory.IsConnected

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionConnected.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Connectedness of the fixed-quotient extension action category

Every finite-projective extension splits, providing an actual arrow from the
identity extension in the action category. Splittings are not required to be
natural or unique; only connectedness is concluded.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal extensionFiberDirectSumAction
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- Splitting an extension identifies it with its kernel acting on the identity
extension over exactly the same quotient. -/
def extensionSplitIso {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    extensionKernelIsoObject R p ⊙ₗ (exactStructure R).extensionUnit C ≅ p := by
  let k := (exactStructure R).extensionKernelData p.of
  let S := ShortComplex.mk k.ι p.of.obj.hom k.zero
  let s := splittingOfConflation R S k.conflation
  refine Core.isoMk ((exactStructure R).extensionProperty C |>.isoMk
    (Over.isoMk ((biprod.isoCoprod k.obj C).symm ≪≫ s.isoBinaryBiproduct.symm) ?_))
  change (biprod.isoCoprod k.obj C).inv ≫
    biprod.desc k.ι s.s ≫ p.of.obj.hom = coprod.desc 0 (𝟙 C)
  apply coprod.hom_ext
  · simp [biprod.isoCoprod_inv, k.zero]
  · simp only [biprod.isoCoprod_inv, coprod.inr_desc_assoc, biprod.inr_desc_assoc, coprod.inr_desc]
    exact s.s_g

/-- Every extension is reached from the identity extension by an actual action
category arrow, without making a natural choice of splitting. -/
def extensionUnitTo {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    (⟨(exactStructure R).extensionUnit C⟩ : ExtensionActionCategory R C) ⟶ ⟨p⟩ :=
  GroupCompletion.ActionLocalization.mkHom
    ⟨extensionKernelIsoObject R p, (extensionSplitIso R p).hom⟩

/-- The action category of finite-projective extensions over a fixed quotient
is genuinely connected. -/
theorem extensionActionCategory_isConnected (C : Category.{u, u} R) :
    IsConnected (ExtensionActionCategory R C) := by
  apply IsConnected.of_induct (j₀ := ⟨(exactStructure R).extensionUnit C⟩)
  intro p hp h X
  exact (h (extensionUnitTo R X.obj)).mp hp

end ModuleCat.FiniteProjective
