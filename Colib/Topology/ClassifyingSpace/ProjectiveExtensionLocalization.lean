/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionLocalization
public import Colib.CategoryTheory.GroupCompletion.ProjectionComma
public import Colib.Topology.ClassifyingSpace.ExtensionTotal
public import Colib.Topology.ClassifyingSpace.GroupCompletionContractibleUniversal

/-!
# The actual localized total extension category of finite projectives

The source for Grayson's comparison with the original Q-construction is the
simultaneous localization of the extension category by direct sums. Its
projection to the action category of the isomorphism groupoid retains the
original denominator. No plus or Q-comparison theorem is built into this type.
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] directSumMonoidal directSumSymmetric extensionDirectSumAction

/-- The original unlocalized extension category has contractible realization. -/
theorem extensionTotal_classifyingSpace_contractible :
    ContractibleSpace (ClassifyingSpace (exactStructure R).ExtensionTotal) :=
  (exactStructure R).extensionTotal_contractibleSpace

/-- The actual localized total extension realization is contractible. The
proof uses its base projection, the comma adjunction, and Quillen's Theorem A. -/
theorem localizedExtension_classifyingSpace_contractible :
    ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) := by
  let : ∀ A : IsoCategory R, (tensorRight A).Faithful := directSumRight_faithful R
  let : ContractibleSpace (ClassifyingSpace (exactStructure R).ExtensionTotal) :=
    extensionTotal_classifyingSpace_contractible R
  exact GroupCompletion.Localization.classifyingSpace_contractible_universal
    (C := IsoCategory R) (D := (exactStructure R).ExtensionTotal)

end ModuleCat.FiniteProjective
