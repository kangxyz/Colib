/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionTotal
public import Colib.Topology.ClassifyingSpace.Subdivision

/-!
# Contractibility of the actual total extension category

The zero object is initial among admissible inflations. The explicit
subdivision contraction therefore contracts the total extension realization.
This does not assert contractibility after action localization; that comparison
requires its own proof.
-/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section

universe u v

open CategoryTheory Topology SSet HomotopyGroup CategoryTheory.Limits ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure
open CategoryTheory Topology SSet HomotopyGroup

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- The original zero object, considered among admissible inflations. -/
def inflationZero : E.InflationCategory := ⟨0⟩

/-- Initiality uses the actual admissible zero map and its uniqueness. -/
def inflationZeroIsInitial : IsInitial (inflationZero E) :=
  IsInitial.ofUniqueHom (fun X => ⟨0, E.inflation_zero X.obj⟩) (by
    intro X f
    apply WideSubcategory.hom_ext
    exact (isZero_zero C).eq_of_src _ _)

/-- The specified zero-extension object at which the contraction ends. -/
def extensionTotalPoint : E.ExtensionTotal :=
  Subdivision.of (𝟙 (inflationZero E))

/-- An actual contraction to the original identity of the zero object. -/
def extensionTotalContraction :
    (ContinuousMap.id (ClassifyingSpace E.ExtensionTotal)).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint (extensionTotalPoint E))) :=
  Subdivision.initialContraction (inflationZeroIsInitial E)

/-- The unlocalized total extension category has contractible realization. -/
theorem extensionTotal_contractibleSpace : ContractibleSpace (ClassifyingSpace E.ExtensionTotal) :=
  Subdivision.contractibleSpace_of_isInitial (inflationZeroIsInitial E)

end CategoryTheory.ExactCategory.ExactStructure
