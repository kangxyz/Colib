/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Subdivision.Initial
public import Colib.Topology.ClassifyingSpace.Contraction

/-!
# An explicit contraction of subdivision

An initial object in the original category supplies the two natural
transformations needed to contract the actual subdivision realization.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Topology SSet HomotopyGroup CategoryTheory.Limits

namespace CategoryTheory.Subdivision

variable {C : Type u} [Category.{v} C] {z : C} (hz : IsInitial z)

/-- Realize the actual identity-to-raise-to-constant zigzag. -/
def initialContraction :
    (ContinuousMap.id (ClassifyingSpace (Subdivision C))).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint (of (𝟙 z)))) := by
  have h₁ := classifyingSpaceNaturalTransformationHomotopy (identityToInitialRaise hz)
  have h₂ := classifyingSpaceNaturalTransformationHomotopy (constantToInitialRaise hz)
  simpa only [classifyingSpaceMap_id, TopCat.hom_id, classifyingSpaceMap_const] using
    h₁.trans h₂.symm

include hz in
/-- Subdivision of a category with an initial object has contractible realization. -/
theorem contractibleSpace_of_isInitial : ContractibleSpace (ClassifyingSpace (Subdivision C)) := by
  apply (contractible_iff_id_nullhomotopic _).2
  exact ⟨classifyingSpacePoint (of (𝟙 z)), ⟨initialContraction hz⟩⟩

end CategoryTheory.Subdivision
