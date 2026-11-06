/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.Contraction
public import Mathlib.Topology.Homotopy.Contractible

/-! # Contracting a classifying space through a contractible category -/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory
namespace CategoryTheory

/-- A natural transformation from a functor factoring through a contractible
category to the identity gives an actual contraction on classifying spaces. -/
theorem classifyingSpace_contractible_of_factor_natTrans
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (R : C ⥤ D) (S : D ⥤ C) (h : R ⋙ S ⟶ 𝟭 C)
    [ContractibleSpace (ClassifyingSpace D)] :
    ContractibleSpace (ClassifyingSpace C) := by
  apply (contractible_iff_id_nullhomotopic _).2
  have hn : (classifyingSpaceMap (R ⋙ S)).hom.Nullhomotopic := by
    simpa only [ContinuousMap.id_comp, classifyingSpaceMap_comp, TopCat.hom_comp] using
      ((id_nullhomotopic (ClassifyingSpace D)).comp_left (classifyingSpaceMap R).hom).comp_right
        (classifyingSpaceMap S).hom
  obtain ⟨p, hp⟩ := hn
  refine ⟨p, ?_⟩
  have ht : (ContinuousMap.id (ClassifyingSpace C)).Homotopic
      (classifyingSpaceMap (R ⋙ S)).hom := by
    simpa only [classifyingSpaceMap_id, TopCat.hom_id] using
      (show (classifyingSpaceMap (𝟭 C)).hom.Homotopic (classifyingSpaceMap (R ⋙ S)).hom from
        ⟨(classifyingSpaceNaturalTransformationHomotopy h).symm⟩)
  exact ht.trans hp

end CategoryTheory
