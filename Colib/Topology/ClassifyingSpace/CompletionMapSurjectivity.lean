/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.CompletionFunctorNaturality
public import Colib.Topology.ClassifyingSpace.CompletionInjectivity
public import Colib.Topology.Homotopy.HomotopyGroup.FundamentalGroup

/-!
# Surjectivity on fundamental groups from actual categorical localization

Surjectivity of the endomorphism map on genuine groupoid localizations transfers
to the induced fundamental-group map of the original nerve realizations. The
map uses the actual cross-universe realization and its original vertex formula;
no homological or topological presentation hypothesis is required.
-/
@[expose] public section

noncomputable section
universe u₁ v₁ u₂ v₂
open CategoryTheory Topology SSet HomotopyGroup
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory
attribute [local instance] Localization.groupoid


variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A surjective endomorphism map between actual categorical completions gives a
surjective map of the actual fundamental groups at the original object vertices. -/
theorem classifyingSpaceMapUniversal_fundamentalGroup_surjective
    (F : C ⥤ D) (c : C)
    (h : Function.Surjective ((groupoidCompletionFunctorMap F).mapEnd
      ((⊤ : MorphismProperty C).Q.obj c))) :
    Function.Surjective (FundamentalGroup.mapOfEq (classifyingSpaceMapUniversal F)
      (classifyingSpaceMapUniversal_point F c)) := by
  intro a
  obtain ⟨b, rfl⟩ := classifyingGroupoidCompletionMap_surjective D (F.obj c) a
  obtain ⟨a, rfl⟩ := h b
  exact ⟨classifyingGroupoidCompletionMap C c a,
    classifyingGroupoidCompletionMap_naturality F c a⟩

/-- Surjectivity for the original based continuous map is equivalent to
surjectivity on endomorphisms in the actual groupoid localizations. -/
theorem classifyingSpaceMapUniversal_fundamentalGroup_surjective_iff
    (F : C ⥤ D) (c : C) :
    Function.Surjective (FundamentalGroup.mapOfEq (classifyingSpaceMapUniversal F)
      (classifyingSpaceMapUniversal_point F c)) ↔
    Function.Surjective ((groupoidCompletionFunctorMap F).mapEnd
      ((⊤ : MorphismProperty C).Q.obj c)) := by
  refine ⟨?_, classifyingSpaceMapUniversal_fundamentalGroup_surjective F c⟩
  intro h b
  obtain ⟨a, ha⟩ := h (classifyingGroupoidCompletionMap D (F.obj c) b)
  obtain ⟨a, rfl⟩ := classifyingGroupoidCompletionMap_surjective C c a
  exact ⟨a, (classifyingGroupoidCompletionMap_bijective D (F.obj c)).injective
    ((classifyingGroupoidCompletionMap_naturality F c a).symm.trans ha)⟩

/-- A surjective localization endomorphism map gives surjectivity of the genuine
`π₁` homomorphism of the original cross-universe classifying-space map. -/
theorem classifyingSpaceMapUniversal_piOne_surjective
    (F : C ⥤ D) (c : C)
    (h : Function.Surjective ((groupoidCompletionFunctorMap F).mapEnd
      ((⊤ : MorphismProperty C).Q.obj c))) :
    Function.Surjective (piMap 0 (classifyingSpaceMapUniversal F)
      (classifyingSpaceMapUniversal_point F c)) := by
  intro b
  obtain ⟨a, ha⟩ := classifyingSpaceMapUniversal_fundamentalGroup_surjective F c h
    (HomotopyGroup.pi1MulEquivFundamentalGroup b)
  obtain ⟨a, rfl⟩ := HomotopyGroup.pi1MulEquivFundamentalGroup.surjective a
  refine ⟨a, HomotopyGroup.pi1MulEquivFundamentalGroup.injective ?_⟩
  exact (HomotopyGroup.pi1MulEquivFundamentalGroup_naturality _ _ a).trans ha

/-- The genuine first homotopy-group surjectivity condition is exactly the
endomorphism surjectivity condition on the categorical localizations. -/
theorem classifyingSpaceMapUniversal_piOne_surjective_iff
    (F : C ⥤ D) (c : C) :
    Function.Surjective (piMap 0 (classifyingSpaceMapUniversal F)
      (classifyingSpaceMapUniversal_point F c)) ↔
    Function.Surjective ((groupoidCompletionFunctorMap F).mapEnd
      ((⊤ : MorphismProperty C).Q.obj c)) := by
  refine ⟨?_, classifyingSpaceMapUniversal_piOne_surjective F c⟩
  intro h
  apply (classifyingSpaceMapUniversal_fundamentalGroup_surjective_iff F c).mp
  intro b
  obtain ⟨b, rfl⟩ := HomotopyGroup.pi1MulEquivFundamentalGroup.surjective b
  obtain ⟨a, rfl⟩ := h b
  exact ⟨HomotopyGroup.pi1MulEquivFundamentalGroup a,
    (HomotopyGroup.pi1MulEquivFundamentalGroup_naturality _ _ a).symm⟩

/-- In common universes the result is about the existing classifying-space map. -/
theorem classifyingSpaceMap_piOne_surjective
    {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
    (F : C ⥤ D) (c : C)
    (h : Function.Surjective ((groupoidCompletionFunctorMap F).mapEnd
      ((⊤ : MorphismProperty C).Q.obj c))) :
    Function.Surjective (piMap 0 (classifyingSpaceMap F).hom
      (classifyingSpaceMap_point F c)) := by
  simpa only [classifyingSpaceMapUniversal_eq] using
    classifyingSpaceMapUniversal_piOne_surjective F c h

end CategoryTheory
