/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.CompletionMap
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy

/-!
# Naturality of the original groupoid-completion comparison

A functor induces a functor between the actual groupoid localizations. The
completed-arrow comparison commutes with the actual continuous map between the
original nerve realizations, using its specified vertex equality. Object and
morphism universes of both categories are independent.
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

/-- The functor between genuine groupoid localizations induced by a functor. -/
def groupoidCompletionFunctorMap (F : C ⥤ D) :
    (⊤ : MorphismProperty C).Localization ⥤ (⊤ : MorphismProperty D).Localization :=
  Localization.Construction.lift (F ⋙ (⊤ : MorphismProperty D).Q)
    (fun _ _ _ _ ↦ inferInstance)

/-- The localization square commutes on the original categories. -/
@[simp] theorem groupoidCompletionFunctorMap_fac (F : C ⥤ D) :
    (⊤ : MorphismProperty C).Q ⋙ groupoidCompletionFunctorMap F =
      F ⋙ (⊤ : MorphismProperty D).Q :=
  Localization.Construction.fac _ _

/-- On object vertices the induced localization functor is the original object map. -/
@[simp] theorem groupoidCompletionFunctorMap_obj (F : C ⥤ D) (c : C) :
    (groupoidCompletionFunctorMap F).obj ((⊤ : MorphismProperty C).Q.obj c) =
      (⊤ : MorphismProperty D).Q.obj (F.obj c) := rfl

/-- Cross-universe realization preserves original arrow paths with the prescribed endpoints. -/
theorem classifyingSpaceMapUniversal_path_cast (F : C ⥤ D) {c d : C} (f : c ⟶ d) :
    ((classifyingSpacePath f).map (classifyingSpaceMapUniversal F).continuous).cast
      (classifyingSpaceMapUniversal_point F c).symm
      (classifyingSpaceMapUniversal_point F d).symm = classifyingSpacePath (F.map f) := by
  ext t
  exact classifyingSpaceMapUniversal_path F f t

/-- The realized original-arrow functors are naturally compatible with every functor. -/
def classifyingFundamentalGroupoidUniversalNaturality (F : C ⥤ D) :
    classifyingFundamentalGroupoidFunctor C ⋙
        FundamentalGroupoid.map (classifyingSpaceMapUniversal F) ≅
      F ⋙ classifyingFundamentalGroupoidFunctor D :=
  NatIso.ofComponents (fun c ↦ eqToIso (congrArg FundamentalGroupoid.mk
    (classifyingSpaceMapUniversal_point F c))) (by
    intro c d f
    apply (cancel_epi (eqToHom (congrArg FundamentalGroupoid.mk
      (classifyingSpaceMapUniversal_point F c).symm))).1
    simp only [eqToIso, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [Category.assoc]
    change eqToHom (congrArg FundamentalGroupoid.mk
        (classifyingSpaceMapUniversal_point F c).symm) ≫
      (⟦(classifyingSpacePath f).map (classifyingSpaceMapUniversal F).continuous⟧ :
        Path.Homotopic.Quotient _ _) ≫
      eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceMapUniversal_point F d)) = _
    rw [FundamentalGroupoid.conj_eqToHom
      (classifyingSpaceMapUniversal_point F c).symm
      (classifyingSpaceMapUniversal_point F d).symm]
    exact congrArg Path.Homotopic.Quotient.mk (classifyingSpaceMapUniversal_path_cast F f))

/-- Extend the original-arrow naturality transformation over the genuine localization. -/
def classifyingGroupoidCompletionUniversalNaturality (F : C ⥤ D) :
    classifyingGroupoidCompletionFunctor C ⋙
        FundamentalGroupoid.map (classifyingSpaceMapUniversal F) ⟶
      groupoidCompletionFunctorMap F ⋙ classifyingGroupoidCompletionFunctor D := by
  apply Localization.Construction.natTransExtension
  exact (eqToHom (by rw [← Functor.assoc, toClassifyingGroupoidCompletionFunctor])) ≫
    (classifyingFundamentalGroupoidUniversalNaturality F).hom ≫
      eqToHom (by rw [← Functor.assoc, groupoidCompletionFunctorMap_fac, Functor.assoc,
        toClassifyingGroupoidCompletionFunctor])

/-- The extended naturality component is the actual vertex equality, with no chosen path. -/
@[simp] theorem classifyingGroupoidCompletionUniversalNaturality_app (F : C ⥤ D) (c : C) :
    (classifyingGroupoidCompletionUniversalNaturality F).app
      ((⊤ : MorphismProperty C).Q.obj c) =
        eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceMapUniversal_point F c)) := by
  simp [classifyingGroupoidCompletionUniversalNaturality,
    Localization.Construction.NatTransExtension.app_eq,
    classifyingFundamentalGroupoidUniversalNaturality]

/-- Completed-loop realization is natural for the original based continuous map. -/
theorem classifyingGroupoidCompletionMap_naturality (F : C ⥤ D) (c : C)
    (a : End ((⊤ : MorphismProperty C).Q.obj c)) :
    FundamentalGroup.mapOfEq (classifyingSpaceMapUniversal F)
      (classifyingSpaceMapUniversal_point F c) (classifyingGroupoidCompletionMap C c a) =
        classifyingGroupoidCompletionMap D (F.obj c)
          ((groupoidCompletionFunctorMap F).mapEnd _ a) := by
  have h := (classifyingGroupoidCompletionUniversalNaturality F).naturality a
  rw [classifyingGroupoidCompletionUniversalNaturality_app] at h
  change eqToHom (congrArg FundamentalGroupoid.mk
      (classifyingSpaceMapUniversal_point F c).symm) ≫
    (classifyingGroupoidCompletionFunctor C ⋙
      FundamentalGroupoid.map (classifyingSpaceMapUniversal F)).map a ≫
    eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceMapUniversal_point F c)) = _
  rw [h]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rfl

end CategoryTheory
