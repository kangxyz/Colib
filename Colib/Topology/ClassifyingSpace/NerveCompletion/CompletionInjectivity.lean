/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveJointData
public import Colib.CategoryTheory.Groupoid.JointRepresentatives
public import Colib.Topology.ClassifyingSpace.CompletionMap

/-!
# Completion Injectivity

Ambient equality of arbitrary parallel actual graph classes preserves the
original decoder values, by the proved compact-homotopy finite-stage argument.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open FundamentalGroupoid.OpenCover
open stdSimplex.Boundary
open FundamentalGroupoid.SequentialColimit
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover
open TopCat.SimplexAttachment
open stdSimplex.Boundary
open FundamentalGroupoid.SequentialColimit
open CategoryTheory.Groupoid.JointRepresentation
attribute [local instance] Localization.groupoid

/-- Ambient equality of arbitrary parallel actual graph classes preserves the
original decoder values, by the proved compact-homotopy finite-stage argument. -/
theorem graphDecoder_value_of_map_eq (C : Type u) [Category.{v} C]
    {x y : FundamentalGroupoid (NerveGraphData.Stage C)} (a b : x ⟶ y)
    (h : (FundamentalGroupoid.map (NerveGraphData.inclusion C)).map a =
      (FundamentalGroupoid.map (NerveGraphData.inclusion C)).map b) :
    (nerveGraphDecoder C).map a = (nerveGraphDecoder C).map b := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective b
  exact graphDecoder_value_of_homotopic C p q (Path.Homotopic.Quotient.eq.mp h)

/-- The ORIGINAL completion functor is injective on every hom-set. Both joint
representation and actual ambient-homotopy reflection have been proved, not assumed. -/
theorem completion_map_injective (C : Type u) [Category.{v} C]
    (X Y : (⊤ : MorphismProperty C).Localization) :
    Function.Injective ((classifyingGroupoidCompletionFunctor C).map :
      (X ⟶ Y) → ((classifyingGroupoidCompletionFunctor C).obj X ⟶
        (classifyingGroupoidCompletionFunctor C).obj Y)) := by
  apply map_injective_of_joint (nerveGraphDecoder C)
    (FundamentalGroupoid.map (NerveGraphData.inclusion C))
    (classifyingGroupoidCompletionFunctor C) (localizedGraphObject C)
    (localizedGraphIso C) (localizedAmbientIso C)
  · intro x y f
    change nerveJointProperty C f
    rw [nerveJointProperty_all]
    trivial
  · intro x y a b h
    exact graphDecoder_value_of_map_eq C a b h

/-- Faithfulness of the unchanged original groupoid-completion functor. -/
theorem completionFaithful (C : Type u) [Category.{v} C] :
    (classifyingGroupoidCompletionFunctor C).Faithful :=
  ⟨fun {X Y} {_f _g} h => completion_map_injective C X Y h⟩

/-- Injectivity of the ORIGINAL based completion-to-fundamental-group comparison. -/
theorem completionMap_injective (C : Type u) [Category.{v} C] (c : C) :
    Function.Injective (classifyingGroupoidCompletionMap C c) :=
  completion_map_injective C _ _

end CategoryTheory.NerveCompletion
