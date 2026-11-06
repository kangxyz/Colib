/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.Topology.ClassifyingSpace.CompletionInjectivity

@[expose] public section

noncomputable section
open CategoryTheory
universe u v
attribute [local instance] Localization.groupoid

example (C : Type u) [Category.{v} C]
    (X Y : (⊤ : MorphismProperty C).Localization) :
    Function.Injective ((classifyingGroupoidCompletionFunctor C).map :
      (X ⟶ Y) → ((classifyingGroupoidCompletionFunctor C).obj X ⟶
        (classifyingGroupoidCompletionFunctor C).obj Y)) :=
  CategoryTheory.NerveCompletion.completion_map_injective C X Y

example (C : Type u) [Category.{v} C] :
    (classifyingGroupoidCompletionFunctor C).Faithful :=
  CategoryTheory.NerveCompletion.completionFaithful C

example (C : Type u) [Category.{v} C] (c : C) :
    Function.Bijective (classifyingGroupoidCompletionMap C c) :=
  classifyingGroupoidCompletionMap_bijective C c

-- Original identity-arrow generators are represented by the same construction.
example (C : Type u) [Category.{v} C] (c : C) :
    CategoryTheory.NerveCompletion.nerveJointProperty C ((⊤ : MorphismProperty C).Q.map (𝟙 c)) :=
  CategoryTheory.NerveCompletion.nerveJointProperty_arrow C (𝟙 c)
