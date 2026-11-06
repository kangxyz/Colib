/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.CompletionInjectivity
public import Colib.Topology.ClassifyingSpace.CompletionSurjectivity

/-!
# Completion Injectivity

Injectivity of the unchanged original completed-loop comparison.
-/

@[expose] public section

/-!
Exact original based-comparison statements from Quillen
Topology/ClassifyingSpace/CompletionRetraction.lean (final injectivity theorem)
and CompletionSurjectivity.lean (third, bijectivity theorem), fixed revision
c561118b7795eb9780be9ed391c3251d6a4d0afd. The original maps and independent
universes are unchanged. Injectivity is proved by actual graph representatives
and compact homotopy reflection instead of importing a retraction or Theorem B.
-/
noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory
attribute [local instance] Localization.groupoid

/-- Injectivity of the unchanged original completed-loop comparison. -/
theorem classifyingGroupoidCompletionMap_injective (C : Type u) [Category.{v} C] (c : C) :
    Function.Injective (classifyingGroupoidCompletionMap C c) :=
  CategoryTheory.NerveCompletion.completionMap_injective C c

/-- The original categorical completion computes the genuine topological
fundamental group, in independent object and morphism universes. -/
theorem classifyingGroupoidCompletionMap_bijective (C : Type u) [Category.{v} C] (c : C) :
    Function.Bijective (classifyingGroupoidCompletionMap C c) :=
  ⟨classifyingGroupoidCompletionMap_injective C c,
    classifyingGroupoidCompletionMap_surjective C c⟩

end CategoryTheory

attribute [colib_tag "COL-0239",
  colib_ref "WeibelKBook" "IV, Recipe 3.1.1 and Definition 3.1.4, pages 24-25"
    "background"
    "Original nerve realization and completion comparison;
      injectivity is proved by the finite-skeleton argument"]
  CategoryTheory.NerveCompletion.completion_map_injective
  CategoryTheory.NerveCompletion.completionFaithful
  CategoryTheory.classifyingGroupoidCompletionMap_injective
  CategoryTheory.classifyingGroupoidCompletionMap_bijective
