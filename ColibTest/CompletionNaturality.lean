/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.ClassifyingSpace.CompletionNaturality

/-!
# Actual groupoid-completion functors and naturality

Object and morphism universes stay independent. The natural isomorphisms compare
specified functors only; no fundamental-group retraction or equivalence is asserted.
-/

open CategoryTheory Opposite SSet
open scoped Simplicial Topology unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable (C : Type u) [Category.{v} C]

example : classifyingGroupoidCompletionFunctor C =
    Localization.Construction.lift (classifyingFundamentalGroupoidFunctor C)
      (fun _ _ _ _ => inferInstance) := rfl

example : (⊤ : MorphismProperty C).Q ⋙ classifyingGroupoidCompletionFunctor C =
    classifyingFundamentalGroupoidFunctor C := toClassifyingGroupoidCompletionFunctor C

example (c : C) :
    (classifyingGroupoidCompletionFunctor C).obj ((⊤ : MorphismProperty C).Q.obj c) =
      FundamentalGroupoid.mk (classifyingSpacePoint c) := rfl

example {c d : C} (f : c ⟶ d) :
    (classifyingGroupoidCompletionFunctor C).map ((⊤ : MorphismProperty C).Q.map f) =
      ⟦classifyingSpacePath f⟧ := by
  change ((⊤ : MorphismProperty C).Q ⋙ classifyingGroupoidCompletionFunctor C).map f = _
  simpa [classifyingFundamentalGroupoidFunctor] using Functor.congr_hom (toClassifyingGroupoidCompletionFunctor C) f

example (n : SimplexCategoryᵒᵖ) (F : (nerve C).obj n) :
    (groupoidCompletionNerveMap C).app n F = F ⋙ (⊤ : MorphismProperty C).Q := rfl

example : classifyingSpaceCompletionMap C = SSet.toTop.map (groupoidCompletionNerveMap C) :=
  rfl

example (c : C) : classifyingSpaceCompletionMap C (classifyingSpacePoint c) =
    classifyingSpacePoint ((⊤ : MorphismProperty C).Q.obj c) :=
  classifyingSpaceCompletionMap_point C c

example {c d : C} (f : c ⟶ d) :
    ((classifyingSpacePath f).map (classifyingSpaceCompletionMap C).hom.continuous).cast
      (classifyingSpaceCompletionMap_point C c).symm
      (classifyingSpaceCompletionMap_point C d).symm =
      classifyingSpacePath ((⊤ : MorphismProperty C).Q.map f) :=
  classifyingSpaceCompletionMap_path C f

example : classifyingFundamentalGroupoidFunctor C ⋙
      FundamentalGroupoid.map (classifyingSpaceCompletionMap C).hom ≅
    (⊤ : MorphismProperty C).Q ⋙
      classifyingFundamentalGroupoidFunctor (⊤ : MorphismProperty C).Localization :=
  classifyingFundamentalGroupoidCompletionNaturality C

example (c : C) :
    (classifyingFundamentalGroupoidCompletionNaturality C).hom.app c =
      eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceCompletionMap_point C c)) := rfl

example : classifyingGroupoidCompletionFunctor C ⋙
      FundamentalGroupoid.map (classifyingSpaceCompletionMap C).hom ≅
    classifyingFundamentalGroupoidFunctor (⊤ : MorphismProperty C).Localization :=
  classifyingGroupoidCompletionNaturality C
