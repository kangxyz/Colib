/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.ClassifyingSpace.ArrowPaths
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Realized-arrow functor on categorical groupoid completion

Extracted from the first two declarations of
`Quillen/Topology/ClassifyingSpace/GroupoidCompletion.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual Mathlib localization, Construction.lift and exact Construction.fac
identity are retained, with independent object and morphism universes.
Only namespace and import ownership change. No fullness, faithfulness,
retraction or fundamental-group equivalence is asserted.
-/
@[expose] public section


noncomputable section
universe u v
open CategoryTheory
namespace CategoryTheory

/-- Extend the realized-arrow functor to the actual groupoid localization. -/
def classifyingGroupoidCompletionFunctor (C : Type u) [Category.{v} C] :
    (⊤ : MorphismProperty C).Localization ⥤ FundamentalGroupoid (ClassifyingSpace C) :=
  Localization.Construction.lift (classifyingFundamentalGroupoidFunctor C)
    (fun _ _ _ _ => inferInstance)

/-- The extension preserves the original object vertices and arrow paths exactly. -/
@[simp] theorem toClassifyingGroupoidCompletionFunctor (C : Type u) [Category.{v} C] :
    (⊤ : MorphismProperty C).Q ⋙ classifyingGroupoidCompletionFunctor C =
      classifyingFundamentalGroupoidFunctor C :=
  Localization.Construction.fac _ _

end CategoryTheory

attribute [colib_tag "COL-0092",
  colib_ref "WeibelKBook" "IV, Lemma 3.4, pages 27-28"
    "background"
    "Arrow and composition relations only, not a fundamental-group comparison"]
  CategoryTheory.classifyingGroupoidCompletionFunctor
  CategoryTheory.toClassifyingGroupoidCompletionFunctor
