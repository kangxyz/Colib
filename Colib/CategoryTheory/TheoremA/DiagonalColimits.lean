/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.ReplacementDiagonal
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! Source: Quillen/CategoryTheory/TheoremA/DiagonalColimits.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-! The genuine diagonal functor preserves colimits, since each diagonal
    degree is the composite of the two evaluation functors. -/
@[expose] public section

noncomputable section
open SSet TopCat CategoryTheory Limits Opposite
universe u v w
namespace CategoryTheory.TheoremA

instance diagonalFunctor_preservesColimits [HasColimitsOfSize.{v, w} (Type u)] :
  PreservesColimitsOfSize.{v, w} diagonalFunctor.{u} := by
  constructor
  intro J _
  apply preservesColimitsOfShape_of_evaluation
  intro p
  change PreservesColimitsOfShape J
    (((evaluation SimplexCategoryᵒᵖ SSet).obj p) ⋙
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj p)
  infer_instance

end CategoryTheory.TheoremA
