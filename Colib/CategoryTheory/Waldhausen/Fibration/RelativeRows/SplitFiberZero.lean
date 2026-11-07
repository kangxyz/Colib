/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.SplitFiber

/-! # Exact chosen-zero formulas for the original split inclusion

Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/SplitFiberZero.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C]

/-- The one-step embedding retains the original chosen zero row, including every map. -/
@[simp] theorem QuotientRows.oneEmbedding_zero (W : Structure C) :
    (QuotientRows.oneEmbedding W).obj W.zero = QuotientRows.zero W ⦋1⦌ := by
  apply ObjectProperty.FullSubcategory.ext
  refine CategoryTheory.Functor.ext (fun p ↦ ?_) ?_
  · rcases p with ⟨⟨i,j⟩, hij⟩
    fin_cases i <;> fin_cases j <;> rfl
  · intro p q f
    exact (QuotientRows.evaluation_isZero W ((QuotientRows.oneEmbedding_exact W).zero W.isZero)
      p).eq_of_src _ _

namespace Fibration.RelativeRows
variable {V : Structure C} (N : NestedWeakEquivalences V)

/-- The actual split-fiber inclusion retains the actual chosen relative zero row. -/
@[simp] theorem fiber_zero (n : SimplexCategory) : (fiber N n).obj V.zero = zero N n := by
  apply ObjectProperty.FullSubcategory.ext
  change (QuotientRows.reindex V (fiberOrdinal n)).obj
    ((QuotientRows.oneEmbedding V).obj V.zero) = QuotientRows.zero V (addInitial.obj n)
  rw [QuotientRows.oneEmbedding_zero, QuotientRows.reindex_zero]

end Fibration.RelativeRows
end CategoryTheory.Waldhausen
