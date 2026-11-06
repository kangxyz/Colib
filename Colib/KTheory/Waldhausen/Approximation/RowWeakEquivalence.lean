/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.Rows
public import Colib.KTheory.Waldhausen.Approximation.WeakEquivalence
public import Colib.CategoryTheory.Waldhausen.Rows.NerveFunctoriality

/-! # Complete weakness on the original S-construction row nerves

The actual row App1/App2 and genuine joint source factorization satisfy the
proved weak-category approximation theorem in every degree. The functor
is the existing weak-row postcomposition, so the bisimplicial map is unchanged.

Implementation provenance:
`Quillen/Waldhausen/Approximation/RowWeakEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.QuotientRows


noncomputable section
open Topology TopCat SSet
open CategoryTheory Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.HasApproximationProperty
open QuotientRows
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))

omit [V.weq.HasTwoOutOfThreeProperty] in
/-- Weak postcomposition is the literal functor on the original weak row category. -/
theorem weakRowsPostcompose_eq_weakFunctor (n : SimplexCategory) :
    weakRowsPostcompose W V hF n = (postcompose_exact W V hF n).weakFunctor := rfl

include h J in
/-- Every original row map realizes to a complete weak equivalence, including components. -/
theorem weakRowsPostcompose_isWeakHomotopyEquivalence (n : SimplexCategory) :
    IsWeakHomotopyEquivalence (classifyingSpaceMap (weakRowsPostcompose W V hF n)).hom := by
  rw [weakRowsPostcompose_eq_weakFunctor]
  exact (h.row_approximation_of_joint hF J
    n).weakFunctor_classifyingSpaceMap_isWeakHomotopyEquivalence
    (postcompose_exact W V hF n) (factorizationOfJointData W J n)

include h J in
/-- The unchanged bisimplicial weak-row nerve map meets the rowwise complete weak condition. -/
theorem weakRowNerveMap_row_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence
      (SSet.toTop.map ((weakRowNerveMap W V hF).app (op ⦋n⦌))).hom :=
  weakRowsPostcompose_isWeakHomotopyEquivalence h hF J ⦋n⦌

end CategoryTheory.Waldhausen.HasApproximationProperty
