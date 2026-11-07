/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckGroup.Functor
public import Colib.CategoryTheory.Waldhausen.Approximation.WeakImage

/-! # The actual algebraic image quotient grading

The quotient uses the image of the original exact functor on the universal
algebraic groups. Its zero equation is precisely class membership in that
image. An actual one-arrow weak-image witness proves this equation. The
converse requires further density/classification input and is not inferred.

Implementation provenance: `Quillen/Waldhausen/GrothendieckGroup/Image.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace CategoryTheory.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : Structure C) {V : Structure D} (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Given genuine factorization, every algebraic image class comes from one actual image object. -/
theorem mem_range_iff_image_object (T : FunctorialFactorization W) (g : Group V) :
    g ∈ (map W F hF).range ↔ ∃ A : C, objectClass V (F.obj A) = g := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨A, rfl⟩ := objectClass_surjective W T x
    exact ⟨A, (map_objectClass W F hF A).symm⟩
  · rintro ⟨A, rfl⟩
    exact ⟨objectClass W A, map_objectClass W F hF A⟩

/-- The algebraic quotient by the exact original image, without a surjectivity claim. -/
abbrev ImageQuotient := Group V ⧸ (map W F hF).range

/-- The original target has a canonical additive grading in that actual quotient. -/
def imageQuotientGrading : Cofinality.Grading V (ImageQuotient W F hF) where
  value A := QuotientAddGroup.mk' (map W F hF).range (objectClass V A)
  zero := by rw [objectClass_zero, map_zero]
  weak f hf := congrArg (QuotientAddGroup.mk' (map W F hF).range) (objectClass_weak V f hf)
  pushout hi hQ := by rw [objectClass_pushout V hi hQ, map_sub, map_add]

/-- The actual zero equation detects exactly membership in the actual algebraic image. -/
theorem imageQuotientGrading_zero_iff (A : D) :
    (imageQuotientGrading W F hF).value A = 0 ↔ objectClass V A ∈ (map W F hF).range :=
  QuotientAddGroup.eq_zero_iff _

/-- An actual original weak-image witness implies vanishing of its quotient grade. -/
theorem imageQuotientGrading_zero_of_weakImage {A : D}
    (hA : ApproximationImage.objects V F A) : (imageQuotientGrading W F hF).value A = 0 := by
  obtain ⟨X, p, hp⟩ := hA
  apply (imageQuotientGrading_zero_iff W F hF A).mpr
  exact ⟨objectClass W X, (map_objectClass W F hF X).trans (objectClass_weak V p hp)⟩

/-- Every quotient-grade element has an original target representative under genuine
factorization. -/
theorem imageQuotientGrading_surjective (T : FunctorialFactorization V) :
    Function.Surjective (imageQuotientGrading W F hF).value := by
  intro g
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (map W F hF).range g
  obtain ⟨A, rfl⟩ := objectClass_surjective V T x
  exact ⟨A, rfl⟩

end CategoryTheory.Waldhausen.AlgebraicGrothendieck
