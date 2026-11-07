/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Universe lifting of actual comma categories

The native precomposition and postcomposition equivalences and strict lifting functors
preserve the original comma arrows, projections and transitions. No replacement comma
category or functor structure is introduced.

Source: `Quillen/Aglib/CategoryTheory/Comma/UniverseLift.lean` and
`StructuredUniverseLift.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

universe u₁ v₁ u₂ v₂ w
namespace CategoryTheory.CostructuredArrow

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Lifting both ends of a functor retains its original comma category up to equivalence. -/
def asSmallEquivalence (F : C ⥤ D) (d : AsSmall.{w} D) :
    CostructuredArrow ((AsSmall.down : AsSmall.{w} C ⥤ C) ⋙ F ⋙
      (AsSmall.up : D ⥤ AsSmall.{w} D)) d ≌
      CostructuredArrow F (ULift.down d) := by
  let eC : C ≌ AsSmall.{w} C := AsSmall.equiv
  let eD : D ≌ AsSmall.{w} D := AsSmall.equiv
  exact (CostructuredArrow.pre eC.inverse (F ⋙ eD.functor) d).asEquivalence |>.trans
    (CostructuredArrow.post F eD.functor (ULift.down d)).asEquivalence.symm

/-- Lift an original costructured arrow, retaining its original arrow. -/
def asSmallUp (F : C ⥤ D) (d : D) :
    CostructuredArrow F d ⥤
      CostructuredArrow ((AsSmall.down : AsSmall.{w} C ⥤ C) ⋙ F ⋙
        (AsSmall.up : D ⥤ AsSmall.{w} D))
        (AsSmall.up.obj d) where
  obj x := CostructuredArrow.mk (Y := AsSmall.up.obj x.left) ⟨x.hom⟩
  map f := CostructuredArrow.homMk ⟨f.left⟩ (by
    apply ULift.ext
    exact CostructuredArrow.w f)

/-- Lower a lifted costructured arrow without changing its arrow. -/
def asSmallDown (F : C ⥤ D) (d : D) :
    CostructuredArrow ((AsSmall.down : AsSmall.{w} C ⥤ C) ⋙ F ⋙
      (AsSmall.up : D ⥤ AsSmall.{w} D)) (AsSmall.up.obj d) ⥤
      CostructuredArrow F d where
  obj x := CostructuredArrow.mk (Y := ULift.down x.left) x.hom.down
  map f := CostructuredArrow.homMk f.left.down (by
    exact congrArg ULift.down (CostructuredArrow.w f))

@[simp] theorem asSmallUp_down (F : C ⥤ D) (d : D) :
    asSmallUp.{u₁, v₁, u₂, v₂, w} F d ⋙
      asSmallDown F d = 𝟭 _ := rfl

@[simp] theorem asSmallDown_up (F : C ⥤ D) (d : D) :
    asSmallDown.{u₁, v₁, u₂, v₂, w} F d ⋙
      asSmallUp F d = 𝟭 _ := rfl

/-- The categorical lift is strictly compatible with the original comma projection. -/
theorem asSmallUp_proj (F : C ⥤ D) (d : D) :
    asSmallUp.{u₁, v₁, u₂, v₂, w} F d ⋙
        CostructuredArrow.proj (AsSmall.down ⋙ F ⋙ AsSmall.up) (AsSmall.up.obj d) =
      CostructuredArrow.proj F d ⋙ AsSmall.up := rfl

/-- Lifting commutes strictly with each original comma transition. -/
theorem asSmallUp_map (F : C ⥤ D) {d e : D} (f : d ⟶ e) :
    asSmallUp.{u₁, v₁, u₂, v₂, w} F d ⋙
        CostructuredArrow.map (AsSmall.up.map f) =
      CostructuredArrow.map f ⋙ asSmallUp F e := rfl

end CategoryTheory.CostructuredArrow

namespace CategoryTheory.StructuredArrow

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Lift a structured arrow without changing its original component arrow. -/
def asSmallUp (F : C ⥤ D) (d : D) :
    StructuredArrow d F ⥤
      StructuredArrow (AsSmall.up.obj d) ((AsSmall.down : AsSmall.{w} C ⥤ C) ⋙ F ⋙
        (AsSmall.up : D ⥤ AsSmall.{w} D)) where
  obj x := StructuredArrow.mk (Y := AsSmall.up.obj x.right) ⟨x.hom⟩
  map f := StructuredArrow.homMk ⟨f.right⟩ (by
    apply ULift.ext
    exact StructuredArrow.w f)

/-- Lower a lifted structured arrow without changing its original component arrow. -/
def asSmallDown (F : C ⥤ D) (d : D) :
    StructuredArrow (AsSmall.up.obj d) ((AsSmall.down : AsSmall.{w} C ⥤ C) ⋙ F ⋙
      (AsSmall.up : D ⥤ AsSmall.{w} D)) ⥤
      StructuredArrow d F where
  obj x := StructuredArrow.mk (Y := ULift.down x.right) x.hom.down
  map f := StructuredArrow.homMk f.right.down (by
    exact congrArg ULift.down (StructuredArrow.w f))

@[simp] theorem asSmallUp_down (F : C ⥤ D) (d : D) :
    asSmallUp.{u₁, v₁, u₂, v₂, w} F d ⋙
      asSmallDown F d = 𝟭 _ := rfl

@[simp] theorem asSmallDown_up (F : C ⥤ D) (d : D) :
    asSmallDown.{u₁, v₁, u₂, v₂, w} F d ⋙
      asSmallUp F d = 𝟭 _ := rfl

/-- Lifting preserves the original structured projection strictly. -/
theorem asSmallUp_proj (F : C ⥤ D) (d : D) :
    asSmallUp.{u₁, v₁, u₂, v₂, w} F d ⋙
        StructuredArrow.proj (AsSmall.up.obj d) (AsSmall.down ⋙ F ⋙ AsSmall.up) =
      StructuredArrow.proj d F ⋙ AsSmall.up := rfl

/-- Lifting preserves every original structured transition strictly. -/
theorem asSmallUp_map (F : C ⥤ D) {d e : D} (f : d ⟶ e) :
    asSmallUp.{u₁, v₁, u₂, v₂, w} F e ⋙
        StructuredArrow.map (AsSmall.up.map f) =
      StructuredArrow.map f ⋙ asSmallUp F d := rfl

end CategoryTheory.StructuredArrow
