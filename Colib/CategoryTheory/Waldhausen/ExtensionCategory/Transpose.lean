/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Structure

/-! # Actual transposition of genuine Reedy cofibration squares

The relative pushout is flipped, and its original comparison map is retained.
This gives the categorical involution; exactness on morphism cubes is proved
separately using the actual three-direction relative pushout interchange.


Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/Transpose.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The transposed genuine cofibration square, using the same relative comparison. -/
def transposeSquare {X Y : Obj W} (f : X ⟶ Y) (hf : cof W f) : Obj (waldhausenStructure W) := by
  let L : Obj W := ⟨Arrow.mk f.hom.left, hf.1⟩
  let R : Obj W := ⟨Arrow.mk f.hom.right, cof_middle W hf⟩
  let g : L ⟶ R := (objects W).homMk (Arrow.homMk X.obj.hom Y.obj.hom f.hom.w.symm)
  refine ⟨Arrow.mk g, ?_⟩
  exact cof_of_relative W g X.property
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk f)).flip
    (relativeMap W f)
    (Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f))
    (Additivity.sourceι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)) hf.2

/-- Transposition retains the four original component maps of every cube. -/
def transpose : Obj (waldhausenStructure W) ⥤ Obj (waldhausenStructure W) where
  obj X := transposeSquare W X.obj.hom X.property
  map a := (objects (waldhausenStructure W)).homMk (Arrow.homMk
    ((objects W).homMk (Arrow.homMk a.hom.left.hom.left a.hom.right.hom.left
      (congrArg (fun f ↦ f.hom.left) a.hom.w)))
    ((objects W).homMk (Arrow.homMk a.hom.left.hom.right a.hom.right.hom.right
      (congrArg (fun f ↦ f.hom.right) a.hom.w)))
    (by
      apply ObjectProperty.hom_ext
      apply Arrow.hom_ext
      · exact a.hom.left.hom.w
      · exact a.hom.right.hom.w))
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> apply ObjectProperty.hom_ext <;> apply Arrow.hom_ext <;> rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> apply ObjectProperty.hom_ext <;> apply Arrow.hom_ext <;> rfl

@[simp] theorem transpose_obj_left_hom (X : Obj (waldhausenStructure W)) :
    ((transpose W).obj X).obj.left.obj.hom = X.obj.hom.hom.left := rfl
@[simp] theorem transpose_obj_right_hom (X : Obj (waldhausenStructure W)) :
    ((transpose W).obj X).obj.right.obj.hom = X.obj.hom.hom.right := rfl
@[simp] theorem transpose_obj_hom_left (X : Obj (waldhausenStructure W)) :
    ((transpose W).obj X).obj.hom.hom.left = X.obj.left.obj.hom := rfl
@[simp] theorem transpose_obj_hom_right (X : Obj (waldhausenStructure W)) :
    ((transpose W).obj X).obj.hom.hom.right = X.obj.right.obj.hom := rfl

@[simp] theorem transpose_transpose : transpose W ⋙ transpose W = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The equivalence retains literal original component squares in both directions. -/
def transposeEquivalence : Obj (waldhausenStructure W) ≌ Obj (waldhausenStructure W) :=
  CategoryTheory.Equivalence.mk (transpose W) (transpose W)
    (eqToIso (transpose_transpose W).symm) (eqToIso (transpose_transpose W))

@[simp] theorem transpose_zero :
    (transpose W).obj (zero (waldhausenStructure W)) = zero (waldhausenStructure W) := rfl

/-- Transposition preserves the actual four component weak equivalences. -/
theorem transpose_weq {X Y : Obj (waldhausenStructure W)} {f : X ⟶ Y}
    (hf : weq (waldhausenStructure W) f) : weq (waldhausenStructure W) ((transpose W).map f) :=
  ⟨⟨hf.1.1, hf.2.1⟩, ⟨hf.1.2, hf.2.2⟩⟩

end CategoryTheory.Waldhausen.ExtensionCategory
