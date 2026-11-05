/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ZeroSkeleton

/-! The actual skeleton, universe lift, object vertex and inclusion are retained. -/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u v

variable {C : Type u} [Category.{v} C]

example : IsIso (nerveZeroSkeletonToConstant (C := C)) := inferInstance

example : (nerveZeroSkeletonIso (C := C)).hom = nerveZeroSkeletonToConstant := rfl

example (c : C) :
    (nerveZeroSkeletonRealizationIso (C := C)).hom (nerveZeroSkeletonPoint c) =
      ULift.up c :=
  nerveZeroSkeletonRealizationIso_point c

example (c : C) :
    (nerveZeroSkeletonRealizationIso (C := C)).inv (ULift.up c) =
      nerveZeroSkeletonPoint c :=
  nerveZeroSkeletonRealizationIso_inv_object c

example (c : C) : nerveZeroSkeletonHomeomorph (nerveZeroSkeletonPoint c) = c :=
  nerveZeroSkeletonHomeomorph_point c

example (c : C) :
    (nerveZeroSkeletonHomeomorph (C := C)).symm c = nerveZeroSkeletonPoint c :=
  nerveZeroSkeletonHomeomorph_symm_object c

example (c : C) :
    SSet.toTop.map ((nerve C).skeleton 1).ι (nerveZeroSkeletonPoint c) =
      classifyingSpacePoint c :=
  nerveZeroSkeletonPoint_inclusion c

open scoped Topology

example (p : SimplexCategoryᵒᵖ) (s : ((nerve C).skeleton 1).obj p) :
    (nerveZeroSkeletonToConstant (C := C)).app p s = (ULift.up (s.1.obj 0) : ULift.{v} C) :=
  rfl

example (p : SimplexCategoryᵒᵖ) (s : (nerve C).obj p)
    (hs : s ∈ ((nerve C).skeleton 1).obj p) :
    s = (Functor.const (Fin (p.unop.len + 1))).obj (s.obj 0) :=
  nerve_zeroSkeleton_constant s hs

example (c : C) (p : SimplexCategoryᵒᵖ) :
    (Functor.const (Fin (p.unop.len + 1))).obj c ∈ ((nerve C).skeleton 1).obj p :=
  nerve_constant_mem_zeroSkeleton c p

example : nerveZeroSkeletonRealizationIso (C := C) =
    SSet.toTop.mapIso nerveZeroSkeletonIso ≪≫ SSet.constantRealizationIso (ULift.{v} C) := rfl

example : |((nerve C).skeleton 1 : SSet.{max u v})| ≃ₜ TopCat.discrete.obj C :=
  nerveZeroSkeletonHomeomorph

example (x : |((nerve C).skeleton 1 : SSet.{max u v})|) :
    (nerveZeroSkeletonHomeomorph (C := C)).symm (nerveZeroSkeletonHomeomorph x) = x :=
  (nerveZeroSkeletonHomeomorph (C := C)).symm_apply_apply x

example (c : C) :
    SSet.toTop.map ((nerve C).skeleton 1).ι
      ((nerveZeroSkeletonHomeomorph (C := C)).symm c) = classifyingSpacePoint c := by
  rw [nerveZeroSkeletonHomeomorph_symm_object, nerveZeroSkeletonPoint_inclusion]
