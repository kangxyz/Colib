/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.ChainCategories

/-! # Literal transposition of the two original mixed nerve directions

The operation switches the two original ordinal indices. Every object,
horizontal arrow and vertical arrow is the corresponding original component;
only its proved weak/cofibration predicate is repackaged.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/Transpose.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration.RelativeRows


noncomputable section
open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
open RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Transpose an original fine-weak chain of coarse-weak chains. -/
def transposeCoarse (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains N n) k.len) :
    ComposableArrows (HorizontalChains N k) n.len where
  obj i := ⟨⟨{
    obj j := (F.obj j).obj.obj.obj i
    map f := (F.map f).hom.hom.app i
    map_id j := congrArg (fun f ↦ f.hom.hom.app i) (F.map_id j)
    map_comp f g := congrArg (fun h ↦ h.hom.hom.app i) (F.map_comp f g) },
    fun f ↦ (F.map f).property i⟩⟩
  map f := ⟨(fineChains V k).homMk {
    app j := (F.obj j).obj.obj.map f
    naturality j l g := ((F.map g).hom.hom.naturality f).symm },
    fun j ↦ (F.obj j).obj.property f⟩
  map_id i := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext j
    exact (F.obj j).obj.obj.map_id i
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext j
    exact (F.obj j).obj.obj.map_comp f g

/-- The inverse switch retains the original coarse-chain object type. -/
def untransposeCoarse (n k : SimplexCategory)
    (F : ComposableArrows (HorizontalChains N k) n.len) :
    ComposableArrows (FineWeakCoarseChains N n) k.len where
  obj j := ⟨⟨{
    obj i := (F.obj i).obj.obj.obj j
    map f := (F.map f).hom.hom.app j
    map_id i := congrArg (fun f ↦ f.hom.hom.app j) (F.map_id i)
    map_comp f g := congrArg (fun h ↦ h.hom.hom.app j) (F.map_comp f g) },
    fun f ↦ (F.map f).property j⟩⟩
  map f := ⟨(coarseWeakChains N n).homMk {
    app i := (F.obj i).obj.obj.map f
    naturality i l g := ((F.map g).hom.hom.naturality f).symm },
    fun i ↦ (F.obj i).obj.property f⟩
  map_id j := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext i
    exact (F.obj i).obj.obj.map_id j
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext i
    exact (F.obj i).obj.obj.map_comp f g

@[simp] theorem untranspose_transposeCoarse (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains N n) k.len) :
    untransposeCoarse N n k (transposeCoarse N n k F) = F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem transpose_untransposeCoarse (n k : SimplexCategory)
    (F : ComposableArrows (HorizontalChains N k) n.len) :
    transposeCoarse N n k (untransposeCoarse N n k F) = F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual simplexwise equivalence switches precisely the two original indices. -/
def transposeCoarseEquiv (n k : SimplexCategory) :
    ComposableArrows (FineWeakCoarseChains N n) k.len ≃
      ComposableArrows (HorizontalChains N k) n.len where
  toFun := transposeCoarse N n k
  invFun := untransposeCoarse N n k
  left_inv := untranspose_transposeCoarse N n k
  right_inv := transpose_untransposeCoarse N n k

@[simp] theorem transposeCoarse_obj_obj (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains N n) k.len)
    (i : Fin (n.len + 1)) (j : Fin (k.len + 1)) :
    ((transposeCoarse N n k F).obj i).obj.obj.obj j = (F.obj j).obj.obj.obj i := rfl

@[simp] theorem transposeCoarse_map_app (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains N n) k.len)
    {i l : Fin (n.len + 1)} (f : i ⟶ l) (j : Fin (k.len + 1)) :
    ((transposeCoarse N n k F).map f).hom.hom.app j = (F.obj j).obj.obj.map f := rfl

@[simp] theorem transposeCoarse_obj_map (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains N n) k.len)
    (i : Fin (n.len + 1)) {j l : Fin (k.len + 1)} (f : j ⟶ l) :
    ((transposeCoarse N n k F).obj i).obj.obj.map f = (F.map f).hom.hom.app i := rfl

/-- Transpose an original fine-weak chain of coarse-weak chains. -/
def transposeCof (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakChains N n) k.len) :
    ComposableArrows (HorizontalCofChains N k) n.len where
  obj i := ⟨⟨{
    obj j := (F.obj j).obj.obj.obj i
    map f := (F.map f).hom.hom.app i
    map_id j := congrArg (fun f ↦ f.hom.hom.app i) (F.map_id j)
    map_comp f g := congrArg (fun h ↦ h.hom.hom.app i) (F.map_comp f g) },
    fun f ↦ (F.map f).property i⟩⟩
  map f := ⟨(fineChains V k).homMk {
    app j := (F.obj j).obj.obj.map f
    naturality j l g := ((F.map g).hom.hom.naturality f).symm },
    ⟨fun j ↦ (F.obj j).obj.property.1 f, fun j ↦ (F.obj j).obj.property.2 f⟩⟩
  map_id i := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext j
    exact (F.obj j).obj.obj.map_id i
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext j
    exact (F.obj j).obj.obj.map_comp f g

/-- The inverse switch retains the original coarse-chain object type. -/
def untransposeCof (n k : SimplexCategory)
    (F : ComposableArrows (HorizontalCofChains N k) n.len) :
    ComposableArrows (FineWeakChains N n) k.len where
  obj j := ⟨⟨{
    obj i := (F.obj i).obj.obj.obj j
    map f := (F.map f).hom.hom.app j
    map_id i := congrArg (fun f ↦ f.hom.hom.app j) (F.map_id i)
    map_comp f g := congrArg (fun h ↦ h.hom.hom.app j) (F.map_comp f g) },
    ⟨fun f ↦ (F.map f).property.1 j, fun f ↦ (F.map f).property.2 j⟩⟩⟩
  map f := ⟨(cofibrationWeakChains N n).homMk {
    app i := (F.obj i).obj.obj.map f
    naturality i l g := ((F.map g).hom.hom.naturality f).symm },
    fun i ↦ (F.obj i).obj.property f⟩
  map_id j := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext i
    exact (F.obj i).obj.obj.map_id j
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext i
    exact (F.obj i).obj.obj.map_comp f g

@[simp] theorem untranspose_transposeCof (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakChains N n) k.len) :
    untransposeCof N n k (transposeCof N n k F) = F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem transpose_untransposeCof (n k : SimplexCategory)
    (F : ComposableArrows (HorizontalCofChains N k) n.len) :
    transposeCof N n k (untransposeCof N n k F) = F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual simplexwise equivalence switches precisely the two original indices. -/
def transposeCofEquiv (n k : SimplexCategory) :
    ComposableArrows (FineWeakChains N n) k.len ≃
      ComposableArrows (HorizontalCofChains N k) n.len where
  toFun := transposeCof N n k
  invFun := untransposeCof N n k
  left_inv := untranspose_transposeCof N n k
  right_inv := transpose_untransposeCof N n k

@[simp] theorem transposeCof_obj_obj (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakChains N n) k.len)
    (i : Fin (n.len + 1)) (j : Fin (k.len + 1)) :
    ((transposeCof N n k F).obj i).obj.obj.obj j = (F.obj j).obj.obj.obj i := rfl

@[simp] theorem transposeCof_map_app (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakChains N n) k.len)
    {i l : Fin (n.len + 1)} (f : i ⟶ l) (j : Fin (k.len + 1)) :
    ((transposeCof N n k F).map f).hom.hom.app j = (F.obj j).obj.obj.map f := rfl

@[simp] theorem transposeCof_obj_map (n k : SimplexCategory)
    (F : ComposableArrows (FineWeakChains N n) k.len)
    (i : Fin (n.len + 1)) {j l : Fin (k.len + 1)} (f : j ⟶ l) :
    ((transposeCof N n k F).obj i).obj.obj.map f = (F.map f).hom.hom.app i := rfl

end CategoryTheory.Waldhausen.Fibration.MixedNerves
