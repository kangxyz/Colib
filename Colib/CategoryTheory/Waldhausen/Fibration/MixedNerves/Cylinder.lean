/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.ChainCategories
public import Colib.CategoryTheory.Waldhausen.Fibration.TrivialCofibrations.Category
public import Colib.CategoryTheory.ArrowDiagrams

/-! # The actual cylinder on original fine-weak chains

The middle diagram is obtained by applying the original cylinder to each
original component arrow. Its fine-weak object condition follows from actual
fine-square preservation. The endpoint and projection maps retain their
original components. No Waldhausen structure or comparison equivalence on
the fine-chain category is assumed.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/Cylinder.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)
  (D : TrivialCofibrations.CylinderData V.cof N.coarse.weq)

/-- The only extra object-closure condition: the actual middle preserves fine squares. -/
def CylinderPreservesFineSquares : Prop :=
  ∀ {f g : Arrow C} (α : f ⟶ g), V.weq α.left → V.weq α.right → V.weq (D.middle.map α)

/-- An arrow of fine chains is evaluated at its literal original component arrows. -/
def chainArrowDiagram (k : SimplexCategory) : Arrow (FineChain V k) ⥤ (Fin (k.len+1) ⥤ Arrow C) :=
  (fineChains V k).ι.mapArrow ⋙ ArrowDiagrams.toDiagram

/-- The original middle functor is applied pointwise, retaining all natural transformations. -/
def chainMiddle (hD : CylinderPreservesFineSquares N D) (k : SimplexCategory) :
    Arrow (FineChain V k) ⥤ FineChain V k where
  obj f := ⟨(chainArrowDiagram (V := V) k).obj f ⋙ D.middle,
    fun a ↦ hD (((chainArrowDiagram (V := V) k).obj f).map a)
      (f.left.property a) (f.right.property a)⟩
  map α := (fineChains V k).homMk
    (Functor.whiskerRight ((chainArrowDiagram (V := V) k).map α) D.middle)
  map_id f := by
    apply ObjectProperty.hom_ext
    ext i
    exact CategoryTheory.Functor.map_id D.middle _
  map_comp α β := by
    apply ObjectProperty.hom_ext
    ext i
    change D.middle.map (((chainArrowDiagram (V := V) k).map (α ≫ β)).app i) = _
    rw [(chainArrowDiagram (V := V) k).map_comp]
    exact CategoryTheory.Functor.map_comp D.middle _ _

/-- The actual first endpoint at every original fine-chain vertex. -/
def chainInclusionMap (hD : CylinderPreservesFineSquares N D) (k : SimplexCategory) :
    Arrow.leftFunc ⟶ chainMiddle N D hD k where
  app f := (fineChains V k).homMk
    (Functor.whiskerLeft ((chainArrowDiagram (V := V) k).obj f) D.inclusion)
  naturality f g α := by
    apply ObjectProperty.hom_ext
    ext i
    exact D.inclusion.naturality (((chainArrowDiagram (V := V) k).map α).app i)

/-- The actual coarse projection at every original fine-chain vertex. -/
def chainProjectionMap (hD : CylinderPreservesFineSquares N D) (k : SimplexCategory) :
    chainMiddle N D hD k ⟶ Arrow.rightFunc where
  app f := (fineChains V k).homMk
    (Functor.whiskerLeft ((chainArrowDiagram (V := V) k).obj f) D.projection)
  naturality f g α := by
    apply ObjectProperty.hom_ext
    ext i
    exact D.projection.naturality (((chainArrowDiagram (V := V) k).map α).app i)

/-- The actual second endpoint at every original fine-chain vertex. -/
def chainTargetMap (hD : CylinderPreservesFineSquares N D) (k : SimplexCategory) :
    Arrow.rightFunc ⟶ chainMiddle N D hD k where
  app f := (fineChains V k).homMk
    (Functor.whiskerLeft ((chainArrowDiagram (V := V) k).obj f) D.target)
  naturality f g α := by
    apply ObjectProperty.hom_ext
    ext i
    exact D.target.naturality (((chainArrowDiagram (V := V) k).map α).app i)

/-- Actual pointwise structural cylinder data on the original fine-chain category. -/
def chainCylinder (hD : CylinderPreservesFineSquares N D) (k : SimplexCategory) :
    TrivialCofibrations.CylinderData (pointwiseCof V k) (pointwiseCoarse N k) where
  middle := chainMiddle N D hD k
  inclusion := chainInclusionMap N D hD k
  projection := chainProjectionMap N D hD k
  target := chainTargetMap N D hD k
  factorization f := by
    apply ObjectProperty.hom_ext
    ext i
    exact D.factorization (Arrow.mk (f.hom.hom.app i))
  target_projection f := by
    apply ObjectProperty.hom_ext
    ext i
    exact D.target_projection (Arrow.mk (f.hom.hom.app i))
  inclusion_cof f i := D.inclusion_cof (Arrow.mk (f.hom.hom.app i))
  target_cof f i := D.target_cof (Arrow.mk (f.hom.hom.app i))
  projection_weak f i := D.projection_weak (Arrow.mk (f.hom.hom.app i))
  middle_cof α hl hr i :=
    D.middle_cof (((chainArrowDiagram (V := V) k).map α).app i) (hl i) (hr i)

@[simp] theorem chainCylinder_middle_obj (hD : CylinderPreservesFineSquares N D)
    (k : SimplexCategory) (f : Arrow (FineChain V k)) (i : Fin (k.len + 1)) :
    (((chainCylinder N D hD k).middle.obj f).obj.obj i) =
      D.middle.obj (Arrow.mk (f.hom.hom.app i)) := rfl

@[simp] theorem chainCylinder_inclusion_app (hD : CylinderPreservesFineSquares N D)
    (k : SimplexCategory) (f : Arrow (FineChain V k)) (i : Fin (k.len + 1)) :
    ((chainCylinder N D hD k).inclusion.app f).hom.app i =
      D.inclusion.app (Arrow.mk (f.hom.hom.app i)) := rfl

@[simp] theorem chainCylinder_target_app (hD : CylinderPreservesFineSquares N D)
    (k : SimplexCategory) (f : Arrow (FineChain V k)) (i : Fin (k.len + 1)) :
    ((chainCylinder N D hD k).target.app f).hom.app i =
      D.target.app (Arrow.mk (f.hom.hom.app i)) := rfl

@[simp] theorem chainCylinder_projection_app (hD : CylinderPreservesFineSquares N D)
    (k : SimplexCategory) (f : Arrow (FineChain V k)) (i : Fin (k.len + 1)) :
    ((chainCylinder N D hD k).projection.app f).hom.app i =
      D.projection.app (Arrow.mk (f.hom.hom.app i)) := rfl

/-- The fixed-fine-degree comparison is literally the generic original-arrow inclusion. -/
theorem horizontalInclusion_eq (k : SimplexCategory) : horizontalInclusion N k =
    TrivialCofibrations.inclusion (pointwiseCof V k) (pointwiseCoarse N k) := rfl

/-- The original middle diagrams commute strictly with every fine-index restriction. -/
theorem chainMiddle_reindex (hD : CylinderPreservesFineSquares N D)
    {k l : SimplexCategory} (α : k ⟶ l) :
    (fineReindex V α).mapArrow ⋙ chainMiddle N D hD k =
      chainMiddle N D hD l ⋙ fineReindex V α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem chainProjection_reindex (hD : CylinderPreservesFineSquares N D)
    {k l : SimplexCategory} (α : k ⟶ l) (f : Arrow (FineChain V l)) :
    (fineReindex V α).map ((chainCylinder N D hD l).projection.app f) =
      (chainCylinder N D hD k).projection.app ((fineReindex V α).mapArrow.obj f) := rfl

end CategoryTheory.Waldhausen.Fibration.MixedNerves
