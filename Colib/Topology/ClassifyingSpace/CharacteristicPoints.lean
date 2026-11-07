/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.Skeleton
public import Colib.Topology.ClassifyingSpace.Path
public import Colib.Topology.ClassifyingSpace.ZeroSkeleton

/-!
# Original simplex paths in actual skeletal attachments

The characteristic maps of the actual realized skeletal pushouts, followed by
the original inclusion into realization, are the original simplex maps. In a
nerve, their one-cells give exactly the original classifying-space paths.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/ClassifyingSpace/CharacteristicPoints.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, endpoint equalities,
path classes and independent universe parameters are retained. Native namespace
ownership and the pinned native standard simplex replace source ownership.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial Topology
universe u v
namespace SSet

/-- The actual characteristic map followed by inclusion is the original simplex map. -/
theorem realizedSkeletalCharacteristic_inclusion {A X : SSet.{u}} (i : A ⟶ X)
    (n : ℕ) (a : SSet.relativeCellComplexOfMono.Cell i n) (x : |(Δ[n] : SSet.{u})|) :
    SSet.toTop.map (SSet.skeletonOfMono i (n + 1)).ι
      (realizedSkeletalCharacteristic i n (a, SimplexCategory.toTopHomeo ⦋n⦌ x)) =
        SSet.toTop.map (SSet.yonedaEquiv.symm a.simplex) x := by
  have he := ConcreteCategory.congr_hom (realizedSkeletalCellsIso_ι i n a) x
  change (realizedSkeletalCellsIso i n).hom (SSet.toTop.map a.ιSigmaStdSimplex x) =
    (a, SimplexCategory.toTopHomeo ⦋n⦌ x) at he
  have hi : (realizedSkeletalCellsIso i n).inv (a, SimplexCategory.toTopHomeo ⦋n⦌ x) =
      SSet.toTop.map a.ιSigmaStdSimplex x := by
    rw [← he]
    exact (TopCat.homeoOfIso (realizedSkeletalCellsIso i n)).symm_apply_apply _
  change SSet.toTop.map (SSet.skeletonOfMono i (n + 1)).ι
    (SSet.toTop.map (SSet.relativeCellComplexOfMono.b i n)
      ((realizedSkeletalCellsIso i n).inv (a, SimplexCategory.toTopHomeo ⦋n⦌ x))) = _
  rw [hi]
  change (SSet.toTop.map a.ιSigmaStdSimplex ≫
    SSet.toTop.map (SSet.relativeCellComplexOfMono.b i n) ≫
    SSet.toTop.map (SSet.skeletonOfMono i (n + 1)).ι) x = _
  rw [← Functor.map_comp, ← Functor.map_comp, a.ι_b_ι]

/-- The same original-simplex formula in the geometric coordinates of the cell. -/
theorem realizedSkeletalCharacteristic_inclusion_geometric {A X : SSet.{u}} (i : A ⟶ X)
    (n : ℕ) (a : SSet.relativeCellComplexOfMono.Cell i n)
    (t : _root_.stdSimplex ℝ (Fin (n + 1))) :
    SSet.toTop.map (SSet.skeletonOfMono i (n + 1)).ι
      (realizedSkeletalCharacteristic i n (a, t)) =
        SSet.toTop.map (SSet.yonedaEquiv.symm a.simplex)
          ((SimplexCategory.toTopHomeo ⦋n⦌).symm t) := by
  simpa only [Homeomorph.apply_symm_apply] using
    realizedSkeletalCharacteristic_inclusion i n a
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm t)

end SSet

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The original object vertices are distinct points of the original classifying space. -/
theorem classifyingSpacePoint_injective :
    Function.Injective (classifyingSpacePoint (C := C)) := by
  intro c d h
  have hs : nerveZeroSkeletonPoint c = nerveZeroSkeletonPoint d :=
    (realization_skeleton_isClosedEmbedding (nerve C) 1).injective
      ((nerveZeroSkeletonPoint_inclusion c).trans (h.trans
        (nerveZeroSkeletonPoint_inclusion d).symm))
  have he := congrArg (nerveZeroSkeletonHomeomorph (C := C)) hs
  simpa only [nerveZeroSkeletonHomeomorph_point] using he

/-- An actual one-cell of the nerve skeleton is precisely the original morphism path. -/
theorem realizedNerveOneCell_original_path
    (a : SSet.relativeCellComplexOfMono.Cell ((⊥ : (nerve C).Subcomplex).ι) 1)
    (t : unitInterval) :
    SSet.toTop.map (SSet.skeletonOfMono ((⊥ : (nerve C).Subcomplex).ι) 2).ι
      (realizedSkeletalCharacteristic ((⊥ : (nerve C).Subcomplex).ι) 1
        (a, SimplexCategory.toTopHomeo ⦋1⦌ (realizationInterval.{max u v} t))) =
          classifyingSpacePath (a.simplex.map' 0 1) t := by
  refine (realizedSkeletalCharacteristic_inclusion
    ((⊥ : (nerve C).Subcomplex).ι) 1 a (realizationInterval.{max u v} t)).trans ?_
  change SSet.toTop.map (SSet.yonedaEquiv.symm a.simplex) (realizationInterval.{max u v} t) =
    SSet.toTop.map (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (a.simplex.map' 0 1)))
      (realizationInterval.{max u v} t)
  have he : a.simplex = ComposableArrows.mk₁ (a.simplex.map' 0 1) :=
    ComposableArrows.ext₁ rfl rfl (by simp)
  exact congrArg (fun s : (nerve C) _⦋1⦌ ↦
    SSet.toTop.map (SSet.yonedaEquiv.symm s) (realizationInterval.{max u v} t)) he

/-- The source of the actual one-cell is its original source object. -/
theorem realizedNerveOneCell_original_source
    (a : SSet.relativeCellComplexOfMono.Cell ((⊥ : (nerve C).Subcomplex).ι) 1) :
    SSet.toTop.map (SSet.skeletonOfMono ((⊥ : (nerve C).Subcomplex).ι) 2).ι
      (realizedSkeletalCharacteristic ((⊥ : (nerve C).Subcomplex).ι) 1
        (a, SimplexCategory.toTopHomeo ⦋1⦌ (realizationInterval.{max u v} 0))) =
          classifyingSpacePoint (a.simplex.obj 0) := by
  exact (realizedNerveOneCell_original_path a 0).trans
    (classifyingSpacePath (a.simplex.map' 0 1)).source

/-- The target of the actual one-cell is its original target object. -/
theorem realizedNerveOneCell_original_target
    (a : SSet.relativeCellComplexOfMono.Cell ((⊥ : (nerve C).Subcomplex).ι) 1) :
    SSet.toTop.map (SSet.skeletonOfMono ((⊥ : (nerve C).Subcomplex).ι) 2).ι
      (realizedSkeletalCharacteristic ((⊥ : (nerve C).Subcomplex).ι) 1
        (a, SimplexCategory.toTopHomeo ⦋1⦌ (realizationInterval.{max u v} 1))) =
          classifyingSpacePoint (a.simplex.obj 1) := by
  exact (realizedNerveOneCell_original_path a 1).trans
    (classifyingSpacePath (a.simplex.map' 0 1)).target

end CategoryTheory
