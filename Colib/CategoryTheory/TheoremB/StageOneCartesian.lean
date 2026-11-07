/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.ReplacementStageOne
public import Colib.Topology.HomotopyPullback.CoproductPaths

/-! # The canonical vertex square in the actual first replacement stage

The actual first-stage coproduct coordinates identify its vertex square with a
coproduct component square. This proves cartesianness of the specified square,
without any condition on the coefficient map. It does not assert cartesianness
of inclusions between different skeletal stages.

The construction uses the exact maps in the pinned source
`Quillen/CategoryTheory/TheoremB/ReplacementStageOne.lean` and the component
comparison from `Quillen/Topology/Realization/Cartesian/CoproductPaths.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/
@[expose] public noncomputable section

universe u
open SSet CategoryTheory Topology.HomotopyPullback
open scoped Simplicial Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA
variable {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}} (η : H ⟶ K)

/-- Coefficient transformations preserve the actual stage-one vertex inclusions. -/
theorem realizedReplacementStageOneVertex_square (d : D) :
    SSet.toTop.map (simplicialSigmaι (fun d ↦ H.obj d) d ≫ vertexCoproductToStageOne H) ≫
      (realizedReplacementSkeletonMap η).app 1 =
    SSet.toTop.map (η.app d) ≫
      SSet.toTop.map (simplicialSigmaι (fun d ↦ K.obj d) d ≫ vertexCoproductToStageOne K) := by
  change SSet.toTop.map _ ≫ SSet.toTop.map _ = SSet.toTop.map _ ≫ SSet.toTop.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The canonical vertex square of the actual first-stage coefficient map is homotopy
cartesian. Its comparison includes precisely the original vertex and constant target path. -/
theorem realizedReplacementStageOneVertex_cartesian (d : D) :
    Cartesian (SSet.toTop.map (η.app d)).hom ((realizedReplacementSkeletonMap η).app 1).hom
      (SSet.toTop.map (simplicialSigmaι (fun d ↦ H.obj d) d ≫
        vertexCoproductToStageOne H)).hom
      (SSet.toTop.map (simplicialSigmaι (fun d ↦ K.obj d) d ≫
        vertexCoproductToStageOne K)).hom
      (congrArg TopCat.Hom.hom (realizedReplacementStageOneVertex_square η d)) := by
  let q : ∀ d : D, C(|H.obj d|, |K.obj d|) :=
    fun d ↦ (SSet.toTop.map (η.app d)).hom
  apply cartesianOfCoordinates _ _ _ _ _
    (q d) (sigmaMap q)
    (ContinuousMap.sigmaMk (X := fun i : D ↦ |H.obj i|) d)
    (ContinuousMap.sigmaMk (X := fun i : D ↦ |K.obj i|) d)
    (show (sigmaMap q).comp (ContinuousMap.sigmaMk (X := fun i : D ↦ |H.obj i|) d) =
      (ContinuousMap.sigmaMk (X := fun i : D ↦ |K.obj i|) d).comp (q d) from rfl)
    (Homeomorph.refl _) (realizedReplacementStageOneHomeomorph H).symm
    (Homeomorph.refl _) (realizedReplacementStageOneHomeomorph K).symm
  · rfl
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, x⟩, rfl⟩ := (realizedReplacementStageOneHomeomorph H).surjective z
    change sigmaMap q ((realizedReplacementStageOneHomeomorph H).symm
      (realizedReplacementStageOneHomeomorph H ⟨i, x⟩)) = _
    rw [Homeomorph.symm_apply_apply]
    apply (realizedReplacementStageOneHomeomorph K).injective
    change realizedReplacementStageOneHomeomorph K ⟨i, q i x⟩ =
      realizedReplacementStageOneHomeomorph K
        ((realizedReplacementStageOneHomeomorph K).symm _)
    rw [Homeomorph.apply_symm_apply]
    exact (realizedReplacementStageOneHomeomorph_naturality η i x).symm
  · apply ContinuousMap.ext
    intro x
    apply (realizedReplacementStageOneHomeomorph H).injective
    change realizedReplacementStageOneHomeomorph H ⟨d, x⟩ =
      realizedReplacementStageOneHomeomorph H
        ((realizedReplacementStageOneHomeomorph H).symm _)
    rw [Homeomorph.apply_symm_apply]
    exact realizedReplacementStageOneHomeomorph_apply H d x
  · apply ContinuousMap.ext
    intro x
    apply (realizedReplacementStageOneHomeomorph K).injective
    change realizedReplacementStageOneHomeomorph K ⟨d, x⟩ =
      realizedReplacementStageOneHomeomorph K
        ((realizedReplacementStageOneHomeomorph K).symm _)
    rw [Homeomorph.apply_symm_apply]
    exact realizedReplacementStageOneHomeomorph_apply K d x
  · exact cartesianComponentInclusion q d

end CategoryTheory.TheoremA
