/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.ReplacementStageOne
public import Colib.CategoryTheory.TheoremA.ReplacementInvariance

/-!
# The actual point-augmentation tower

The point diagram identifies the first base stage with the discrete object
space and the exhaustive base colimit with its actual classifying space.
These coordinates retain the canonical point-augmentation map of towers.

Implementation provenance: extracted from
`Quillen/CategoryTheory/TheoremB/VertexWeakAssembly.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No weak-comparison result or
finite-stage cartesianness is assumed by these constructions.
-/
@[expose] public noncomputable section

open Topology CategoryTheory Limits Opposite
open CategoryTheory.TheoremA
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremB
variable {D : Type u} [SmallCategory D]

/-- The point-valued diagram whose replacement is the actual base nerve. -/
abbrev pointDiagram : D ⥤ SSet.{u} := (Functor.const D).obj (Δ[0] : SSet.{u})

/-- The point-diagram first stage is exactly the discrete space of objects. -/
def pointStageOneHomeomorph :
    (realizedReplacementSkeleton (pointDiagram (D := D))).obj 1 ≃ₜ TopCat.discrete.obj D :=
  (realizedReplacementStageOneHomeomorph (pointDiagram (D := D))).symm.trans
    (TopCat.sigmaPointHomeomorph D)

instance pointStageOne_discreteTopology :
    DiscreteTopology ((realizedReplacementSkeleton (pointDiagram (D := D))).obj 1) :=
  pointStageOneHomeomorph.symm.discreteTopology

/-- The actual point of stage one corresponding to an object. -/
def pointStageOneVertex (d : D) : (realizedReplacementSkeleton (pointDiagram (D := D))).obj 1 :=
  pointStageOneHomeomorph.symm d

/-- The exhaustive base cocone has the actual nerve realization as its vertex. -/
def replacementBaseSkeletonCocone : Cocone (realizedReplacementSkeleton (pointDiagram (D := D)))
  where
  pt := ClassifyingSpace D
  ι := {
    app n := (realizedReplacementSkeletonCocone pointDiagram).ι.app n ≫
      (replacementPointRealizationIso (D := D)).hom
    naturality n m f := by
      rw [← Category.assoc, (realizedReplacementSkeletonCocone pointDiagram).w f]
      simp }

/-- This is the actual colimit after the already proved point-replacement
homeomorphism, rather than a replacement base assumed equivalent to it. -/
def replacementBaseSkeletonIsColimit : IsColimit (replacementBaseSkeletonCocone (D := D)) :=
  IsColimit.ofIsoColimit (realizedReplacementSkeletonIsColimit pointDiagram)
    (Cocone.ext replacementPointRealizationIso)

/-- The point-replacement homeomorphism is exactly its canonical base projection. -/
theorem replacementPointRealizationIso_hom :
    (replacementPointRealizationIso (D := D)).hom =
      SSet.toTop.map (replacementBaseMap pointDiagram) := rfl

/-- The exhaustive base cocone sends each stage-one object to its actual
classifying-space vertex. -/
theorem replacementBaseSkeletonCocone_vertex (d : D) :
    (replacementBaseSkeletonCocone (D := D)).ι.app 1 (pointStageOneVertex d) =
      classifyingSpacePoint d := by
  change (replacementPointRealizationIso (D := D)).hom
    ((realizedReplacementSkeletonCocone pointDiagram).ι.app 1
      (realizedReplacementStageOneHomeomorph pointDiagram ⟨d, (default : |(Δ[0] : SSet.{u})|)⟩)) = _
  exact (congrArg (replacementPointRealizationIso (D := D)).hom
    (realizedReplacementStageOneHomeomorph_colimit pointDiagram d
      (default : |(Δ[0] : SSet.{u})|))).trans
      (replacementVertex_base pointDiagram d (default : |(Δ[0] : SSet.{u})|))

variable (H : D ⥤ SSet.{u})

/-- The map of base-skeleton towers induced by the point augmentation. -/
abbrev replacementProjectionTowerMap := realizedReplacementSkeletonMap (replacementPointAugmentation
  H)


end CategoryTheory.TheoremB
