/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremA.GeometricAttachments
public import Colib.Topology.LocalCoefficients.SimplexAttachmentExcision
public import Colib.Topology.LocalCoefficients.EmbeddingRelativeChains

/-!
Adapted from `Quillen/CategoryTheory/TheoremA/AttachmentHomology.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Actual twisted relative chains of replacement successor attachments

The original geometric characteristic map compares the actual geometric cell
boundary pair to the cokernel of the original realized skeleton inclusion.
The comparison is a quasi-isomorphism for every target local system, and its
quotient equation retains the original absolute characteristic map.
-/

@[expose] public section
noncomputable section
open SSet TopCat Convexity.StdSimplex
open CategoryTheory Limits FundamentalGroupoid.LocalCoefficients
open scoped Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremA
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The original successor inclusion in the actual realized base-skeleton filtration. -/
def replacementSkeletonStep (n : ℕ) :
    C((realizedReplacementSkeleton H).obj n, (realizedReplacementSkeleton H).obj (n + 1)) :=
  ((realizedReplacementSkeleton H).map (homOfLE (Nat.le_succ n))).hom

/-- The actual successor inclusion has the closed subspace topology of its image. -/
theorem replacementSkeletonStep_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (replacementSkeletonStep H n) :=
  simplexAttachment_old_isClosedEmbedding (replacementCellParameters H n) n
    (replacementGeometric_isPushout H n)

/-- The original characteristic pair map, with the target expressed as the original
skeleton-inclusion cokernel rather than a replacement complex. -/
def replacementCellRelativeChainMap (n : ℕ)
    (L : System.{u, u} ((realizedReplacementSkeleton H).obj (n + 1))) :
    relativeSingularChainComplex
        (SimplexAttachment.sourceBoundary (replacementCellParameters H n) n)
        (pullback (replacementGeometricCharacteristic H n).hom L) ⟶
      cokernel (pushforwardChainMap (replacementSkeletonStep H n) L) :=
  relativePushforwardChainMap (replacementGeometricCharacteristic H n).hom
      (SimplexAttachment.sourceBoundary (replacementCellParameters H n) n)
      (Set.range (replacementSkeletonStep H n))
      (SimplexAttachment.cell_mapsTo_boundary (replacementCellParameters H n) n
        (replacementGeometric_isPushout H n)) L ≫
    (embeddingCokernelIsoRelative (replacementSkeletonStep H n)
      (replacementSkeletonStep_isClosedEmbedding H n).isEmbedding L).inv

/-- The relative comparison leaves the original characteristic chain map in the quotient square. -/
@[reassoc]
theorem replacementCellRelativeChainMap_quotient (n : ℕ)
    (L : System.{u, u} ((realizedReplacementSkeleton H).obj (n + 1))) :
    cokernel.π (pushforwardChainMap
        (subspaceInclusion (SimplexAttachment.sourceBoundary (replacementCellParameters H n) n))
        (pullback (replacementGeometricCharacteristic H n).hom L)) ≫
      replacementCellRelativeChainMap H n L =
    pushforwardChainMap (replacementGeometricCharacteristic H n).hom L ≫
      cokernel.π (pushforwardChainMap (replacementSkeletonStep H n) L) := by
  dsimp only [replacementCellRelativeChainMap]
  rw [← Category.assoc, relativePushforwardChainMap_quotient, Category.assoc,
    ← embeddingCokernelIsoRelative_quotient (replacementSkeletonStep H n)
      (replacementSkeletonStep_isClosedEmbedding H n).isEmbedding L,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Genuine all-local-system attachment excision for the original replacement skeleton cokernel. -/
theorem replacementCellRelativeChainMap_quasiIso (n : ℕ)
    (L : System.{u, u} ((realizedReplacementSkeleton H).obj (n + 1))) :
    QuasiIso (replacementCellRelativeChainMap H n L) := by
  have h : QuasiIso (relativePushforwardChainMap (replacementGeometricCharacteristic H n).hom
      (SimplexAttachment.sourceBoundary (replacementCellParameters H n) n)
      (Set.range (replacementSkeletonStep H n))
      (SimplexAttachment.cell_mapsTo_boundary (replacementCellParameters H n) n
        (replacementGeometric_isPushout H n)) L) :=
    simplexAttachmentCell_relative_quasiIso (replacementCellParameters H n) n
      (replacementGeometric_isPushout H n) L
  dsimp only [replacementCellRelativeChainMap]
  infer_instance

end CategoryTheory.TheoremA
