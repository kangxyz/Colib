/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.SimplexAttachment.RelativeCharts
public import Colib.Topology.LocalCoefficients.RelativeSubspaceInclusion
public import Colib.Topology.LocalCoefficients.RelativeOpenRestriction

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SimplexAttachmentExcision.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original pair maps.

# Twisted relative excision for original parameterized simplex attachments

For every actual pushout attaching `X × Δⁿ` along `X × ∂Δⁿ`, the original cell
map induces a quasi-isomorphism from the actual geometric boundary pair to the
actual old-image pair. The local system on the target is arbitrary. No hypothesis
on the parameter space, the attaching map, or the dimension is needed, including
in dimension zero. The proof uses the existing radial collar deformation and
actual open excision, with the original relative coefficient squares retained.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits _root_.stdSimplex TopCat
universe u
namespace FundamentalGroupoid.LocalCoefficients

variable (X : TopCat.{u}) (n : ℕ) {B D : TopCat.{u}}
  {f : TopCat.of (X × _root_.stdSimplex.boundary n) ⟶ B}
  {g : TopCat.of (X × _root_.stdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : B ⟶ D}
  (sq : IsPushout (TopCat.parameterizedSimplexBoundaryInclusion X n) f g j)

/-- The actual open-collar pair map is a quasi-isomorphism for every target local system. -/
theorem simplexAttachmentCell_collar_relative_quasiIso (L : System.{u, u} D) :
    QuasiIso (relativePushforwardChainMap g.hom
      (SimplexAttachment.sourceCollar X n) (simplexAttachmentCollar X n sq)
      (SimplexAttachment.cell_mapsTo_collar X n sq) L) := by
  apply relativePushforwardChainMap_quasiIso_of_openRestriction g.hom
    (SimplexAttachment.sourceInterior X n) (SimplexAttachment.sourceCollar X n)
    (SimplexAttachment.targetInterior (j := j)) (simplexAttachmentCollar X n sq)
    (SimplexAttachment.cell_mapsTo_interior X n sq)
    (SimplexAttachment.cell_mapsTo_collar X n sq) L
    (SimplexAttachment.sourceInterior_isOpen X n)
    (SimplexAttachment.sourceCollar_isOpen X n)
    (SimplexAttachment.sourceInterior_union_collar X n)
    (SimplexAttachment.targetInterior_isOpen X n sq)
    (isOpen_simplexAttachmentCollar X n sq)
    (SimplexAttachment.targetInterior_union_collar X n sq)
  apply relativePushforwardChainMap_quasiIso_of_homotopyEquiv
    (subspaceMap g.hom (SimplexAttachment.sourceInterior X n)
      (SimplexAttachment.targetInterior (j := j))
      (SimplexAttachment.cell_mapsTo_interior X n sq))
    (intersectionInSubspace (SimplexAttachment.sourceInterior X n)
      (SimplexAttachment.sourceCollar X n))
    (intersectionInSubspace (SimplexAttachment.targetInterior (j := j))
      (simplexAttachmentCollar X n sq))
    (fun _ hx ↦ SimplexAttachment.cell_mapsTo_collar X n sq hx)
    (pullback (subspaceInclusion (SimplexAttachment.targetInterior (j := j))) L)
    (SimplexAttachment.cellInteriorHomeomorph X n sq).toHomotopyEquiv
    (by apply ContinuousMap.ext; intro z; apply Subtype.ext; rfl)
    (SimplexAttachment.cellInteriorCollarHomeomorph X n sq).toHomotopyEquiv
    (by apply ContinuousMap.ext; intro z; apply Subtype.ext; apply Subtype.ext; rfl)

/-- The exact square between the original closed-pair map and its collar enlargement. -/
theorem simplexAttachmentCell_relative_collar_square (L : System.{u, u} D) :
    relativeSubspaceInclusion (SimplexAttachment.sourceBoundary X n)
        (SimplexAttachment.sourceCollar X n)
        (SimplexAttachment.sourceBoundary_subset_collar X n) (pullback g.hom L) ≫
      relativePushforwardChainMap g.hom (SimplexAttachment.sourceCollar X n)
        (simplexAttachmentCollar X n sq) (SimplexAttachment.cell_mapsTo_collar X n sq) L =
    relativePushforwardChainMap g.hom (SimplexAttachment.sourceBoundary X n)
        (SimplexAttachment.baseImage (j := j))
        (SimplexAttachment.cell_mapsTo_boundary X n sq) L ≫
      relativeSubspaceInclusion (SimplexAttachment.baseImage (j := j))
        (simplexAttachmentCollar X n sq) (SimplexAttachment.baseImage_subset_collar X n sq) L :=
  relativeSubspaceInclusion_naturality g.hom _ _ _ _ _ _ _ _ L

/-- The original characteristic map of an actual parameterized simplex attachment
is a twisted relative quasi-isomorphism in every dimension, including zero. -/
theorem simplexAttachmentCell_relative_quasiIso (L : System.{u, u} D) :
    QuasiIso (relativePushforwardChainMap g.hom (SimplexAttachment.sourceBoundary X n)
      (SimplexAttachment.baseImage (j := j))
      (SimplexAttachment.cell_mapsTo_boundary X n sq) L) := by
  exact relativePushforwardChainMap_quasiIso_of_subspaceEnlargement g.hom
    (SimplexAttachment.sourceBoundary X n) (SimplexAttachment.sourceCollar X n)
    (SimplexAttachment.baseImage (j := j)) (simplexAttachmentCollar X n sq)
    (SimplexAttachment.sourceBoundary_subset_collar X n)
    (SimplexAttachment.baseImage_subset_collar X n sq)
    (SimplexAttachment.cell_mapsTo_boundary X n sq)
    (SimplexAttachment.cell_mapsTo_collar X n sq) L
    (SimplexAttachment.sourceBoundaryCollarEquiv X n)
    (by apply ContinuousMap.ext; intro z; apply Subtype.ext; rfl)
    (SimplexAttachment.baseImageCollarEquiv X n sq)
    (by
      apply ContinuousMap.ext
      intro z
      apply Subtype.ext
      exact SimplexAttachment.baseImageCollarEquiv_apply X n sq z)
    (simplexAttachmentCell_collar_relative_quasiIso X n sq L)

end FundamentalGroupoid.LocalCoefficients
