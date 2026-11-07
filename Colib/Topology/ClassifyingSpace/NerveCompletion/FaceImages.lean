/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.FaceGeometry

/-!
# Face Images

The original native realization homeomorphism sends the geometric interval parameter
back to exactly the original realizationInterval, with its original ULift direction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Convexity.StdSimplex SSet TopCat
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary

/-- The original native realization homeomorphism sends the geometric interval parameter
back to exactly the original realizationInterval, with its original ULift direction. -/
theorem intervalPath_realization (t : unitInterval) :
    (SimplexCategory.toTopHomeo ⦋1⦌).symm (NerveGraphData.intervalPath t) =
      realizationInterval.{u} t := by
  apply (SimplexCategory.toTopHomeo ⦋1⦌).injective
  rw [Homeomorph.apply_symm_apply, NerveGraphData.realizationInterval_geometric]
  rfl

/-- Exact pointwise face formula for the original two-cell attachment after its
unchanged graph-stage inclusion. No nondegeneracy assumption on the face is made. -/
theorem nerveTwoCellBoundary_face_inclusion (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (k : Fin 3) (t : unitInterval) (x : Convexity.StdSimplex.boundary 2)
    (hx : x.val = Convexity.StdSimplex.map (SimplexCategory.δ k) (NerveGraphData.intervalPath t)) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a x) =
      SSet.toTop.map (SSet.yonedaEquiv.symm ((nerve C).δ k a.simplex))
        (realizationInterval.{max u v} t) := by
  rw [nerveTwoCellBoundary_inclusion, hx,
    SimplexCategory.toTopHomeo_symm_naturality_apply, intervalPath_realization]
  change (SSet.toTop.map (SSet.stdSimplex.δ k) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm a.simplex)) (realizationInterval t) = _
  rw [← SSet.toTop.map_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]

/-- The actual short 01 edge is the original d2 face, including degenerate faces. -/
theorem nerveTwoCellBoundary_01_inclusion (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (t : unitInterval) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a (boundaryEdge 0 1 t)) =
      SSet.toTop.map (SSet.yonedaEquiv.symm ((nerve C).δ 2 a.simplex))
        (realizationInterval.{max u v} t) :=
  nerveTwoCellBoundary_face_inclusion C a 2 t _ (boundaryEdge_01_face t)

/-- The actual short 12 edge is the original d0 face, including degenerate faces. -/
theorem nerveTwoCellBoundary_12_inclusion (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (t : unitInterval) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a (boundaryEdge 1 2 t)) =
      SSet.toTop.map (SSet.yonedaEquiv.symm ((nerve C).δ 0 a.simplex))
        (realizationInterval.{max u v} t) :=
  nerveTwoCellBoundary_face_inclusion C a 0 t _ (boundaryEdge_12_face t)

/-- The actual long 02 edge is the original d1 face, including degenerate faces. -/
theorem nerveTwoCellBoundary_02_inclusion (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (t : unitInterval) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a (boundaryEdge 0 2 t)) =
      SSet.toTop.map (SSet.yonedaEquiv.symm ((nerve C).δ 1 a.simplex))
        (realizationInterval.{max u v} t) :=
  nerveTwoCellBoundary_face_inclusion C a 1 t _ (boundaryEdge_02_face t)

end CategoryTheory.NerveCompletion
